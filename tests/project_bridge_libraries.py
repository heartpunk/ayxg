"""Project native library roots to the exact parsed bridge import closure.
Only disposable dependency build metadata is edited; declarations are untouched.
Lake's ordinary shared/static targets continue to own compilation/linking.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess


def project_libraries(work: Path, floatlib: Path, parser_source: Path) -> None:
    roots=[work,work/'leanpy',floatlib,*sorted((work/'.lake/packages').iterdir())]
    roots=[path for path in roots if path.is_dir()]
    parser=subprocess.Popen(['lake','env','lean','--run',str(parser_source)],cwd=work,
                            stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    pending=['Bridge'];seen={};standard=set();by_root={}
    try:
        while pending:
            module=pending.pop()
            if module in seen or module in standard:continue
            suffix=Path(*module.split('.')).with_suffix('.lean')
            matches=[(root,root/suffix) for root in roots if (root/suffix).is_file()]
            if not matches:
                if module.split('.')[0] in {'Init','Std','Lean','Lake'}:
                    standard.add(module);continue
                raise RuntimeError(f'unresolved bridge import {module}')
            if len(matches)!=1:raise RuntimeError(f'ambiguous bridge import {module}: {matches}')
            root,path=matches[0];data=path.read_bytes()
            parser.stdin.write(str(path)+'\n');parser.stdin.flush()
            response=parser.stdout.readline()
            if not response:raise RuntimeError('Lean import parser exited unexpectedly')
            imports=json.loads(response)
            if not isinstance(imports,list):raise RuntimeError(imports)
            seen[module]={'source':str(path),'sha256':hashlib.sha256(data).hexdigest(),'imports':imports}
            by_root.setdefault(root,[]).append(module);pending.extend(imports)
    finally:
        parser.stdin.close();status=parser.wait()
        if status:raise RuntimeError(f'Lean import parser exited {status}')
    projected={}
    for root,library in [(floatlib,'FloatLib'),(work/'.lake/packages/mathlib','Mathlib')]:
        modules=sorted(by_root.get(root,[]))
        if not modules:raise RuntimeError(f'empty {library} closure')
        config=root/'lakefile.lean';original=config.read_text()
        needle=f'lean_lib {library} where'
        if original.count(needle)!=1:raise RuntimeError(f'unexpected {library} library configuration')
        names=', '.join('`'+name for name in modules)
        projected_config=original.replace(needle,needle+'\n  roots := #['+names+']',1)
        if library=='FloatLib':
            projected_config=projected_config.replace('  roots := #[`FloatLib]\n','')
        config.write_text(projected_config)
        projected[library]={'modules':modules,'original_lakefile_sha256':hashlib.sha256(original.encode()).hexdigest(),'projected_lakefile_sha256':hashlib.sha256(config.read_bytes()).hexdigest()}
    (work/'native-library-projection.json').write_text(json.dumps({'root':'Bridge','modules':seen,'toolchain_modules':sorted(standard),'projections':projected},indent=2)+'\n')
    print('Projected native library roots:',{key:len(value['modules']) for key,value in projected.items()},flush=True)
