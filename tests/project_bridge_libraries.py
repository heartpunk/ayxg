"""Project native library roots to the exact parsed bridge import closure.
Only disposable dependency build metadata is edited; declarations are untouched.
Lake's ordinary shared/static targets continue to own compilation/linking.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import re
import tomllib


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
            try: imports=json.loads(response)
            except json.JSONDecodeError as error:
                raise RuntimeError(f'Lean import parser non-JSON diagnostic: {response.rstrip()}') from error
            if not isinstance(imports,list):raise RuntimeError(imports)
            seen[module]={'source':str(path),'sha256':hashlib.sha256(data).hexdigest(),'imports':imports}
            by_root.setdefault(root,[]).append(module);pending.extend(imports)
    finally:
        parser.stdin.close();status=parser.wait()
        if status and sys.exc_info()[0] is None:raise RuntimeError(f'Lean import parser exited {status}')
    projected={}
    for root,library in [(floatlib,'FloatLib'),(work/'.lake/packages/mathlib','Mathlib'),
                         (work/'.lake/packages/importGraph','ImportGraph'),
                         *[(work/'.lake/packages'/package,library) for package,library in
                           [('batteries','Batteries'),('aesop','Aesop'),('Qq','Qq'),
                            ('proofwidgets','ProofWidgets'),('LeanSearchClient','LeanSearchClient'),
                            ('plausible','Plausible'),('Cli','Cli')]]]:
        modules=sorted(by_root.get(root,[]))
        if not modules:
            if library in {'FloatLib','Mathlib'}:raise RuntimeError(f'empty {library} closure')
            continue
        config=root/('lakefile.toml' if (root/'lakefile.toml').exists() else 'lakefile.lean')
        original=config.read_text()
        if config.suffix=='.toml':
            needle='[[lean_lib]]\nname = '+json.dumps(library)
            if original.count(needle)!=1:raise RuntimeError(f'unexpected {library} library configuration')
            roots_line='roots = '+json.dumps(modules)
        else:
            needle=f'lean_lib {library} where'
            if original.count(needle)!=1:raise RuntimeError(f'unexpected {library} library configuration')
            names=', '.join('`'+name for name in modules)
            roots_line='  roots := #['+names+']'
        addition=needle+'\n'+roots_line
        projected_config=original if addition in original else original.replace(needle,addition,1)
        if library=='FloatLib':
            projected_config=projected_config.replace('  roots := #[`FloatLib]\n','')
        config.write_text(projected_config)
        projected[library]={'modules':modules,'original_lakefile_sha256':hashlib.sha256(original.encode()).hexdigest(),'projected_lakefile_sha256':hashlib.sha256(config.read_bytes()).hexdigest()}
    # The existing FFI harness embeds AYXG/LeanPy static archives. Embed their
    # exact new dependency archives too: compiler plugin loading alone does not
    # make those symbols available to Python's later dlopen of Bridge.
    package_names={'FloatLib':'floatlib','Mathlib':'mathlib','ImportGraph':'importGraph',
                   'Batteries':'batteries','Aesop':'aesop','Qq':'Qq',
                   'ProofWidgets':'proofwidgets','LeanSearchClient':'LeanSearchClient',
                   'Plausible':'plausible','Cli':'Cli'}
    owners={module:library for library,info in projected.items() for module in info['modules']}
    dependencies={library:set() for library in projected}
    for module,library in owners.items():
        dependencies[library].update(owners[name] for name in seen[module]['imports']
                                    if name in owners and owners[name]!=library)
    ordered=[];visited=set();active=set()
    def visit(library):
        if library in visited:return
        if library in active:raise RuntimeError(f'cyclic native library dependency at {library}')
        active.add(library)
        for dependency in sorted(dependencies[library]):visit(dependency)
        active.remove(library);visited.add(library);ordered.append(library)
    for library in sorted(projected):visit(library)
    targets=[package_names[library]+'/'+library+':static' for library in reversed(ordered)]
    bridge_config=work/'lakefile.toml';bridge_original=bridge_config.read_text()
    bridge_library=next(lib for lib in tomllib.loads(bridge_original)['lean_lib'] if lib['name']=='Bridge')
    baseline=['ayxgDerisk/Ayxg:static','LeanPy/LeanPy:static','LeanPy/leanPyNative:static']
    if bridge_library['moreLinkObjs'][:3]!=baseline:raise RuntimeError('unexpected FFI native link baseline')
    link_line='moreLinkObjs = '+json.dumps(baseline+targets)
    bridge_projected,count=re.subn(r'(?m)^moreLinkObjs = \[.*\]$',link_line,bridge_original)
    if count!=1:raise RuntimeError('unexpected FFI native link configuration')
    bridge_config.write_text(bridge_projected)
    native_link={'targets':baseline+targets,
                 'original_lakefile_sha256':hashlib.sha256(bridge_original.encode()).hexdigest(),
                 'projected_lakefile_sha256':hashlib.sha256(bridge_projected.encode()).hexdigest()}
    (work/'native-library-projection.json').write_text(json.dumps({'root':'Bridge','modules':seen,'toolchain_modules':sorted(standard),'projections':projected,'native_link':native_link},indent=2)+'\n')
    print('Projected native library roots:',{key:len(value['modules']) for key,value in projected.items()},flush=True)
