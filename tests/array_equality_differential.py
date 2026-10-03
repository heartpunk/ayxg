"""Compare array equality via the existing Lean JSON bridge, Python, and Z3.

The disposable CLI transport removes only lean.py import/export annotations;
it preserves the bridge parser and calls the actual AYXG denotation.
Run: nix develop --command env PYTHONPATH=python python tests/array_equality_differential.py
"""
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile
import z3
from ayxg.expr import Declaration, TermSort, TypedExpr
from ayxg.qfabv import ArraySort, QFAbvArrayValue
from ayxg.eval import _eval_nodes
from ayxg.z3 import expr_to_z3, expr_from_z3

root = Path(__file__).resolve().parents[1]
rng = random.Random(20261002)
with tempfile.TemporaryDirectory(prefix="ayxg-array-equality-") as td:
    work = Path(td).resolve()
    (work / "Bridge").mkdir()
    source = root / "tests/lean_bridge"
    (work / "Bridge/Examples.lean").write_text((source / "Bridge/Examples.lean").read_text())
    bridge = (source / "Bridge.lean").read_text().replace("import LeanPy\n", "import Lean\n").replace("open LeanPy Lean", "open Lean")
    bridge = bridge.replace('@[python "py_eval_json"]\n', "").replace('#export_python_registry "Bridge"\n', "")
    (work / "ArrayBridge.lean").write_text(bridge)
    (work / "Runner.lean").write_text('import ArrayBridge\ndef main (args : List String) : IO Unit := do\n  let data ← IO.FS.readFile args.head!\n  for line in data.splitOn "\\n" do\n    if !line.isEmpty then IO.println (evalJson line)\n')
    env = dict(os.environ)
    paths = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], text=True).strip().split(":")
    env["LEAN_PATH"] = ":".join([str(work), *(str((root / p).resolve()) for p in paths)])
    for module in ["Bridge/Examples", "ArrayBridge"]:
        subprocess.run(["lean", "-o", str(work / (module + ".olean")), str(work / (module + ".lean"))], env=env, cwd=work, check=True)
    requests, expected, solver_failures = [], [], []
    for i in range(300):
        iw, vw = rng.randint(1, 4), rng.choice([1, 3, 8, 32])
        sort = ArraySort(iw, vw)
        values = [rng.randrange(1 << vw) for _ in range(1 << iw)]
        other = values.copy()
        if i % 3 == 1:
            j = rng.randrange(len(other)); other[j] ^= 1
        defaults = [rng.randrange(1 << vw), rng.randrange(1 << vw)]
        arrays = [QFAbvArrayValue(sort, d, tuple((j, v) for j, v in enumerate(vs) if v != d))
                  for d, vs in zip(defaults, [values, other])]
        declarations = [Declaration(n, sort.encode()) for n in ["a", "b"]]
        expr = TypedExpr.equal(*(TypedExpr.var(d.name, d.sort) for d in declarations))
        if i % 3 == 2:
            expr = TypedExpr.negate(expr)
        py = _eval_nodes((expr,), dict(zip(["a", "b"], arrays)))[0]
        variables = {}
        for name, arr in zip(["a", "b"], arrays):
            term = z3.K(z3.BitVecSort(iw), z3.BitVecVal(arr.default, vw))
            for key, value in arr.entries:
                term = z3.Store(term, z3.BitVecVal(key, iw), z3.BitVecVal(value, vw))
            variables[name] = term
        smt = expr_to_z3(expr, variables, z3.main_ctx())
        solver = z3.Solver(); solver.add(smt != z3.BoolVal(py))
        result = solver.check()
        if result != z3.unsat:
            solver_failures.append({"case": i, "sort": [iw, vw], "python": py,
                "result": str(result), "reason": solver.reason_unknown(), "expression": smt.sexpr()})
        # Reverse conversion admits both equality and disequality of arrays.
        expr_from_z3(smt)
        requests.append({"declarations": [d.to_data() for d in declarations],
            "values": [{"default": a.default, "entries": list(a.entries)} for a in arrays],
            "expression": expr.to_data()})
        expected.append(py)
    request_file = work / "requests.jsonl"
    request_file.write_text("\n".join(json.dumps(r) for r in requests) + "\n")
    output = subprocess.check_output(["lean", "--run", str(work / "Runner.lean"), str(request_file)], env=env, cwd=work, text=True)
    actual = [json.loads(line)["value"] for line in output.splitlines()]
    assert actual == expected, (actual, expected)
    print(f"300 array equality/disequality cases: Lean = Python; Z3 discrepancies: {len(solver_failures)}")
    if solver_failures:
        report = root / "tests/evidence/array-equality/z3-discrepancies.json"
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text(json.dumps({"version": z3.get_version_string(), "failures": solver_failures}, indent=2) + "\n")
    assert not solver_failures, "Z3 discrepancies retained; validation FAILED"
