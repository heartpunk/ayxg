# Reproduce the actual FP correspondence campaign

Use a frozen AYXG snapshot at24f6686b (or its evidence-only descendants), a Linux
host admitted under the standing fleet policy, and a detached resource-limited
service. First-time Mathlib cache decompression needs more memory than the
subsequent campaign; do not copy the331.2M campaign peak as a bootstrap limit.

```sh
nix develop --command python tests/prepare_lean_bridge.py /tmp/ayxg-fp-bridge
nix develop --command sh -c '
  PYTHONPATH="$PWD/python:/tmp/ayxg-fp-bridge/leanpy" \
  python tests/differential_fp.py --bridge-project /tmp/ayxg-fp-bridge \
    --examples 20 --artifacts /tmp/ayxg-fp-correspondence
'
```

The source pin is
verified by preparation; native compilation uses standard Lake library facets,
projected to Lean's exact parsed import closure. The projection records every
source hash and native link target. It changes only disposable build metadata.
No candidate/native SUT binaries are executed by this test.

`run-scoped-v18.sh` and `run-ffi-v19.sh` preserve the exact observed staged-run
commands, including valid reuse of unchanged native inputs. `run-v18.json` and
`run-v19.json`, journal files, and coverage JSON preserve results and resources.
9,419 comparisons include mode-independent repetitions; they are not9,419 unique
bit-patterns. The canonical NaN/invalid-cast/zero-tie interpretation is explicit.
