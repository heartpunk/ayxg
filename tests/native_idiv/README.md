# IDIV extraction-to-native check

This bounded Linux x86-64 check reads the exact instruction bytes from
`tests/fixtures/chroot_print_int_idiv.json`. For each encoding it assembles a
minimal ELF function with the instruction at `0x400170`, invokes Wruh's normal
`wruh-fresh` CLI on that function, selects the matching occurrence, and decodes
its emitted AYXG artifact. For each seeded input it evaluates the enabled model
edge and compares RAX and RDX with the shared Wruh native observer. The observer
places the same bytes at the same target PC and installs the same register and
memory inputs. The trailing `ret` is extraction scaffolding and is not executed
by the observer. Undefined success flags are not compared.

Inputs are sign-extended signed 64-bit dividends and signed 64-bit divisors;
zero divisors and the overflowing minimum-dividend / -1 case are rejected.
The observer must report successful fallthrough. Model, setup, timeout, or
observation errors fail the check. This does not test IDIV faults or all 128-bit
dividends. The fixture's binary digest and original occurrence metadata identify
the encodings; the retained original failure did not identify its exact site.

## Running

Use an isolated Linux x86-64 runner with the pinned Wruh angr environment,
`as`, `ld`, Python, bubblewrap, and an already built AYXG checkout at this PR
revision. Wruh's native observer source, fixtures, Lean toolchain and native shim
are required. The following commands use `WRUH`, `AYXG`, and a scratch `OUT`
as absolute paths. Run the two build commands in Wruh's `nativeObserver` shell;
run the check in its angr runtime shell, with `bwrap` on `PATH`. Configure
`WRUH_PYTHON` if the angr Python interpreter is not the default.

```sh
bash "$AYXG/tests/native_idiv/build-observer.sh" \
  "$WRUH/experiments/mov_observer/native_observer" \
  "$WRUH/experiments/mov_observer/native_shim" "$OUT/observer"
bash "$AYXG/tests/native_idiv/build-extractor.sh" "$WRUH" "$AYXG" "$OUT/extractor"
PYTHONPATH="$AYXG/python" python "$AYXG/tests/native_idiv/check.py" \
  --wruh-source "$WRUH" --wruh-fresh "$OUT/extractor/wruh-fresh" \
  --observer "$OUT/observer/observer-bridge" \
  --observer-fixtures "$WRUH/experiments/mov_observer/fixtures"
```

`build-extractor.sh` builds the ordinary `Wruh.AngrMain` modules against the
specified AYXG build and runs that same CLI entry point with `lean --run`. This
prevents an older prebuilt Wruh executable from silently using a different AYXG
codec. The check defaults to 12 cases per encoding and seed 260013; the case
count is limited to 100. It is an explicit integration check, not part of the
normal Python unit suite or a claim of exhaustive coverage.
