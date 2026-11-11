# Fresh PCMPGTB extraction versus native execution

This bounded Linux x86-64 check consumes the two sudo-derived instruction byte
files in `tests/regressions/sudo-pcmpgtb`. For each encoding it assembles a
minimal ELF with the target at `0x400170` and a RET as extraction scaffolding,
then runs the normal `wruh-fresh` CLI on the rooted function. It checks the
extracted occurrence's address and exact bytes, parses the emitted AYXG DAG,
and evaluates the target guard and destination update for generated inputs.

The shared WRUH `NativeObserver.observeFallthrough` constructs its own execution
ELF with the same target bytes at `0x400170`; its post-target jump leads to the
capture code. The adapter checks installation of both XMM inputs and returns the
16 captured destination bytes. The test compares those bytes with the extracted
model. The surrounding ELF scaffolds differ; the instruction address, bytes,
and concrete XMM operand values coincide. This is an instruction-level
comparison, not execution of the extraction ELF as a process. Other machine
state is not compared. An unexpected fault or observer failure fails the test.

Each encoding receives 12 seeded cases by default. Each pair samples signed-boundary values and arbitrary byte lanes.
The result is a bounded nonfaulting check, not exhaustive verification or a
fault-behavior test.

To run, use an x86-64 Linux machine with the WRUH source, its built `wruh-fresh`,
its native-observer fixtures, the pinned WRUH Nix shells, and bubblewrap user
namespaces. Set `WRUH` to that checkout and `AYXG` to this checkout, then build
the adapter in the WRUH `nativeObserver` shell:

```sh
nix develop "$WRUH#nativeObserver" --command bash "$AYXG/tests/native_pcmpgtb/build-observer.sh" \
  "$WRUH/experiments/mov_observer/native_observer" \
  "$WRUH/experiments/mov_observer/native_shim" /tmp/ayxg-pcmpgtb-build
```

Run from AYXG inside its CI shell and the WRUH native-observer shell, with the
WRUH extraction environment available (including `GHOT_NIX_ANGR_ROOT`):

```sh
PYTHONPATH="$AYXG/python" python "$AYXG/tests/native_pcmpgtb/check.py" \
  --observer /tmp/ayxg-pcmpgtb-build/observer-bridge \
  --observer-fixtures "$WRUH/experiments/mov_observer/fixtures" \
  --wruh-root "$WRUH" --wruh-fresh "$WRUH/.lake/build/bin/wruh-fresh" \
  --examples 12 --seed 270933
```

The run requires the shared observer and `wruh-fresh`; it is not wired into
AYXG's ordinary CI targets. A mismatch reports the seed, both input vectors,
the model result, and the observed result.
