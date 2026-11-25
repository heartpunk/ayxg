import Lake

open Lake DSL

package ayxg where
  version := v!"0.1.0"

-- FloatLib's checked-in Lake manifest still carries an older Mathlib pin;
-- explicitly select the release matching this Lean toolchain.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

-- Exact pinned upstream source is provided by the qualified Nix environment.
-- Lake fails closed outside it; no accidental floating dependency fallback.
require floatlib from (run_io do
  let some source ← IO.getEnv "AYXG_FLOATLIB_SOURCE"
    | throw <| IO.userError "Run Lake through nix develop: AYXG_FLOATLIB_SOURCE missing"
  let some key ← IO.getEnv "AYXG_FLOATLIB_SOURCE_KEY"
    | throw <| IO.userError "Run Lake through nix develop: AYXG_FLOATLIB_SOURCE_KEY missing"
  -- The content key covers both the SMT extension and axiom-footprint patches.
  let writable := __dir__ / ".lake" / ("floatlib-source-" ++ key)
  unless ← writable.pathExists do
    IO.FS.createDirAll writable
    let copied ← IO.Process.output { cmd := "cp", args := #["-R", source ++ "/.", writable.toString] }
    if copied.exitCode != 0 then throw <| IO.userError copied.stderr
    let permissions ← IO.Process.output { cmd := "chmod", args := #["-R", "u+w", writable.toString] }
    if permissions.exitCode != 0 then throw <| IO.userError permissions.stderr
  return writable)

@[default_target]
lean_lib Ayxg where
  globs := #[`Ayxg.*]
