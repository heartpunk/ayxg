import Lake

open Lake DSL

package ayxg where
  version := v!"0.1.0"

-- Exact patched source is provided by the qualified Nix environment. Lake
-- fails closed outside it; no accidental upstream/unpatched fallback.
require floatlib from (run_io do
  let some source ← IO.getEnv "AYXG_FLOATLIB_SOURCE"
    | throw <| IO.userError "Run Lake through nix develop: AYXG_FLOATLIB_SOURCE missing"
  let some key ← IO.getEnv "AYXG_FLOATLIB_SOURCE_KEY"
    | throw <| IO.userError "Run Lake through nix develop: AYXG_FLOATLIB_SOURCE_KEY missing"
  let writable := System.FilePath.mk ".lake" / ("floatlib-source-" ++ key)
  unless ← writable.pathExists do
    IO.FS.createDirAll writable
    let copied ← IO.Process.output { cmd := "cp", args := #["-R", source ++ "/.", writable.toString] }
    if copied.exitCode != 0 then throw <| IO.userError copied.stderr
    let permissions ← IO.Process.output { cmd := "chmod", args := #["-R", "u+w", writable.toString] }
    if permissions.exitCode != 0 then throw <| IO.userError permissions.stderr
  return writable)

lean_lib Ayxg where
  globs := #[`Ayxg.*]
