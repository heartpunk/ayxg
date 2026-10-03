import Lean

/-- Stream exact import headers using Lean's own parser, including module-system
public/meta/import-all forms. No source or semantics are changed. -/
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let path := line.trimAscii.toString
    try
      let header ← Lean.parseImports' (← IO.FS.readFile path) path
      let names := header.imports.map fun entry => Lean.Json.str entry.module.toString
      output.putStrLn (Lean.Json.arr names).compress
    catch error =>
      output.putStrLn (Lean.Json.mkObj [("error", toJson error.toString)]).compress
    output.flush
