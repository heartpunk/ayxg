import Observer
open MovObserver.NativeObserver

-- Adapter to the shared WRUH observer. No instruction semantics live here.
def main (args : List String) : IO Unit := do
  let [fixtureDir, workDir, instructionPath, inputPath, outputPath, destText, srcText] := args
    | throw <| IO.userError "expected fixtures, workdir, instruction, inputs, output, destination and source"
  let some dest := destText.toNat? | throw <| IO.userError "invalid destination register"
  let some src := srcText.toNat? | throw <| IO.userError "invalid source register"
  if dest >= 16 || src >= 16 || dest == src then throw <| IO.userError "invalid XMM registers"
  let input ← IO.FS.readBinFile inputPath
  if input.size != 32 then throw <| IO.userError "expected exactly two XMM inputs"
  let instruction ← IO.FS.readBinFile instructionPath
  let loader ← IO.FS.readBinFile (fixtureDir ++ "/loader.bin")
  let capture ← IO.FS.readBinFile (fixtureDir ++ "/observer.bin")
  let gprs : Array UInt64 := Array.replicate 16 0
  let request : Request := { instruction := ByteArray.mk #[0x90], gprs, flags := 0x202, memory := #[] }
  let baseline ← observeFallthrough loader capture (workDir ++ "/baseline.elf") request
  let mut fp := baseline.installedFp
  for i in [:16] do
    fp := fp.set! (160 + 16 * dest + i) input[i]!
    fp := fp.set! (160 + 16 * src + i) input[16+i]!
  let result ← observeFallthrough loader capture (workDir ++ "/target.elf")
    { request with instruction, fp := some fp }
  let mut output := ByteArray.empty
  for i in [:16] do
    if result.installedFp[160 + 16 * dest + i]! != input[i]! ||
       result.installedFp[160 + 16 * src + i]! != input[16+i]! then
      throw <| IO.userError "XMM input installation mismatch"
    output := output.push result.terminalFp[160 + 16 * dest + i]!
  IO.FS.writeBinFile outputPath output
