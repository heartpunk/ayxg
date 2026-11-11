import Observer
open MovObserver.NativeObserver

-- Transport only: the shared observer executes the exact supplied bytes.
def main (args : List String) : IO Unit := do
  let [fixtureDir, workDir, instructionPath, inputPath, outputPath] := args
    | throw <| IO.userError "expected fixtures, workdir, instruction, input and output"
  let input ← IO.FS.readBinFile inputPath
  if input.size != 24 then throw <| IO.userError "expected RAX, RDX, divisor"
  let instruction ← IO.FS.readBinFile instructionPath
  let loader ← IO.FS.readBinFile (fixtureDir ++ "/loader.bin")
  let capture ← IO.FS.readBinFile (fixtureDir ++ "/observer.bin")
  let rax := word input 0
  let rdx := word input 8
  let divisor := word input 16
  let address : UInt64 := 0x100000000
  let gprs := (((Array.replicate 16 (0 : UInt64)).set! 0 rax).set! 2 rdx).set! 7 divisor
  let gprs := gprs.set! 5 (address + 0x58)
  let memory : Array Region := #[⟨address, putWord (zeros 8) 0 divisor⟩]
  let result ← observeFallthrough loader capture (workDir ++ "/target.elf")
    { instruction, gprs, flags := 0x202, memory }
  let output := putWord (putWord (zeros 16) 0 result.gprs[0]!) 8 result.gprs[2]!
  IO.FS.writeBinFile outputPath output
