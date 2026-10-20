import Ayxg.LTS.QfAbv.SymbolicStep
import Lean
open Lean

partial def axiomPath (root target : Name) : StateT NameSet CoreM (Option (List Name)) := do
  if root == target then return some [root]
  if (← get).contains root then return none
  modify fun seen => seen.insert root
  let env ← getEnv
  let some info := env.find? root | return none
  for dep in info.getUsedConstantsAsSet.toArray do
    if (← collectAxioms dep).contains target then
      if let some path ← axiomPath dep target then
        return some (root :: path)
  return none

run_cmd do
  for root in [``Ayxg.QfAbv.FPFormat.floatFormat,
      ``FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN,
      ``Ayxg.QfAbv.canonicalNaN] do
    for ax in [``Classical.choice, ``Quot.sound] do
      let (result, _) ← Elab.Command.liftCoreM ((axiomPath root ax).run {})
      logInfo m!"{root} -> {ax}: {result}"
