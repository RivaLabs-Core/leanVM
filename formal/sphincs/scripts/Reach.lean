import SphincsSecurity
import Lean

/-!
`lake env lean scripts/Reach.lean` writes `reach.txt`, listing each local declaration, its source range and whether the proofs listed below use it. Declarations needed only by the elaborator, such as instances and simp lemmas, may still need to be kept when pruning.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[``SphincsSecurity.sphincs_has_127_bits_of_classical_security,
    ``SphincsSecurity.sphincs_is_correct, ``SphincsSecurity.sphincs_is_complete]
  let mut visited : NameSet := {}
  let mut stack : Array Name := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      for c in ci.type.getUsedConstants do
        if !visited.contains c then stack := stack.push c
      match ci.value? (allowOpaque := true) with
      | some v =>
        for c in v.getUsedConstants do
          if !visited.contains c then stack := stack.push c
      | none => pure ()
  let mut out : String := ""
  let mut total := 0
  let mut reached := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index.toNat]!
    if !moduleName.toString.startsWith "SphincsSecurity" then continue
    total := total + 1
    let r := visited.contains name
    if r then reached := reached + 1
    let range ← match ← findDeclarationRanges? name with
      | some rs => pure s!"{rs.range.pos.line}|{rs.range.endPos.line}"
      | none => pure "-|-"
    out := out ++ s!"{moduleName}|{name}|{range}|{if r then "1" else "0"}\n"
  IO.FS.writeFile "reach.txt" out
  logInfo m!"total {total} reached {reached}"
