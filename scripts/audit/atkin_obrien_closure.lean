import RamanujanTau.OrdQuot.Atkin
open Lean Meta Elab Command

/-- constants appearing in the TYPE (statement) with their defining module -/
elab "#stmt_consts " n:ident : command => do
  let env ← getEnv
  let some ci := env.find? n.getId | throwError "no decl"
  let cs := ci.type.getUsedConstants
  for c in cs do
    let m := match env.getModuleIdxFor? c with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => "(this file)"
    logInfo m!"{c}  ←  {m}"

/-- full transitive dependency closure of the PROOF: count, repo-defined count, and every axiom -/
elab "#closure " n:ident : command => do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut stack := [n.getId]
  let mut axs : Array Name := #[]
  let mut repo := 0
  while !stack.isEmpty do
    let c := stack.head!; stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    if let .axiomInfo _ := ci then axs := axs.push c
    if let some i := env.getModuleIdxFor? c then
      if (toString env.header.moduleNames[i.toNat]!).startsWith "RamanujanTau" then repo := repo + 1
    let body : Array Name := match ci with
      | .thmInfo v => v.value.getUsedConstants
      | .defnInfo v => v.value.getUsedConstants
      | .opaqueInfo v => v.value.getUsedConstants
      | _ => #[]
    let deps := ci.type.getUsedConstants ++ body
    for d in deps do
      if !seen.contains d then stack := d :: stack
  logInfo m!"closure size {seen.size}, repo-defined {repo}, axioms: {axs}, sorryAx present: {seen.contains ``sorryAx}"

#stmt_consts OrdQuot.atkin_obrien_13
#closure OrdQuot.atkin_obrien_13
#closure OrdQuot.atkin_obrien_17
#closure OrdQuot.atkin_obrien_19
#closure OrdQuot.atkin_obrien_23
