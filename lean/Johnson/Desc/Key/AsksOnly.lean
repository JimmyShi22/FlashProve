-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/AsksOnly.lean: a check on Lean's environment, run when this file is compiled.
Compiled at every change of the door (Johnson/Desc/Key/Asks.lean). Where the
check fails this file does not compile.
ONLY: the door's module declares `lawsAsk` and nothing else at all; `lawsAsk` has no other code to
run than its term (by neither of Lean's two attributes for that), is no instance, no rule of the
simplifier, and is unfolded as any plain definition is.
THROUGH: of the modules that the door reaches and that the two library files named here
(Johnson/Desc/Key/Road.lean, Johnson/Desc/BlockSlot.lean) do not: none of the constants that they
declare is an instance, HAS A TYPE THAT IS A CLASS's (by Lean's own routine for that question,
the one that an instance's elaboration asks; and by a reading of the type's head with definitions
unfolded: so an instance that is scoped, local or not yet marked is seen too), has other code to run
than its term, or has a type that names a constant of Lean's own machinery (a macro, a parser, an
elaborator).
Limits. By names and marks in the compiled files. THIS FILE IMPORTS THE DOOR: what comes through the
door could touch this file's own text: the sheet Johnson/RunOne/SheetKeyDoor.lean
[not in this library] asks the same and
imports Lean alone. Nothing on soundness.

-/
import Johnson.Desc.Key.Asks

open Lean in
#eval show CoreM Unit from do
  let envS ← getEnv
  let door := `Johnson.Desc.Key.Asks
  let ask := `VerifiableInference.Desc.Key.lawsAsk
  let some idx := envS.getModuleIdx? door | throwError "the door's module is not in the environment"
  let coded (n : Name) : Bool := (Compiler.getImplementedBy? envS n).isSome || isExtern envS n
  let own := envS.constants.fold
    (fun acc n _ => if envS.getModuleIdxFor? n == some idx then n :: acc else acc) []
  let badOwn := own.filter (· != ask)
  let simps := Meta.simpExtension.getState envS
  let marked := coded ask || Meta.isInstanceCore envS ask ||
    simps.lemmaNames.contains (.decl ask) || simps.toUnfold.contains ask ||
    getReducibilityStatusCore envS ask != .semireducible
  unless badOwn.isEmpty && !marked && own.contains ask do
    throwError "THE DOOR BRINGS MORE THAN ITS ONE PLAIN NAME: {badOwn} ; a mark on it: {marked}"
  let closure (roots : List Name) (cut : Option Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut todo := roots
    while !todo.isEmpty do
      match todo with
      | [] => break
      | m :: rest =>
        todo := rest
        if seen.contains m then continue
        seen := seen.insert m
        if cut == some m then continue
        match envS.getModuleIdx? m with
        | some i => todo := (envS.header.moduleData[i.toNat]!.imports.toList.map (·.module)) ++ todo
        | none => pure ()
    return seen
  let base := closure [`Johnson.Desc.Key.Road, `Johnson.Desc.BlockSlot] none
  let through := (closure [door] none).toList.filter fun m => !base.contains m && m != door
  let tIdx := through.filterMap envS.getModuleIdx?
  let ofClass (c : ConstantInfo) : Bool := Id.run do
    let mut e := c.type
    for _ in [0:8] do
      while e.isLambda do
        e := e.bindingBody!
      match e.getForallBody.getAppFn with
      | .const k _ =>
        if isClass envS k then return true
        match envS.find? k with
        | some (.defnInfo d) => e := d.value
        | _ => return false
      | _ => return false
    return false
  let cand := envS.constants.fold (fun acc n c =>
    match envS.getModuleIdxFor? n with
    | some i => if tIdx.contains i then (n, c) :: acc else acc
    | none => acc) []
  let mut bad : List Name := []
  for (n, c) in cand do
    let byLean ← try (Meta.isClass? c.type).run' catch _ => pure (some `failed)
    if coded n || Meta.isInstanceCore envS n || byLean.isSome || ofClass c ||
        c.type.getUsedConstants.any (fun u => (`Lean).isPrefixOf u) then
      bad := n :: bad
  unless bad.isEmpty do
    throwError "THROUGH THE DOOR COMES MORE THAN PLAIN DEFINITIONS AND THEOREMS: {bad}"
