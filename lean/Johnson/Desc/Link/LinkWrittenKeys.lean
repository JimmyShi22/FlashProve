-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkWrittenKeys.lean: THE SEAT's VALUE (Johnson/Desc/Link/LinkWritten.lean: linkDecisionAtParameterFile) RUNS THE WRITTEN LINK's DESCRIPTION AT THE KEYS WRITTEN OF THE TWO RECORDS: the first table's, and the copy's with item := 1: the rewrite of its
key expression «keysOfX frS.P.v 29 1 (anT frS.P.v 1) (recX rr)» (LinkWritten.lean:55) by keys_recX (OnBytes/Flat/LinkSib.lean): as decOfRoot_keys (LinkSlotKeys.lean) has it for the elder value.
  decWritten_keys       the equation, at every parameter file; no premise
  decWritten_keys_at    where the parameter file's lines are the full size's written ones: linkDecisionAtParameterFile pol = the description at the typed parameters, run at these keys (by linkAt_full)
  decWritten_keys_scope the same in the goals' scope
OBJECT: Desc.K15.linkDecisionAtParameterFile · USER: whoever runs or reads the seat at typed records · LETTERS: none. Equations of values. Nothing on soundness.
-/
import Johnson.Goal.Conditions.EntryWrittenLaw
import Johnson.Desc.Link.LinkSlotKeys

set_option autoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params VerifiableInference.Desc
open OnBytes.Flat OnBytes.Slice TypedOracleCompiler.Slice _root_.Run

theorem decWritten_keys (pol : ByteArray) : linkDecisionAtParameterFile pol =
    match readLines pol with
    | .ok (l, _) =>
      if l = recordLines then
        match linkAt frP recordPlan with
        | .ok L => fun rr V => L.F.run (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V
        | .error _ => fun _ _ => false
      else fun _ _ => false
    | .error _ => fun _ _ => false := by
  unfold linkDecisionAtParameterFile
  cases readLines pol with
  | error e => rfl
  | ok x =>
    obtain ⟨l, b⟩ := x
    by_cases hl : l = recordLines
    · simp only [hl, if_true]
      cases linkAt frP recordPlan with
      | error e => rfl
      | ok L =>
        funext rr V
        show L.F.run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) (recX rr)) V = _
        rw [keys_recX]
    · simp only [hl, if_false]

theorem decWritten_keys_at {pol b : ByteArray} (h : readLines pol = .ok (recordLines, b)) :
    linkDecisionAtParameterFile pol = fun rr V => (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run
      (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V := by
  rw [decWritten_keys, h]
  simp only [if_true, linkAt_full]

theorem decWritten_keys_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) :
    linkDecisionAtParameterFile Z.pol = fun rr V => (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run
      (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V := by
  obtain ⟨b, hb⟩ := scope_reads hZ
  exact decWritten_keys_at hb

end Desc.K15

#print axioms Desc.K15.decWritten_keys
#print axioms Desc.K15.decWritten_keys_at
#print axioms Desc.K15.decWritten_keys_scope
