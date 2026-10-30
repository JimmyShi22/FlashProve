-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/EndsOfRun.lean: AT THE HEAD's BATCHING, A RETURN OF A RUN OF THE OUTPUT HEAD GIVES THAT ROW's TEST
ON VALUES: endsS (BatchBools.lean) at the state in front: of the head's rows in cellV (BatchCells.lean) these four need no
value from outside. K8.equations' row (eqPreB) is not here. Statements and proofs.

  `endsS_of_Ends`    the Bool from the sentence
  `endsS_of_three`   a return of "norm", "policy" or "logits"
  `endsS_of_join`    a return of "join"
  `guarded_run`      a return of a guarded run is a return of the run

Limits. Nothing says that a run returns. Nothing on any property.
-/
import Johnson.AtFull.Shape.BatchCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Shape
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)

theorem endsS_of_Ends {p : Par} {s : S} (h : Ends p s) : endsS p s = true := by
  unfold endsS
  cases hl : s.lookHeard? with
  | none => rfl
  | some g => exact h.ends g hl

variable (W : OnBytes.Model.Verify.Public) (iU3 : Nat)

/-- **A return of one of the three runs gives the row's test.** -/
theorem endsS_of_three {name : String} (hn : name ∈ ["norm", "policy", "logits"]) {n : Nat} {s : S}
    {z : List VerifiableInference.Desc.Claim × S} (hz : (rowThree W iU3 name).run n s = .ok z) :
    endsS (parOf W.hS (workAtW W)) s = true := by
  obtain ⟨cs, s'⟩ := z
  exact endsS_of_Ends (three_strong W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name _
    (bare_look W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name hn) n s s' cs hz).2.2

/-- **A return of "join" gives the row's test.** -/
theorem endsS_of_join {n : Nat} {s : S} {z : List VerifiableInference.Desc.Claim × S}
    (hz : VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim)
      (callerKeys (parOf W.hS (workAtW W)) (seatAt W.hS iU3)) n s = .ok z) :
    endsS (parOf W.hS (workAtW W)) s = true := by
  obtain ⟨cs, s'⟩ := z
  exact endsS_of_Ends (join_strong W.hS iU3 (parOf W.hS (workAtW W)) n s s' cs hz).2

/-- A return of a guarded run is a return of the run. -/
theorem guarded_run {same : S → S → Bool}
    {r : Nat → S → Except String (List ProofFile.Cl × S)} {n : Nat} {s : S} {z : List ProofFile.Cl × S}
    (h : IM.guardRun same r n s = .ok z) : ∃ y, r n s = .ok y := by
  unfold IM.guardRun at h
  cases e : r n s with
  | error x =>
    rw [e] at h
    cases h
  | ok y => exact ⟨y, rfl⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.endsS_of_three
#print axioms Johnson.AtFull.Shape.Scope.endsS_of_join
#print axioms Johnson.AtFull.Shape.Scope.guarded_run
