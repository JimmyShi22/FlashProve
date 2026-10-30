-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardPublicCut.lean: kind K5: THE SECOND PAYER OF PlanIs
(Att/GuardPublic.lean): it holds at every public record with PublicCut
(Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean): so at every return of
publicOfO o, at every o: publicOf's text with a letter in the second hash function's place.

Main names:
  `planIs_of_cut`: **PublicCut pol KL X → PlanIs X**: each stored attention plan of X is, but for
    the field plFor of seam.tl, what the planner returns at that plan's own settings, input and
    configuration.
  `p4_of_cut`: PublicCut pol KL X → X.A[g]? = some a → X.p4 = true.
  `planIs_publicO`: publicOfO o pol KL layout = .ok X → PlanIs X.
How. PublicCut's own clauses say that X.A is the list A0 with the records that attentionOwners
returns laid in, and that A0's members are what Attention.group returns. Called, not typed anew:
owners_plFor (what attentionOwners returns is what it was handed but for plFor;
OnBytes/Tie/Pv/Lookup/Ends/FoPublicAPlFor.lean) · ConfigCut.at (PublicAtCut.lean) · group_plan
(Johnson/Road/Lane5AttPlan.lean) · plan_at_own (Att/GuardPublic.lean). The walk is that of the
library's public_A_plFor, with PublicCut in the place of publicOf_cut. PublicAtCut.lean's cut_A is
not enough: it keeps of seam.tl the matrices and tau alone. So the law at the seated block
(K05_law_one_guard and those above it) has its premise hP paid at a description's public record
whichever o it was made at.
Limits. One direction: from a record with PublicCut. At no o is publicOfO o shown to return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model Fo.BatRows Fo.Pub
open VerifiableInference.PlanWritten (PublicCut publicCut_of_O publicOfO)

/-- **PlanIs at every public record with PublicCut.** -/
theorem planIs_of_cut {pol KL : ByteArray} {X : Verify.Public} (C : PublicCut pol KL X) :
    PlanIs X := by
  obtain ⟨⟨_, _, _, _, _, _, sc, A0, seen, _, k3, k6, k7⟩, _⟩ := C
  intro g a hg
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := Fo.PubA.owners_plFor k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, kc⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, _, l2⟩ := kc.at
    obtain ⟨cf, _, m2, _⟩ := OnBytes.Road.L5.group_plan (l2 g a0 e1)
    have f4 : s.tl = { a0.seam.tl with plFor := s.tl.plFor } := by
      have t : s.tl = { s0.tl with plFor := s.tl.plFor } := f2
      rw [f3] at t
      exact t
    refine ⟨a0, s.tl.plFor, ?_, ?_⟩
    · subst e3
      exact plan_at_own m2
    · rw [e3, ← f4]
  · simp at e1

/-- **A public record with PublicCut and a stored attention plan covers attention**: below profile 4
PublicCut's own clause says that there is no plan. -/
theorem p4_of_cut {pol KL : ByteArray} {X : Verify.Public} (C : PublicCut pol KL X) {g : ℕ}
    {a : Attention.Plan} (hg : X.A[g]? = some a) : X.p4 = true := by
  obtain ⟨⟨_, _, _, _, _, _, sc, A0, seen, _, k3, _, k7⟩, _⟩ := C
  rcases k3 with ⟨h4, _⟩ | ⟨_, rfl⟩
  · exact h4
  · rw [k7] at hg
    simp at hg

/-- **At every return of publicOfO o, at every o.** -/
theorem planIs_publicO {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : publicOfO o pol KL layout = .ok X) :
    PlanIs X :=
  planIs_of_cut (publicCut_of_O h)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.planIs_of_cut
#print axioms VerifiableInference.Desc.First.Att.P.p4_of_cut
#print axioms VerifiableInference.Desc.First.Att.P.planIs_publicO
