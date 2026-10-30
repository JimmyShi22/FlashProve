-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyAtFkMore.lean. THE THIRD OF AtFk's THREE FACTS ON PUBLIC VALUES (Johnson/RunOne/KeyRowsAtFk.lean): «the one-time plan's codes are the sized key's», which start₂ lays into the shared chain's first state: OUT OF THE DESCRIPTION's OWN TESTS ON THE PLAN:
  pubsOf_k        PROVED: what sourceOf m returns holds m itself and, as its key's chains, m's own
  codes_of_front  PROVED: where X's key's chains are its Made's own: the shared chain's front block's test on the plan (sharedFrontOk: «the codes read back are the planner's») and fileOk («chains 1 and 2 hold the same codes») give it
  codes_at_pubsOf PROVED: so at X := what sourceOf m returns (at a letter X it follows from nothing)
  PlanOk · planOk₁  PROVED: the plan's two maps are inverse at I and V (the last chain's files' law of its first block wants K₁.num (K₁.orc 2) = some 2; public, asked nowhere): at the first chain's plan wherever the ranges' test has a stage
  atFk_of         PROVED: so AtFk's three facts on values follow from fileOk and the front block's planOk; what is left are the conditions on the letters (orc · arr · reads · off)
Limits. That F.planOk gives the front block's planOk is not shown here (Block.lean's planOkCore runs over all blocks). Nothing on soundness.

-/
import Johnson.RunOne.KeyRowsAtFk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key

theorem pubsOf_k (m : Johnson.G.OfPlan.Made) (X : Source) (h : sourceOf m = .ok X) : X.chains = m.p.chains ∧ X.Y.k = m.p.chains.key := by
  unfold sourceOf at h
  cases hD : Johnson.G.OfPlan.declKOf m with
  | error e => simp [hD, bind, Except.bind] at h
  | ok D =>
    cases hT : toldOfMade m with
    | error e => simp [hD, hT, bind, Except.bind] at h
    | ok T =>
      simp only [hD, hT, bind, Except.bind, pure, Except.pure] at h
      cases h
      exact ⟨rfl, rfl⟩

/-- **The plan's number of a message and the message of a number are inverse at I and V.** -/
def PlanOk (K : KPlan) : Prop := ∀ k ∈ [0, 2], ∃ o, K.orc k = some o ∧ K.num o = some k

theorem planOk₁ (one : OneTime) (h : 1 ≤ one.ranges.stages.length) : PlanOk (Johnson.RunOne.KeyRows1.plan₁ one) := by
  intro k hk
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
  rcases hk with rfl | rfl
  · exact ⟨0, rfl, rfl⟩
  · refine ⟨1 + 2 * one.ranges.stages.length, rfl, ?_⟩
    have hne : one.ranges.stages ≠ [] := by
      intro e
      rw [e] at h
      exact absurd h (by decide)
    simp [Johnson.RunOne.KeyRows1.plan₁, Johnson.RunOne.KeyReaders.planOf, hne]

/-- THE KEY FILE's TABLES AT descriptionFromSource ARE LAID AT idx := [0] (KeyRowsAtFk.lean: On₃): at that list every member is below V's number and two (the last chain's files' row 3.0: «idxBelow»). THAT THE KEY FILE's INDEX MASKS' MESSAGES ARE JUST [0] IS NOT SAID HERE: it is promised by the first chain's book-keeping and evaluated at the honest walk. -/
theorem idxBelow₀ (w : Nat) : ∀ i ∈ [0], i < w + 2 := fun i hi => by
  have e : i = 0 := by simpa using hi
  omega

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

theorem codes_of_front (hk : X.Y.k = X.chains.key) (hf : sharedFrontOk X.chains = true) (h : (descriptionFromSource X N P).fileOk = true) :
    (oneAt X).codes = codesAt X := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have hm : ∀ c ∈ shapeClauses X.Y.k (shapeAt X), c.2 = true := fun c hc =>
    List.all_eq_true.1 ha c (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hc))))))
  have h10 := hm _ (List.mem_of_getElem? (l := shapeClauses X.Y.k (shapeAt X)) (i := 10) rfl)
  have h3 := List.all_eq_true.1 hf _ (List.mem_of_getElem? (l := sharedFrontClauses X.chains) (i := 3) rfl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h10 h3
  show X.Y.k.oneTime.codes = X.chains.made.sized.key.codes
  rw [h10.1, hk, h3]

theorem codes_at_pubsOf (m : Johnson.G.OfPlan.Made) (hX : sourceOf m = .ok X) (hf : sharedFrontOk m.p.chains = true) (h : (descriptionFromSource X N P).fileOk = true) :
    (oneAt X).codes = codesAt X := by
  obtain ⟨e1, e2⟩ := pubsOf_k m X hX
  exact codes_of_front X N P (by rw [e2, e1]) (by rw [e1]; exact hf) h

variable {Cells M Smp Rec : Type} (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (off₃ : Nat → Nat)

theorem atFk_of (hk : X.Y.k = X.chains.key) (hf : sharedFrontOk X.chains = true) (h : (descriptionFromSource X N P).fileOk = true)
    (orc : B.orc₁ = (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc) (arr : ArrOk B.h₂ at_ [0, 2, 3, 4, 5]) (reads : ReadsPinned B.h₂ at_ R [3, 4, 5])
    (off : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1) : AtFk X B at_ R off₃ :=
  ⟨form_of_fileOk X N P h, lin_of_fileOk X N P h, codes_of_front X N P hk hf h, orc, arr, reads, off⟩

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.idxBelow₀
#print axioms Johnson.RunOne.KeyRows23.planOk₁
#print axioms Johnson.RunOne.KeyRows23.pubsOf_k
#print axioms Johnson.RunOne.KeyRows23.codes_of_front
#print axioms Johnson.RunOne.KeyRows23.codes_at_pubsOf
#print axioms Johnson.RunOne.KeyRows23.atFk_of
