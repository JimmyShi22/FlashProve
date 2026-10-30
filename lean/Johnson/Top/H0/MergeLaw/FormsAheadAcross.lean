-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FormsAheadAcross.lean: K11's SECOND TIE: THE SIBLING OF `formsIn_merge`
(FormsAcross.lean) AT THE PUBLIC TEST `K9.formsInA` (Johnson/Desc/First/Batch/Ahead.lean: a run's
forms may name an array that the open segment has not yet sent): THE TEST PASSES THE MERGE's
ACCEPTING STEP, AT ANY RUN WHOSE READER ANSWERS BEHIND WHAT IT ANSWERS IN FRONT. Theorems.

What is said.
  `aheadIn_same`, `entInA_rides`, `affInA_more`: free of the kind: "ahead" reads the open link's
    context alone; so, where that context is the same and the later part rides, an entry that is
    there or ahead in front is so behind; the slots go by `slotIn_more`
    (Johnson/Desc/Reads/FormsPass.lean).
  `more_at_merge`: `Rides` and `More` at the merge's step, as a statement of its own (what
    `formsIn_merge` pays inside).
  `formsInA_merge`: **the test at s gives the test at s'**, under the six premises of
    `formsIn_merge`, sign for sign.

Limits. Implications: shown at no real state. `Fwd` is shown here of no run. The sentence's side
(`formsQA`) is other files' to show. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.FormsAcross
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.K9 (segAt? lateAt lateOk mergeOf Readers aheadOf aheadIn entInA affInA
  formsInA)
open VerifiableInference.Desc.Sound (Rides)
open VerifiableInference.Reads
open VerifiableInference.Reads.Pass (Fwd entIn_rides slotIn_more)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-! ## Free of the kind -/

section
variable (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ))

/-- "Ahead" reads the open link's context alone. -/
theorem aheadIn_same {a b : K9.Part} (hL : b.L = a.L) (c : ℕ × String) :
    aheadIn sent own b c = aheadIn sent own a c := by
  unfold aheadIn aheadOf
  rw [hL]

/-- An entry that is there or ahead in front is so behind. -/
theorem entInA_rides {a b : K9.Part} (hL : b.L = a.L) (hr : Rides own a b) {x : Ent}
    (h : entInA sent own a x = true) : entInA sent own b x = true := by
  unfold entInA at h ⊢
  rcases Eq.mp (Bool.or_eq_true _ _) h with h | h
  · rw [entIn_rides own hr h]
    rfl
  · rw [hL, show aheadIn sent own b = aheadIn sent own a from funext (aheadIn_same sent own hL), h]
    exact Bool.or_true _

/-- A form that names only what is there or ahead in front names only such things behind. -/
theorem affInA_more {late : List (ℕ × E × E)} {a b : K9.Part} {s s' : S} (hL : b.L = a.L)
    (hr : Rides own a b) (M : Pass.More late a b s s') {f : Aff}
    (h : affInA sent own (mergeOf s) late a f = true) :
    affInA sent own (mergeOf s') late b f = true := by
  unfold affInA at h ⊢
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact Eq.mpr (Bool.and_eq_true _ _)
    ⟨List.all_eq_true.2 fun x hx => entInA_rides sent own hL hr (List.all_eq_true.1 h1 x hx),
      List.all_eq_true.2 fun x hx => slotIn_more own hr M (List.all_eq_true.1 h2 x hx)⟩

end

/-! ## At the merge's step -/

/-- **`Rides` and `More` at the merge's accepting step**, at any list of late slots that passes its
test in front and holds not the slot of the merge's end value. (What `formsIn_merge` pays inside,
FormsAcross.lean, as a statement of its own.) -/
theorem more_at_merge (own : List (ℕ × ℕ)) (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (pa : K9.Part) (hpa : segAt? s = some pa)
    (hS : Sized pa.F) (hfree : pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false)
    (late : List (ℕ × E × E)) (hlo : lateOk late pa = true)
    (hlate : lateAt late (pa.F.next + 2 * P.lay.lk + 2) = none) :
    ∃ pb, segAt? s' = some pb ∧ pb.L = pa.L ∧ Rides own pa pb ∧ Pass.More late pa pb s s' := by
  obtain ⟨a, a', pb, ha, ha', hpb, eF, eF', eL, est, ebk⟩ := seg_at_merge P h pa hpa
  obtain ⟨a₁, a₁', e1, e1', hl⟩ := decide_later h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hl' : Later pa.F pb.F := by
    rw [eF, eF']
    exact hl
  obtain ⟨a₂, a₂', _, G, _, _, wo, f1, f1', _, _, hwo, _, hm, _, _⟩ := decide_inv h
  obtain rfl : a₂' = a₁' := by
    rw [ha'] at f1'
    exact (Here.head.inj f1').symm
  obtain rfl : a₂ = a₁ := by
    rw [ha] at f1
    exact (Here.head.inj f1).symm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsF, _⟩ := mergeHear_inv hm
  have hmo : mergeOf s' = some (pa.F.next + 2 * P.lay.lk + 2) := by
    have e0 : mergeOf s' = a₂'.wo.map (·.sFv) := by
      unfold mergeOf
      rw [ha']
    rw [e0, hwo, Option.map_some, hsF, eF]
    congr 1
    omega
  have hsame : ∀ j, j ≠ pa.F.next + 2 * P.lay.lk + 2 → (Filled pb.F j ↔ Filled pa.F j) := by
    intro j hj
    rw [eF, eF']
    exact (merge_at P h ha ha' (by rw [← eF]; exact hS)) j (by rw [← eF]; exact hj)
  have hS' := hl'.sized hS
  refine ⟨pb, hpb, eL, rides_of_later own pa pb eL est ebk hl', hl'.ns,
    fun j hj => (hl'.keep j hj).1, ?_, ?_, Or.inr ⟨_, hmo, hfree, hlate⟩, ?_⟩
  · rw [hS.1, hS'.1, hl'.ns]
  · rw [hS.2.1, hS'.2.1, hl'.ns]
  · refine lateOk_of_later late pa pb hlo hl' fun x hx hg => ?_
    have hne := ne_of_lateAt_none late _ hlate x hx
    cases hb : pb.F.gotF.getD x.1 false with
    | false => rfl
    | true =>
      have := (hsame x.1 hne).1 hb
      rw [show pa.F.gotF.getD x.1 false = true from this] at hg
      cases hg

/-- **THE TEST "forms", WHERE A FORM MAY NAME WHAT IS AHEAD, ACROSS THE MERGE's ACCEPTING STEP, AT
ANY RUN.** -/
theorem formsInA_merge (Rd : Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (pa : K9.Part) (hpa : segAt? s = some pa)
    (hS : Sized pa.F) (hfree : pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false)
    (hf : Fwd Rd piece run s s')
    (hlate : ∀ R, Rd.forms piece run s = some R →
      lateAt R.late (pa.F.next + 2 * P.lay.lk + 2) = none)
    (hin : formsInA Rd sent own piece run s = true) :
    formsInA Rd sent own piece run s' = true := by
  unfold formsInA at hin ⊢
  cases hR : Rd.forms piece run s with
  | none =>
    rw [hpa, hR] at hin
    cases hin
  | some R =>
    rw [hpa, hR] at hin
    obtain ⟨hlo, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
    obtain ⟨pb, hpb, eL, hr, M⟩ := more_at_merge own P h pa hpa hS hfree R.late hlo (hlate R hR)
    rw [hpb, hf R hR]
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨M.late, List.all_eq_true.2 fun f hm =>
      affInA_more sent own eL hr M (List.all_eq_true.1 hall f hm)⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.entInA_rides
#print axioms VerifiableInference.Desc.First.MergeLaw.more_at_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.formsInA_merge
