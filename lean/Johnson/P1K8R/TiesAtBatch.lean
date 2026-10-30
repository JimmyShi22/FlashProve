-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/TiesAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS
REACH IN FRONT OF A SEGMENT's BATCHING THE SIZES FIT (`sizesB`, Johnson/P1K8R/MadeAtPlans.lean); SO
`tiesLaid` (Johnson/Desc/K8/Honest/LinkedFew.lean) SAYS YES THERE. Lemmas; none of the library's
goals. No prover stands in them; nothing on completeness, soundness or hiding.

"Reached": Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s) (Johnson/Top/H0/Walk/Reach.lean). The letters are
those of an opening of the description (IM.Open). The road is that of `apart_at_batch`
(Johnson/P1K8R/ApartAtBatch.lean): the library's `planned_at_batch`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
  `sizesView`, `sizes_view`, `planned_sizes`   what the test reads of the data; it is `Planned`
  `sizes_of_view`   from the four fields to the test
  `sizes_layers`, `sizes_att`, `sizes_head`   at the three kinds of segments
  **`sizes_at_batch`**   in the goals' scope, at l < 25, at every (z, s) reached at 14 l + 9, or 347
      at the head's segment: s holds data tl with `sizesB tl`
  `ties_of_three`   `apartB`, DgP.colsTest and `sizesB` give `tiesLaid`
  **`tiesLaid_at_batch`**   and `tiesLaid tl` there
By: `planned_at_batch` · IM.ground_named, IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean) ·
`public_made`, `made_sizes` (MadeAtPlans.lean) · `apart_at_batch` · `tiesLaid_of`, `colsFacts_of`
(Johnson/Desc/K8/Honest/TiesLaidOf.lean).
Limits. The full size's 25 segments. The first chain. Nothing on two matrices' arrays, on the
ledger's rows.

-/
import Johnson.P1K8R.ApartAtBatch
import Johnson.P1K8R.MadeAtPlans
import Johnson.Desc.K8.Honest.TiesLaidOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Ready
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What the test reads of the smallness test's data. -/
def sizesView (tl : HTailF2) := (tl.NM, tl.shp, tl.mats, tl.mz)

theorem sizes_view {a b : HTailF2} (h : sizesView a = sizesView b) : sizesB a = sizesB b := by
  simp only [sizesView, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold sizesB
  rw [h1, h2, h3, h4]

/-- It reads planned fields alone. -/
theorem planned_sizes : LinkJoin.Planned sizesView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- From the fields to the test. -/
theorem sizes_of_view {s : S} {tlP : HTailF2}
    (hv : readTl sizesView s = some (sizesView tlP)) (hT : sizesB tlP = true) :
    ∃ tl, s.tl? = some tl ∧ sizesB tl = true := by
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    exact ⟨tl, rfl, by rw [sizes_view (Option.some.inj hv)]; exact hT⟩

/-- The three light tests give `tiesLaid`. -/
theorem ties_of_three (tl : HTailF2) (hA : apartB tl = true) (hC : DgP.colsTest tl = true)
    (hS : sizesB tl = true) : tiesLaid tl = true := by
  unfold sizesB at hS
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hS
  obtain ⟨h1, h2⟩ := hS
  refine tiesLaid_of tl hA (colsFacts_of tl hC (fun mu hmu => (h1 mu hmu).2) fun h0 => ?_)
    fun mu hmu => (h1 mu hmu).1.1
  rcases h2 with h2 | h2
  · exact absurd h0 h2
  · exact h2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem sizes_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ sizesB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, -, X', -, ehp, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_sizes hS hR O (x := (2 * g, 4, 2))
    (List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩) e3 (z, s) h
  rw [htl] at hv
  exact sizes_of_view hv (made_sizes ((public_made O.public).1 g hp ehp))

theorem sizes_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ sizesB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_sizes hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  exact sizes_of_view hv (made_sizes ((public_made O.public).2.1 g q eq))

theorem sizes_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s)) :
    ∃ tl, s.tl? = some tl ∧ sizesB tl = true := by
  obtain ⟨-, X, e3, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X', e3', htl, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_sizes hS hR O (x := (24, 5, 3))
    (List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩) e3 (z, s) h
  rw [htl] at hv
  exact sizes_of_view hv (made_sizes (public_made O.public).2.2)

/-- **At every state reached in front of a segment's batching the sizes fit.** -/
theorem sizes_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ sizesB tl = true := by
  by_cases h24 : l = 24
  · subst h24
    exact sizes_head hS hR O h
  · rw [if_neg h24] at h
    obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
      ⟨l / 2, by omega, by omega⟩
    · exact sizes_layers hS hR O hg h
    · exact sizes_att hS hR O hg h

/-- **And `tiesLaid`.** -/
theorem tiesLaid_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ tiesLaid tl = true := by
  obtain ⟨tl, hts, h1, h2⟩ := apart_at_batch hS hR O hl h
  obtain ⟨tl', hts', h3⟩ := sizes_at_batch hS hR O hl h
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans hts')
  exact ⟨tl, hts, ties_of_three tl h1 h2 h3⟩

end

end P1K8

#print axioms P1K8.planned_sizes
#print axioms P1K8.ties_of_three
#print axioms P1K8.sizes_at_batch
#print axioms P1K8.tiesLaid_at_batch
