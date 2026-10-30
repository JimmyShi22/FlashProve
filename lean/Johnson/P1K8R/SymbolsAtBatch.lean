-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/SymbolsAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING NO TWO MATRICES HAVE ONE ARRAY (`oneEachB`,
Johnson/P1K8R/ArraysApart.lean); SO `symbolsLaid` (Johnson/Desc/K8/Honest/SymbolsFew.lean) SAYS YES
THERE. Lemmas; none of the library's goals. No prover stands in them; nothing on completeness,
soundness or hiding.

"Reached": Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s) (Johnson/Top/H0/Walk/Reach.lean). The letters are
those of an opening of the description (IM.Open). The road is that of `sizes_at_batch`
(Johnson/P1K8R/TiesAtBatch.lean): the library's `planned_at_batch`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
  `eachView`, `each_view`, `planned_each`   what the test reads of the data; it is `Planned`
  `each_of_view`   from the two fields to the test
  `each_layers`, `each_att`, `each_head`   at the three kinds of segments
  **`oneEach_at_batch`**   in the goals' scope, at l < 25, at every (z, s) reached at 14 l + 9, or
      347 at the head's segment: s holds data tl with `oneEachB tl`
  `symbols_of_three`   `apartB`, `sizesB` and `oneEachB` give `symbolsLaid`
  **`symbolsLaid_at_batch`**   and `symbolsLaid tl` there
By: `planned_at_batch` · IM.ground_named, IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean) ·
`public_made` (MadeAtPlans.lean) · `made_oneEach` · `apart_at_batch` (ApartAtBatch.lean) ·
`sizes_at_batch`.
Limits. The full size's 25 segments. The first chain. Nothing on the ledger's rows.

-/
import Johnson.P1K8R.TiesAtBatch
import Johnson.P1K8R.ArraysApart
import Johnson.Desc.K8.Honest.SymbolsFew

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
def eachView (tl : HTailF2) := (tl.NM, tl.gtTree)

theorem each_view {a b : HTailF2} (h : eachView a = eachView b) : oneEachB a = oneEachB b := by
  simp only [eachView, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  unfold oneEachB
  rw [h1, h2]

/-- It reads planned fields alone. -/
theorem planned_each : LinkJoin.Planned eachView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

/-- From the fields to the test. -/
theorem each_of_view {s : S} {tlP : HTailF2}
    (hv : readTl eachView s = some (eachView tlP)) (hT : oneEachB tlP = true) :
    ∃ tl, s.tl? = some tl ∧ oneEachB tl = true := by
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    exact ⟨tl, rfl, by rw [each_view (Option.some.inj hv)]; exact hT⟩

/-- The three light tests give `symbolsLaid`. -/
theorem symbols_of_three (tl : HTailF2) (hA : apartB tl = true) (hS : sizesB tl = true)
    (hN : oneEachB tl = true) : symbolsLaid tl = true := by
  obtain ⟨-, -, -, a4⟩ := (apartB_iff tl).1 hA
  unfold sizesB at hS
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hS
  unfold oneEachB at hN
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, List.all_eq_true, List.mem_range] at hN
  unfold symbolsLaid
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, List.all_eq_true,
    List.mem_range]
  exact fun mu hmu => ⟨⟨⟨⟨Ne.symm (a4 mu hmu).2.1, (a4 mu hmu).2.2.1⟩, (a4 mu hmu).2.2.2⟩,
    (hS.1 mu hmu).1.2⟩, hN mu hmu⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem each_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ oneEachB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, -, X', -, ehp, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_each hS hR O (x := (2 * g, 4, 2))
    (List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩) e3 (z, s) h
  rw [htl] at hv
  exact each_of_view hv (made_oneEach ((public_made O.public).1 g hp ehp))

theorem each_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ oneEachB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_each hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  exact each_of_view hv (made_oneEach ((public_made O.public).2.1 g q eq))

theorem each_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s)) :
    ∃ tl, s.tl? = some tl ∧ oneEachB tl = true := by
  obtain ⟨-, X, e3, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X', e3', htl, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_each hS hR O (x := (24, 5, 3))
    (List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩) e3 (z, s) h
  rw [htl] at hv
  exact each_of_view hv (made_oneEach (public_made O.public).2.2)

/-- **At every state reached in front of a segment's batching no two matrices have one array.** -/
theorem oneEach_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ oneEachB tl = true := by
  by_cases h24 : l = 24
  · subst h24
    exact each_head hS hR O h
  · rw [if_neg h24] at h
    obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
      ⟨l / 2, by omega, by omega⟩
    · exact each_layers hS hR O hg h
    · exact each_att hS hR O hg h

/-- **And `symbolsLaid`.** -/
theorem symbolsLaid_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ symbolsLaid tl = true := by
  obtain ⟨tl, hts, h1, -⟩ := apart_at_batch hS hR O hl h
  obtain ⟨tl', hts', h2⟩ := sizes_at_batch hS hR O hl h
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans hts')
  obtain ⟨tl', hts', h3⟩ := oneEach_at_batch hS hR O hl h
  obtain rfl : tl = tl' := Option.some.inj (hts.symm.trans hts')
  exact ⟨tl, hts, symbols_of_three tl h1 h2 h3⟩

end

end P1K8

#print axioms P1K8.planned_each
#print axioms P1K8.symbols_of_three
#print axioms P1K8.oneEach_at_batch
#print axioms P1K8.symbolsLaid_at_batch
