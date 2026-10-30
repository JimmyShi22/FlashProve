-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/PublicAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING THE THREE TESTS ON PUBLIC NUMBERS `piecesLaid`,
`piecesFit`, `keyFitB` (Johnson/Desc/K8/Honest/PiecesLaid.lean, GoodOf.lean, PublicOfPieces.lean)
SAY YES, AND SO `digitsCover` (DigitsLiveOf.lean). Lemmas; none of the library's goals. No prover
stands in them; nothing on completeness, soundness or hiding.

"Reached": Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s) (Johnson/Top/H0/Walk/Reach.lean). The letters are
those of an opening of the description (IM.Open). The road is that of `units_at_batch`
(Johnson/P1K8R/UnitsAtBatch.lean, UnitsAtBatchAll.lean): the library's `planned_at_batch`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
  `piecesView`, `tests_view`, `planned_pieces`   what the three tests read of the data; it is
      `Planned`
  `tests_of_view`   from the six fields to the tests
  `public_layers`, `public_att`, `public_head`   at the three kinds of segments
  **`public_at_batch`**   in the goals' scope, at l < 25, at every (z, s) reached at 14 l + 9, or
      347 at the head's segment: s holds data tl at which the three tests say yes
  **`cover_at_batch`**   and `digitsCover tl`
By: `planned_at_batch` · IM.ground_named, IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean) ·
`public_tests` (PublicOfPieces.lean) · `cover_of_laid` (PiecesLaid.lean).
Limits. The full size's 25 segments. The first chain.

-/
import Johnson.P1K8R.UnitsAtBatchAll
import Johnson.Desc.K8.Honest.PublicOfPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Ready
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What the three tests read of the smallness test's data. -/
def piecesView (tl : HTailF2) := (tl.ix, tl.blocks, tl.z1, tl.z2, tl.mz, tl.f9)

/-- The three tests together. -/
def publicB (tl : HTailF2) : Bool := piecesLaid tl && piecesFit tl && keyFitB tl

theorem tests_view {a b : HTailF2} (h : piecesView a = piecesView b) : publicB a = publicB b := by
  simp only [piecesView, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold publicB piecesLaid piecesFit keyFitB joinPairs HTailF2.zzBlocks HTailF2.zOf
  rw [h1, h2, h3, h4, h5, h6]

theorem keeps4_pieces : Keeps4 piecesView := fun _ _ _ _ _ => rfl

/-- It reads planned fields alone. -/
theorem planned_pieces : LinkJoin.Planned piecesView :=
  ⟨keeps4_pieces, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

theorem publicB_of {tl : HTailF2}
    (h : piecesLaid tl = true ∧ piecesFit tl = true ∧ keyFitB tl = true) : publicB tl = true := by
  unfold publicB
  rw [h.1, h.2.1, h.2.2]
  rfl

/-- From the six fields to the tests. -/
theorem tests_of_view {s : S} {tlP : HTailF2}
    (hv : readTl piecesView s = some (piecesView tlP)) (hT : publicB tlP = true) :
    ∃ tl, s.tl? = some tl ∧ publicB tl = true := by
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    exact ⟨tl, rfl, by rw [tests_view (Option.some.inj hv)]; exact hT⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem public_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ publicB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, -, X', -, ehp, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_pieces hS hR O (x := (2 * g, 4, 2))
    (List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩) e3 (z, s) h
  rw [htl] at hv
  exact tests_of_view hv (publicB_of ((public_tests O.public).1 g hp ehp))

theorem public_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ publicB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_pieces hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  exact tests_of_view hv (publicB_of ((public_tests O.public).2.1 g q eq))

theorem public_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s)) :
    ∃ tl, s.tl? = some tl ∧ publicB tl = true := by
  obtain ⟨-, X, e3, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X', e3', htl, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_pieces hS hR O (x := (24, 5, 3))
    (List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩) e3 (z, s) h
  rw [htl] at hv
  exact tests_of_view hv (publicB_of (public_tests O.public).2.2)

/-- **At every state reached in front of a segment's batching the three tests say yes.** -/
theorem public_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ piecesLaid tl = true ∧ piecesFit tl = true ∧ keyFitB tl = true := by
  have key : ∃ tl, s.tl? = some tl ∧ publicB tl = true := by
    by_cases h24 : l = 24
    · subst h24
      exact public_head hS hR O h
    · rw [if_neg h24] at h
      obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
        ⟨l / 2, by omega, by omega⟩
      · exact public_layers hS hR O hg h
      · exact public_att hS hR O hg h
  obtain ⟨tl, hts, hb⟩ := key
  unfold publicB at hb
  simp only [Bool.and_eq_true] at hb
  exact ⟨tl, hts, hb.1.1, hb.1.2, hb.2⟩

/-- **And the test on all entries.** -/
theorem cover_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ digitsCover tl = true := by
  obtain ⟨tl, hts, h1, -, -⟩ := public_at_batch hS hR O hl h
  exact ⟨tl, hts, cover_of_laid tl h1⟩

end

end P1K8

#print axioms P1K8.planned_pieces
#print axioms P1K8.public_layers
#print axioms P1K8.public_att
#print axioms P1K8.public_head
#print axioms P1K8.public_at_batch
#print axioms P1K8.cover_at_batch
