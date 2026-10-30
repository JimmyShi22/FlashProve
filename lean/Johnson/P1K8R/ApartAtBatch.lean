-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ApartAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING THE ARRAYS' NUMBERS ARE APART (`apartB`,
Johnson/Desc/K8/Honest/ApartOf.lean) AND THE MATRICES' COLUMNS LIE ONE BEHIND THE OTHER
(DgP.colsTest, OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean); SO `planesLaid`
(Johnson/Desc/K8/Honest/PlanesFew.lean) SAYS YES THERE. Lemmas; none of the library's goals. No
prover stands in them; nothing on completeness, soundness or hiding.

"Reached": Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s) (Johnson/Top/H0/Walk/Reach.lean). The letters are
those of an opening of the description (IM.Open). The road is that of `public_at_batch`
(Johnson/P1K8R/PublicAtBatch.lean): the library's `planned_at_batch`
(Johnson/Desc/First/Link/Law/PlannedAtDraw.lean).
  `laysView`, `lays_view`, `planned_lays`   what the two tests read of the data; it is `Planned`
  `laysB`, `lays_of_view`   the two tests together; from the six fields to the tests
  `lays_layers`, `lays_att`, `lays_head`   at the three kinds of segments
  **`apart_at_batch`**   in the goals' scope, at l < 25, at every (z, s) reached at 14 l + 9, or 347
      at the head's segment: s holds data tl at which both tests say yes
  **`planesLaid_at_batch`**   and `planesLaid tl`
By: `planned_at_batch` · IM.ground_named, IM.ground_tails (Johnson/IMR/PureJoin.lean, K8Seat.lean) ·
`public_apart` (ApartOf.lean) · Fo.ZPlan.public_cols (Johnson/Desc/First/Look/ColsAt.lean).
Limits. The full size's 25 segments. The first chain. Nothing on the shapes, on the matrices' sizes,
on two matrices' arrays, on the ledger's rows.

-/
import Johnson.P1K8R.UnitsAtBatchAll
import Johnson.Desc.K8.Honest.ApartOf
import Johnson.Desc.First.Look.ColsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8 VerifiableInference.Desc.First.K8.Ready
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What the two tests read of the smallness test's data. -/
def laysView (tl : HTailF2) := (tl.ix, tl.NM, tl.gtTree, tl.off, tl.mz, tl.mats)

/-- The two tests together. -/
def laysB (tl : HTailF2) : Bool := apartB tl && DgP.colsTest tl

theorem lays_view {a b : HTailF2} (h : laysView a = laysView b) : laysB a = laysB b := by
  simp only [laysView, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold laysB apartB DgP.colsTest DgP.offOf DgP.mOf
  rw [h1, h2, h3, h4, h5, h6]

/-- It reads planned fields alone. -/
theorem planned_lays : LinkJoin.Planned laysView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

theorem laysB_of {tl : HTailF2} (h1 : apartB tl = true) (h2 : DgP.colsTest tl = true) :
    laysB tl = true := by
  unfold laysB
  rw [h1, h2]
  rfl

/-- From the fields to the tests. -/
theorem lays_of_view {s : S} {tlP : HTailF2}
    (hv : readTl laysView s = some (laysView tlP)) (hT : laysB tlP = true) :
    ∃ tl, s.tl? = some tl ∧ laysB tl = true := by
  unfold readTl at hv
  cases hts : s.tl? with
  | none =>
    rw [hts] at hv
    exact absurd hv (by simp)
  | some tl =>
    rw [hts] at hv
    exact ⟨tl, rfl, by rw [lays_view (Option.some.inj hv)]; exact hT⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem lays_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ laysB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨hp, -, X', -, ehp, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_lays hS hR O (x := (2 * g, 4, 2))
    (List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩) e3 (z, s) h
  rw [htl] at hv
  exact lays_of_view hv (laysB_of ((public_apart O.public).1 g hp ehp)
    ((Fo.ZPlan.public_cols O.public).1 g hp ehp))

theorem lays_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ laysB tl = true := by
  obtain ⟨hN, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X, -, -, -, -, e3, -⟩ := hN g hg
  obtain ⟨hT, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain ⟨-, q, -, X', -, eq, -, -, -, -, -, -, e3', htl, -⟩ := hT g hg
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_lays hS hR O (x := (2 * g + 1, 4, 2))
    (List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩)
    e3 (z, s) h
  rw [htl] at hv
  exact lays_of_view hv (laysB_of ((public_apart O.public).2.1 g q eq)
    ((Fo.ZPlan.public_cols O.public).2.1 g q eq))

theorem lays_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s)) :
    ∃ tl, s.tl? = some tl ∧ laysB tl = true := by
  obtain ⟨-, X, e3, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨-, X', e3', htl, -⟩ := IM.ground_tails hS hR O.pub O.blank
  obtain rfl : X = X' := Option.some.inj (e3.symm.trans e3')
  have hv := LinkJoin.planned_at_batch planned_lays hS hR O (x := (24, 5, 3))
    (List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩) e3 (z, s) h
  rw [htl] at hv
  exact lays_of_view hv (laysB_of (public_apart O.public).2.2
    (Fo.ZPlan.public_cols O.public).2.2)

/-- **At every state reached in front of a segment's batching both tests say yes.** -/
theorem apart_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ apartB tl = true ∧ DgP.colsTest tl = true := by
  have key : ∃ tl, s.tl? = some tl ∧ laysB tl = true := by
    by_cases h24 : l = 24
    · subst h24
      exact lays_head hS hR O h
    · rw [if_neg h24] at h
      obtain ⟨g, hg, rfl | rfl⟩ : ∃ g, g < 12 ∧ (l = 2 * g ∨ l = 2 * g + 1) :=
        ⟨l / 2, by omega, by omega⟩
      · exact lays_layers hS hR O hg h
      · exact lays_att hS hR O hg h
  obtain ⟨tl, hts, hb⟩ := key
  unfold laysB at hb
  rw [Bool.and_eq_true] at hb
  exact ⟨tl, hts, hb.1, hb.2⟩

/-- **And `planesLaid`.** -/
theorem planesLaid_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ planesLaid tl = true := by
  obtain ⟨tl, hts, h1, -⟩ := apart_at_batch hS hR O hl h
  exact ⟨tl, hts, planesLaid_of_apart tl h1⟩

end

end P1K8

#print axioms P1K8.planned_lays
#print axioms P1K8.lays_layers
#print axioms P1K8.lays_att
#print axioms P1K8.lays_head
#print axioms P1K8.apart_at_batch
#print axioms P1K8.planesLaid_at_batch
