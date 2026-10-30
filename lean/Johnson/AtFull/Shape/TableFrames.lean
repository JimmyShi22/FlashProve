-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableFrames.lean: THE TABLE MEETS THE FRAMES, FIRST PART: the members at which
no test on values is laid. Under the head P5J.AtMgA. Nothing is evaluated.

  1 `cells_link`, `cells_head`, `cells_back`: the table read at a number. **`Both cF Z G n`**:
    for every ft: the frame's two premises, Carries and Returns (another house's
    Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the member's number n, AT THE TABLE's OWN
    LETTERS firstZA (Tab.g Z G) (Tab.vals Z G). `sub_odd`, `draw_no`, `base_one`.
  2 `tab_front`, `tab_laid`, `tab_shut`, `tab_shut_head`, `tab_seal`, `tab_batt`, `tab_merge`,
    `tab_draw`, `tab_draw_head`, `tab_cleared_att`, `tab_cleared_lay`, `tab_cleared_head`: Both at
    these members' numbers, written as numerals in the link's number: each from its seat's frame,
    whose equation on g the table meets.

Limits. As the frames': two premises of the rule for acceptance; no state is shown at which a step
returns. `Both` DOES NOT SAY THAT A MEMBER STANDS AT THE NUMBER: the frames' first clause is dropped
here; where none stands it holds emptily (that the list has 358 members: flat_len, Numbers.lean).
cells_back has no bound on j: from the fifth place on it is the seal's cell. At the format's second
hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableOfSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)
open ProofFile.Honest (Carries Returns)

/-! ## 1 Reading the table at a number -/

section
variable (Z : ProofFile.Pub) (G : ProofFile.Ground)

theorem cells_link {n : Nat} (l j : Nat) (hl : l < 24) (hj : j < 14) (hn : n = 14 * l + j + 1) :
    Tab.cells Z G n = (Tab.linkRow Z G l).at j := by
  subst hn
  exact table_link _ _ _ _ l j hl hj

theorem cells_head {n : Nat} (j : Nat) (hj : j < 16) (hn : n = 337 + j) :
    Tab.cells Z G n = (Tab.headRow Z G).at j := by
  subst hn
  exact table_head _ _ _ _ j hj

theorem cells_back {n : Nat} (j : Nat) (hn : n = 353 + j) :
    Tab.cells Z G n = (Tab.backRow Z G).at j := by
  subst hn
  exact table_back _ _ _ _ j

end

/-- The frame's two premises at a member's number, at the table's own steps and tests. -/
def Both (cF : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (G : ProofFile.Ground) (n : Nat) : Prop :=
  ∀ ft : Nat, Carries cF.blocksInOrder ft (firstZA (Tab.g Z G) (Tab.vals Z G)) n ∧
    Returns cF.blocksInOrder ft (firstZA (Tab.g Z G) (Tab.vals Z G)) n

theorem sub_odd (k : Nat) : subAt (2 * k + 1) = .attention := by
  unfold subAt
  rw [if_neg (by omega), if_neg (by omega)]

theorem draw_no {l : Nat} (hl : l < 24) : drawNo (subAt l) = 4 := by
  unfold subAt
  rw [if_neg (by omega)]
  split <;> rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

theorem base_one {A B : ProofFile.PureBase}
    (h1 : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok A)
    (h2 : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok B) : A = B := by
  rw [h1] at h2
  exact Except.ok.inj h2

/-! ## 2 The members without a test on values -/

theorem tab_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 0 := fun ft => front_frame h ft _ _ rfl

theorem tab_laid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    (l : Nat) (hl : l < 25) : Both cF Zp G (14 * l + 1) := fun ft => by
  refine laid_frame h l hl ft _ _ ?_
  unfold Tab.g
  by_cases h24 : l = 24
  · subst h24
    rw [cells_head Zp G 0 (by omega) rfl]
    rfl
  · rw [cells_link Zp G l 0 (by omega) (by omega) rfl]
    rfl

theorem tab_shut (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    (l : Nat) (hl : l < 24) : Both cF Zp G (14 * l + 13) := fun ft => by
  obtain ⟨L, hL, hf⟩ := shut_frame h l (by omega)
  rw [(numbers_at h hl hL).2.2.2.2.1] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_link Zp G l 12 hl (by omega) rfl]
  rfl

theorem tab_shut_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 351 := fun ft => by
  obtain ⟨L, hL, hf⟩ := shut_frame h 24 (by omega)
  rw [(numbers_head h hL).2.2.2.2.2.1] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_head Zp G 14 (by omega) rfl]
  rfl

theorem tab_seal (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 357 := fun ft => by
  refine (seal_frame h).2 ft _ _ ?_
  unfold Tab.g
  rw [cells_back Zp G 4 rfl]
  rfl

theorem tab_batt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 355 := fun ft => by
  refine (batt_frame h).2 ft _ _ ?_
  unfold Tab.g
  rw [cells_back Zp G 2 rfl]
  rfl

theorem tab_merge (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 346 := fun ft => by
  obtain ⟨B', e1, -, hf⟩ := merge_frame h
  obtain rfl := base_one hB e1
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_head Zp Bs.G₀ 9 (by omega) rfl]
  rfl

theorem tab_draw (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (l : Nat)
    (hl : l < 24) : Both cF Zp Bs.G₀ (14 * l + 6) := fun ft => by
  obtain ⟨B', Xl, e1, e2, -, hf⟩ := draw_frame h l (by omega)
  obtain rfl := base_one hB e1
  rw [draw_no hl] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_link Zp Bs.G₀ l 5 hl (by omega) rfl]
  show (Tab.draw Zp Bs.G₀ l).1 = _
  unfold Tab.draw
  rw [e2]

theorem tab_draw_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 343 := fun ft => by
  obtain ⟨B', Xl, e1, e2, -, hf⟩ := draw_frame h 24 (by omega)
  obtain rfl := base_one hB e1
  rw [show 14 * 24 + drawNo (subAt 24) + 2 = 343 from rfl] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_head Zp Bs.G₀ 6 (by omega) rfl]
  show (Tab.draw Zp Bs.G₀ 24).1 = _
  unfold Tab.draw
  rw [e2]

theorem tab_cleared_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    (k : Nat) (hk : k < 12) : Both cF Zp G (14 * (2 * k + 1) + 14) := fun ft => by
  obtain ⟨Y, p, L, e1, e2, hL, hf⟩ := cleared_att_frame h (2 * k + 1) (by omega) (sub_odd k)
  rw [(numbers_at h (by omega) hL).2.2.2.2.2] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_link Zp G (2 * k + 1) 13 (by omega) (by omega) rfl]
  show (Tab.cleared Zp (2 * k + 1)).1 = _
  unfold Tab.cleared
  rw [e1]
  simp only [e2, show (2 * k + 1 == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * k + 1) % 2 == 1) = true from beq_iff_eq.2 (by omega), Bool.false_eq_true, if_false,
    if_true]

theorem tab_cleared_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    (k : Nat) (hk : k < 12) : Both cF Zp G (14 * (2 * k) + 14) := fun ft => by
  obtain ⟨Y, hp, L, e1, e2, hL, hf⟩ := cleared_lay_frame h (2 * k) (by omega) (sub_even k hk)
  rw [(numbers_at h (by omega) hL).2.2.2.2.2] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_link Zp G (2 * k) 13 (by omega) (by omega) rfl]
  show (Tab.cleared Zp (2 * k)).1 = _
  unfold Tab.cleared
  rw [e1]
  simp only [e2, show (2 * k == 24) = false from beq_eq_false_iff_ne.2 (by omega),
    show ((2 * k) % 2 == 1) = false from beq_eq_false_iff_ne.2 (by omega), Bool.false_eq_true,
    if_false]

theorem tab_cleared_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    : Both cF Zp G 352 := fun ft => by
  obtain ⟨Y, L, e1, hL, hf⟩ := cleared_head_frame h 24 (by omega) rfl
  rw [(numbers_head h hL).2.2.2.2.2.2] at hf
  refine hf ft _ _ ?_
  unfold Tab.g
  rw [cells_head Zp G 15 (by omega) rfl]
  show (Tab.cleared Zp 24).1 = _
  unfold Tab.cleared
  rw [e1]
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tab_merge
#print axioms Johnson.AtFull.Shape.tab_draw
#print axioms Johnson.AtFull.Shape.tab_draw_head
#print axioms Johnson.AtFull.Shape.tab_cleared_att
#print axioms Johnson.AtFull.Shape.tab_cleared_lay
#print axioms Johnson.AtFull.Shape.tab_cleared_head
#print axioms Johnson.AtFull.Shape.tab_front
#print axioms Johnson.AtFull.Shape.tab_laid
#print axioms Johnson.AtFull.Shape.tab_shut
#print axioms Johnson.AtFull.Shape.tab_shut_head
#print axioms Johnson.AtFull.Shape.tab_seal
#print axioms Johnson.AtFull.Shape.tab_batt
#print axioms Johnson.AtFull.Shape.cells_link
#print axioms Johnson.AtFull.Shape.cells_head
#print axioms Johnson.AtFull.Shape.cells_back
#print axioms Johnson.AtFull.Shape.sub_odd
#print axioms Johnson.AtFull.Shape.draw_no
#print axioms Johnson.AtFull.Shape.base_one
#print axioms Johnson.AtFull.Shape.Both
