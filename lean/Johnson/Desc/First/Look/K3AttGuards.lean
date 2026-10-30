-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AttGuards.lean: THE CALLS' END THEOREM AT AN ATTENTION LINK, HELD CLAUSE
BY CLAUSE AGAINST ONE QUESTION: over what does each "for all" in its relations range, and what makes
the closed caller's READING there a reading of something committed, and not a silent 0?
Definitions with code, statements and proofs. NO SOUNDNESS IS CLAIMED.

THE FIND. The row out's second item (planes-at-points, K3Planes) reads the cells (row, col) of the
planes' matrix through the caller's entry enCell x.ns tl (A.cf.NAs + 2) row col. That entry is a
cell only where matrix number NAs + 2 of the smallness test's list is there and has that row and
column (cellJ); elsewhere it is the entry that reads 0. NEITHER AttOK NOR AttReadsOK
(Johnson/Desc/First/Look/K3CallerAtt.lean) ASKS THAT THE PLANES' CELLS LIE IN THAT MATRIX: cellsIn
speaks of the segment's named cells alone. Where they did not lie in it, AttBehind would ask the
later blocks for claims on a matrix of zeros, which claims on the committed matrix do not pay.

Main names:
  `planesInB x A tl`: the test on public data: the list has matrix NAs + 2; it has 2 ^ x.lm rows or
    more, and NC * 2 ^ (kT + 5 - lm) columns or more (the program's own count, Forest.planeCols).
  `planes_in`: under it every (row, col) below these two numbers has a cell.
  `cellRC_in`: the cell (t, k, j) of the counts' bits, t < 2 ^ kT, k < NC, j < 32, lies in a row and
    a column below these two numbers (FoNums.cellRC; arithmetic).
  `bc_in`: so every entry that the caller's layout names for a bit of a count is a cell.
  `attNu_cell`, `attNu_cell_out`: what the reading of the places is at a cell: the caller's msg₀ at
    that entry; AND 0 WHERE THE MATRIX HAS NO SUCH CELL: the hazard, as a theorem.
  `attNu_mask`: at a mask entry below x.ns: the mask row's entry off the messages (AttOK.masksIn
    puts the lookup's own mask entries there).

Limits. That matrix NAs + 2 IS the planes' matrix of the programs is the caller's word (its Limits
(1)). Nothing on who pays AttBehind.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AttGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **The planes' cells lie in the list's matrix**: a test on public data. -/
def planesInB (x : Place) (A : Attention.Shape) (tl : HTailF2) : Bool :=
  decide (A.cf.NAs + 2 < (szOf tl).NM) && decide (2 ^ x.lm ≤ (szOf tl).m (A.cf.NAs + 2)) &&
    decide (x.fs.NC * 2 ^ (x.fs.kT + 5 - x.lm) ≤ (szOf tl).k (A.cf.NAs + 2))

/-- Under the test every (row, col) below the two numbers has a cell. -/
theorem planes_in {x : Place} {A : Attention.Shape} {tl : HTailF2} (e : planesInB x A tl = true)
    (row col : ℕ) (hr : row < 2 ^ x.lm) (hc : col < x.fs.NC * 2 ^ (x.fs.kT + 5 - x.lm)) :
    (cellJ (szOf tl) (A.cf.NAs + 2) row col).isSome = true := by
  unfold planesInB at e
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    decide_eq_true_eq] at e
  obtain ⟨⟨h1, h2⟩, h3⟩ := e
  unfold cellJ
  rw [dif_pos ⟨h1, Nat.lt_of_lt_of_le hc h3, Nat.lt_of_lt_of_le hr h2⟩]
  rfl

/-- The cell of bit j of the count of row t of call k's table lies below the two numbers. -/
theorem cellRC_in (h : FoNums.Sh) (lm : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (t k j : ℕ)
    (ht : t < 2 ^ h.kT) (hk : k < h.NC) (hj : j < 32) :
    (FoNums.cellRC h lm (t, k, j)).1 < 2 ^ lm ∧
      (FoNums.cellRC h lm (t, k, j)).2 < h.NC * 2 ^ (h.kT + 5 - lm) := by
  show (t % 2 ^ (lm - 5)) * 32 + j < 2 ^ lm ∧
    k * 2 ^ (h.kT + 5 - lm) + t / 2 ^ (lm - 5) < h.NC * 2 ^ (h.kT + 5 - lm)
  have e1 : 2 ^ (lm - 5) * 32 = 2 ^ lm := by
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_add]
    congr 1
    omega
  have e2 : 2 ^ (lm - 5) * 2 ^ (h.kT + 5 - lm) = 2 ^ h.kT := by
    rw [← pow_add]
    congr 1
    omega
  have ha : 0 < 2 ^ (lm - 5) := Nat.two_pow_pos _
  constructor
  · have hm := Nat.mod_lt t ha
    rw [← e1]
    omega
  · have hq : t / 2 ^ (lm - 5) < 2 ^ (h.kT + 5 - lm) :=
      Nat.div_lt_of_lt_mul (by rw [e2]; exact ht)
    have h1 : (k + 1) * 2 ^ (h.kT + 5 - lm) ≤ h.NC * 2 ^ (h.kT + 5 - lm) :=
      Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at h1
    omega

/-- **Every entry that the caller's layout names for a bit of a count is a cell.** -/
theorem bc_in {set : Params.Setting} {x : Place} {A : Attention.Shape} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} (H : AttOK set x A tl D rad) (e : planesInB x A tl = true)
    (t k j : ℕ) (ht : t < 2 ^ x.fs.kT) (hk : k < x.fs.NC) (hj : j < 32) :
    ((attLay A x.fs x.lm x.F.next x.ns tl).bc t k j).isSome = true := by
  obtain ⟨h1, h2⟩ := cellRC_in x.fs x.lm (att_lm H).1 (att_lm H).2 t k j ht hk hj
  have h3 := planes_in e _ _ h1 h2
  show (enCell x.ns tl (A.cf.NAs + 2) (FoNums.cellRC x.fs x.lm (t, k, j)).1
    (FoNums.cellRC x.fs x.lm (t, k, j)).2).isSome = true
  unfold enCell
  rw [Option.isSome_map]
  exact h3

end VerifiableInference.Desc.First.Look

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {Cells Tok : Type} (x : Desc.First.Look.Place) (A : Attention.Shape) (tl : HTailF2)
  (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

/-- The reading of the places at a cell of the planes' matrix. -/
theorem attNu_cell (w : Desc.Wit Cells Tok MsgT) (r c : ℕ) :
    attNu x A tl D rad seatT arr w (.cell r c) =
      attMu x tl D rad seatT arr w (enCell x.ns tl (A.cf.NAs + 2) r c) := rfl

/-- **THE HAZARD**: where the list's matrix has no such cell the reading is 0, whatever the
messages hold. -/
theorem attNu_cell_out (w : Desc.Wit Cells Tok MsgT) (r c : ℕ)
    (h : cellJ (szOf tl) (A.cf.NAs + 2) r c = none) :
    attNu x A tl D rad seatT arr w (.cell r c) = 0 := by
  rw [attNu_cell]
  unfold enCell
  rw [h]
  rfl

/-- The reading of the places at a mask entry of the mask row. -/
theorem attNu_mask (w : Desc.Wit Cells Tok MsgT) (j : ℕ) (hj : j < x.ns) :
    attNu x A tl D rad seatT arr w (.mask j) =
      (valAt D.codes (sigListCalls D rad x.link) (Desc.First.Look.seatCalls D x.link)
        (attMs x D rad seatT arr w) (.mask j)).getD 0 := by
  show attMu x tl D rad seatT arr w (enMask x.ns tl j) = _
  unfold enMask
  rw [finOf_some hj]
  rfl

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.Desc.First.Look.planes_in
#print axioms VerifiableInference.Desc.First.Look.cellRC_in
#print axioms VerifiableInference.Desc.First.Look.bc_in
#print axioms VerifiableInference.OnPublicFiles.attNu_cell_out
#print axioms VerifiableInference.OnPublicFiles.attNu_mask
