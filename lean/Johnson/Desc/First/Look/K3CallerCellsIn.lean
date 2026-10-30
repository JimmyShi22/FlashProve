-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerCellsIn.lean: what guards a closed caller's reading of the lookup's
own places (the cells of the planes' matrix; the lookup's mask entries) against a silent 0: one
test, general in the matrix's number, for the calls of all three sorts of link; and its use at an
attention link. Definitions with code, statements and proofs. NO SOUNDNESS IS CLAIMED.

Why. A closed caller's layout names, for bit j of the count of row t of call k's table, the entry
of the cell (iB, row, col), and for the lookup's mask entry s the entry of mask entry first + s.
Such an entry is a cell (a mask entry) only where the list's matrix number iB is there and has
that row and column (where first + s lies below the mask row's length); ELSEWHERE IT IS THE ENTRY
«none», WHICH THE CALLER's msg₀ READS AS 0, whatever the messages hold. AttOK and AttReadsOK
(Johnson/Desc/First/Look/K3CallerAtt.lean) do not ask that the planes' cells lie in that matrix:
cellsIn speaks of the segment's named cells alone. Where they did not lie in it, what the block
leaves behind would be claims on a matrix of zeros, which claims on the committed matrix do not
pay.

Main names:
  `cellRC_below`: the cell (t, k, j), t < 2 ^ kT, k < NC, j < 32, lies in a row below 2 ^ lm and a
    column below NC * 2 ^ (kT + 5 - lm) (arithmetic on FoNums.cellRC).
  `planesAtB tl fs lm iB`: the test on public data: 5 ≤ lm ≤ kT + 5; the list has matrix iB; it has
    2 ^ lm rows or more and NC * 2 ^ (kT + 5 - lm) columns or more. `planesAtB_iff`: just that.
  `planesAt_in`, `planesAt_bc`: under it every (row, col) below the two numbers, so every cell of a
    count's bit, has a cell of the list.
  `masksAtB fs first ns`, `masksAt_in`: the like for the lookup's mask entries.
  `att_bc_cell | att_mk_cell` (iB := NAs + 2): so what attention's layout names are cells and mask
    entries, none of them the entry «none».

Limits. That matrix iB IS the planes' matrix of the programs is the caller's word. The tests are
evaluated nowhere in this file. Nothing here on the cells that the KEYS read (AttReadsOK.cellsIn).
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The cell of bit j of the count of row t of call k's table lies below the two numbers. -/
theorem cellRC_below (h : FoNums.Sh) (lm : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (t k j : ℕ)
    (ht : t < 2 ^ h.kT) (hk : k < h.NC) (hj : j < 32) :
    (FoNums.cellRC h lm (t, k, j)).1 < 2 ^ lm ∧
      (FoNums.cellRC h lm (t, k, j)).2 < h.NC * 2 ^ (h.kT + 5 - lm) := by
  show (t % 2 ^ (lm - 5)) * 32 + j < 2 ^ lm ∧
    k * 2 ^ (h.kT + 5 - lm) + t / 2 ^ (lm - 5) < h.NC * 2 ^ (h.kT + 5 - lm)
  have e1 : 2 ^ (lm - 5) * 32 = 2 ^ lm := by
    have h0 : lm - 5 + 5 = lm := by omega
    calc 2 ^ (lm - 5) * 32 = 2 ^ (lm - 5) * 2 ^ 5 := by norm_num
      _ = 2 ^ (lm - 5 + 5) := (pow_add (2 : ℕ) (lm - 5) 5).symm
      _ = 2 ^ lm := by rw [h0]
  have e2 : 2 ^ (lm - 5) * 2 ^ (h.kT + 5 - lm) = 2 ^ h.kT := by
    have h0 : lm - 5 + (h.kT + 5 - lm) = h.kT := by omega
    calc 2 ^ (lm - 5) * 2 ^ (h.kT + 5 - lm) = 2 ^ (lm - 5 + (h.kT + 5 - lm)) :=
          (pow_add (2 : ℕ) (lm - 5) (h.kT + 5 - lm)).symm
      _ = 2 ^ h.kT := by rw [h0]
  have ha : 0 < 2 ^ (lm - 5) := Nat.two_pow_pos _
  constructor
  · have hm : t % 2 ^ (lm - 5) < 2 ^ (lm - 5) := Nat.mod_lt t ha
    rw [← e1]
    omega
  · have hq : t / 2 ^ (lm - 5) < 2 ^ (h.kT + 5 - lm) :=
      Nat.div_lt_of_lt_mul (by rw [e2]; exact ht)
    have h1 : (k + 1) * 2 ^ (h.kT + 5 - lm) ≤ h.NC * 2 ^ (h.kT + 5 - lm) :=
      Nat.mul_le_mul_right _ hk
    have h2 : (k + 1) * 2 ^ (h.kT + 5 - lm) =
        k * 2 ^ (h.kT + 5 - lm) + 2 ^ (h.kT + 5 - lm) := by ring
    omega

/-- **The planes' cells lie in the list's matrix number iB**: a test on public data. -/
def planesAtB (tl : HTailF2) (fs : Forest.Shape) (lm iB : ℕ) : Bool :=
  decide (5 ≤ lm) && decide (lm ≤ fs.kT + 5) && decide (iB < (szOf tl).NM) &&
    decide (2 ^ lm ≤ (szOf tl).m iB) && decide (fs.NC * 2 ^ (fs.kT + 5 - lm) ≤ (szOf tl).k iB)

theorem planesAtB_iff {tl : HTailF2} {fs : Forest.Shape} {lm iB : ℕ} :
    planesAtB tl fs lm iB = true ↔
      5 ≤ lm ∧ lm ≤ fs.kT + 5 ∧ iB < (szOf tl).NM ∧ 2 ^ lm ≤ (szOf tl).m iB ∧
        fs.NC * 2 ^ (fs.kT + 5 - lm) ≤ (szOf tl).k iB := by
  unfold planesAtB
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Under the test every (row, col) below the two numbers has a cell. -/
theorem planesAt_in {tl : HTailF2} {fs : Forest.Shape} {lm iB : ℕ}
    (e : planesAtB tl fs lm iB = true) (row col : ℕ) (hr : row < 2 ^ lm)
    (hc : col < fs.NC * 2 ^ (fs.kT + 5 - lm)) : (cellJ (szOf tl) iB row col).isSome = true := by
  obtain ⟨_, _, h1, h2, h3⟩ := planesAtB_iff.1 e
  unfold cellJ
  rw [dif_pos ⟨h1, Nat.lt_of_lt_of_le hc h3, Nat.lt_of_lt_of_le hr h2⟩]
  rfl

/-- **So every cell of a count's bit has a cell of the list.** -/
theorem planesAt_bc {tl : HTailF2} {fs : Forest.Shape} {lm iB : ℕ}
    (e : planesAtB tl fs lm iB = true) (t k j : ℕ) (ht : t < 2 ^ fs.kT) (hk : k < fs.NC)
    (hj : j < 32) :
    (cellJ (szOf tl) iB (FoNums.cellRC fs lm (t, k, j)).1
      (FoNums.cellRC fs lm (t, k, j)).2).isSome = true := by
  obtain ⟨h5, hlm, _⟩ := planesAtB_iff.1 e
  obtain ⟨h1, h2⟩ := cellRC_below fs lm h5 hlm t k j ht hk hj
  exact planesAt_in e _ _ h1 h2

/-- **The lookup's mask entries are entries of the mask row**: a test on public data. -/
def masksAtB (fs : Forest.Shape) (first ns : ℕ) : Bool := decide (first + FoNums.nMasks fs ≤ ns)

theorem masksAt_in {fs : Forest.Shape} {first ns : ℕ} (e : masksAtB fs first ns = true) (s : ℕ)
    (hs : s < FoNums.nMasks fs) : (finOf ns (first + s)).isSome = true := by
  unfold masksAtB at e
  rw [decide_eq_true_eq] at e
  rw [finOf_some (show first + s < ns by omega)]
  rfl

/-! ### attention -/

theorem enCell_isSome {ns : ℕ} {tl : HTailF2} {a r c : ℕ}
    (h : (cellJ (szOf tl) a r c).isSome = true) : Option.isSome (enCell ns tl a r c) = true := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h
  unfold enCell
  rw [hj]
  rfl

theorem enMask_isSome {ns : ℕ} {tl : HTailF2} {j : ℕ} (h : (finOf ns j).isSome = true) :
    Option.isSome (enMask ns tl j) = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
  unfold enMask
  rw [hk]
  rfl

/-- **Every entry that attention's layout names for a bit of a count is a cell.** -/
theorem att_bc_cell (S : Attention.Shape) (fs : Forest.Shape) (lm first ns : ℕ) (tl : HTailF2)
    (e : planesAtB tl fs lm (S.cf.NAs + 2) = true) (t k j : ℕ) (ht : t < 2 ^ fs.kT)
    (hk : k < fs.NC) (hj : j < 32) :
    Option.isSome ((attLay S fs lm first ns tl).bc t k j) = true :=
  enCell_isSome (planesAt_bc e t k j ht hk hj)

theorem att_mk_cell (S : Attention.Shape) (fs : Forest.Shape) (lm first ns : ℕ) (tl : HTailF2)
    (e : masksAtB fs first ns = true) (s : ℕ) (hs : s < FoNums.nMasks fs) :
    Option.isSome ((attLay S fs lm first ns tl).mkS s) = true :=
  enMask_isSome (masksAt_in e s hs)

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.cellRC_below
#print axioms VerifiableInference.Desc.First.Look.planesAt_bc
#print axioms VerifiableInference.Desc.First.Look.masksAt_in
#print axioms VerifiableInference.Desc.First.Look.att_bc_cell
#print axioms VerifiableInference.Desc.First.Look.att_mk_cell
