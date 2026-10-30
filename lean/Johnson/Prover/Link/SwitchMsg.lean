-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchMsg.lean: what an honest prover's new message is at a code switch of the
proximity test: the next stage's two tables, from the three folded messages, the three folded tails
and what stands in the free room. General in the two stages. No strategy, no record of an honest
side, no type of coins.

The layout is the library's (`csAt`, `csPut`, `csPlace`, OnBytes/Slice/CsData.lean): the folded main
message fills the new main table; the new mask table holds, from the index 0 on, the carried mask
row's message, the fresh mask row's message, the main row's tail, the carried mask row's tail and
the fresh mask row's tail; behind them is free room, whose last entry is the pad of the sample.
("fresh" is the library's name: see the docstring of ReadFront, Johnson/Prover/Link/ReadFront.lean.)

Main names (namespace `Johnson.Prover.Link`).
  `freeOf hf fr`   the free room's values, by the mask table's own index
  `gMsg hf μ' tl fr`   the new message, on the next stage's coordinates
  `gMain`, `gMask`, `gTab s μ' tl fr`   the two tables by index, written out: main (left), mask
      (right)
  `gAns hf μ' tl fr ρo`   the answer to the new message's sample at the seed ρo
  `gMsg_put`, `gMsg_free`   the new message at the layout's names
  `gTab_csAt`, `gMask_free`   the tables at the layout's indices; behind the last tail: free room
  `gMsg_tab`   the new message at a coordinate is the table's entry at the coordinate's index
  `mainOf_gMsg`, `maskOf_gMsg`   at a next stage without a row variable: the two functions that the
      base case's law takes (Johnson/Prover/Link/BaseClaim.lean) are the two tables

Limits. Definitions and equations. Nothing on how the free room's values or a tail are chosen.
Nothing on the tests of form, on trees or on hashes. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BaseClaim
import OnBytes.Slice.CsData

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes.Slice Cb

variable {s s' : Sg}

/-- Free room, by the mask table's own index: at q with outAt s' q.1 = .inr i the value is fr i.
Every q has that form (free_at, OnBytes/Slice/CsData.lean), so the other arm's 0 is never
returned. -/
def freeOf (hf : CsFit s s') (fr : ℕ → GE) : CsFree hf → GE := fun q =>
  match outAt s' q.1 with
  | .inl _ => 0
  | .inr i => fr i

/-- **The new message**: the next stage's message, typed straight off the layout. -/
def gMsg (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE) :
    s'.cIn.J → GE :=
  (csSw hf).re ((csSw hf).msg (μ', tl) (freeOf hf fr))

/-- The new main table, by index: the folded main message. -/
def gMain (s : Sg) (μ' : s.cMid.J → GE) (i : ℕ) : GE :=
  if h : i < s.C.l then μ' (.inl ⟨i, h⟩) else 0

/-- The new mask table, by index: the two folded mask messages, the three folded tails, then free
room: `fr` is read at the table's own index i, from 2 * s.Z.l + s.C.r + 2 * s.Z.r on. -/
def gMask (s : Sg) (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE) (i : ℕ) : GE :=
  if h : i < s.Z.l then μ' (.inr (.inl ⟨i, h⟩))
  else if h : i - s.Z.l < s.Z.l then μ' (.inr (.inr ⟨i - s.Z.l, h⟩))
  else if h : i - 2 * s.Z.l < s.C.r then tl (.inl ⟨i - 2 * s.Z.l, h⟩)
  else if h : i - (2 * s.Z.l + s.C.r) < s.Z.r then tl (.inr (.inl ⟨i - (2 * s.Z.l + s.C.r), h⟩))
  else if h : i - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r then
    tl (.inr (.inr ⟨i - (2 * s.Z.l + s.C.r + s.Z.r), h⟩))
  else fr i

/-- **The new message's two tables, by index**: main (left), mask (right). -/
def gTab (s : Sg) (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE) : ℕ ⊕ ℕ → GE :=
  Sum.elim (gMain s μ') (gMask s μ' tl fr)

/-- **The answer to the new message's sample.** -/
def gAns (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE)
    (ρo : (csSw hf).Zo.D) : GE :=
  (csSw hf).Zo.val ρo ((csSw hf).msg (μ', tl) (freeOf hf fr)) ()

variable (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE)

theorem gMsg_place (n : CsK s ⊕ CsFree hf) :
    gMsg hf μ' tl fr (csPlace hf n) = ldNew (Sum.elim μ' tl) (freeOf hf fr) n :=
  congrArg (ldNew (Sum.elim μ' tl) (freeOf hf fr)) ((csPlace hf).symm_apply_apply n)

theorem gMsg_put (n : CsK s) : gMsg hf μ' tl fr (csPut hf n) = Sum.elim μ' tl n :=
  gMsg_place hf μ' tl fr (.inl n)

theorem gMsg_free (q : CsFree hf) : gMsg hf μ' tl fr q.1 = freeOf hf fr q :=
  gMsg_place hf μ' tl fr (.inr q)

/-- The table at the index of an entry of the old full message. -/
theorem gTab_csAt (n : CsK s) : gTab s μ' tl fr (csAt s n) = Sum.elim μ' tl n := by
  rcases n with (j | j | j) | (q | q | q)
  · show gMain s μ' j.val = μ' (.inl j)
    unfold gMain
    rw [dif_pos j.isLt]
  · show gMask s μ' tl fr j.val = μ' (.inr (.inl j))
    unfold gMask
    rw [dif_pos j.isLt]
  · show gMask s μ' tl fr (s.Z.l + j.val) = μ' (.inr (.inr j))
    have n1 : ¬ s.Z.l + j.val < s.Z.l := by omega
    have e : s.Z.l + j.val - s.Z.l = j.val := by omega
    have p2 : s.Z.l + j.val - s.Z.l < s.Z.l := by rw [e]; exact j.isLt
    unfold gMask
    rw [dif_neg n1, dif_pos p2]
    exact congrArg (fun x => μ' (.inr (.inr x))) (Fin.ext e)
  · show gMask s μ' tl fr (2 * s.Z.l + q.val) = tl (.inl q)
    have n1 : ¬ 2 * s.Z.l + q.val < s.Z.l := by omega
    have n2 : ¬ 2 * s.Z.l + q.val - s.Z.l < s.Z.l := by omega
    have e : 2 * s.Z.l + q.val - 2 * s.Z.l = q.val := by omega
    have p3 : 2 * s.Z.l + q.val - 2 * s.Z.l < s.C.r := by rw [e]; exact q.isLt
    unfold gMask
    rw [dif_neg n1, dif_neg n2, dif_pos p3]
    exact congrArg (fun x => tl (.inl x)) (Fin.ext e)
  · show gMask s μ' tl fr (2 * s.Z.l + s.C.r + q.val) = tl (.inr (.inl q))
    have n1 : ¬ 2 * s.Z.l + s.C.r + q.val < s.Z.l := by omega
    have n2 : ¬ 2 * s.Z.l + s.C.r + q.val - s.Z.l < s.Z.l := by omega
    have n3 : ¬ 2 * s.Z.l + s.C.r + q.val - 2 * s.Z.l < s.C.r := by omega
    have e : 2 * s.Z.l + s.C.r + q.val - (2 * s.Z.l + s.C.r) = q.val := by omega
    have p4 : 2 * s.Z.l + s.C.r + q.val - (2 * s.Z.l + s.C.r) < s.Z.r := by rw [e]; exact q.isLt
    unfold gMask
    rw [dif_neg n1, dif_neg n2, dif_neg n3, dif_pos p4]
    exact congrArg (fun x => tl (.inr (.inl x))) (Fin.ext e)
  · show gMask s μ' tl fr (2 * s.Z.l + s.C.r + s.Z.r + q.val) = tl (.inr (.inr q))
    have n1 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val < s.Z.l := by omega
    have n2 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val - s.Z.l < s.Z.l := by omega
    have n3 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val - 2 * s.Z.l < s.C.r := by omega
    have n4 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val - (2 * s.Z.l + s.C.r) < s.Z.r := by omega
    have e : 2 * s.Z.l + s.C.r + s.Z.r + q.val - (2 * s.Z.l + s.C.r + s.Z.r) = q.val := by omega
    have p5 : 2 * s.Z.l + s.C.r + s.Z.r + q.val - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r := by
      rw [e]; exact q.isLt
    unfold gMask
    rw [dif_neg n1, dif_neg n2, dif_neg n3, dif_neg n4, dif_pos p5]
    exact congrArg (fun x => tl (.inr (.inr x))) (Fin.ext e)

/-- Behind the last tail the mask table holds the free room's values. -/
theorem gMask_free (i : ℕ) (h : 2 * s.Z.l + s.C.r + 2 * s.Z.r ≤ i) :
    gMask s μ' tl fr i = fr i := by
  have n1 : ¬ i < s.Z.l := by omega
  have n2 : ¬ i - s.Z.l < s.Z.l := by omega
  have n3 : ¬ i - 2 * s.Z.l < s.C.r := by omega
  have n4 : ¬ i - (2 * s.Z.l + s.C.r) < s.Z.r := by omega
  have n5 : ¬ i - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r := by omega
  unfold gMask
  rw [dif_neg n1, dif_neg n2, dif_neg n3, dif_neg n4, dif_neg n5]

/-- **The new message at a coordinate is the table's entry at the coordinate's index.** -/
theorem gMsg_tab (j : s'.cIn.J) : gMsg hf μ' tl fr j = gTab s μ' tl fr (outAt s' j) := by
  obtain ⟨n, rfl⟩ := (csPlace hf).surjective j
  rcases n with n | q
  · rw [csPlace_inl, gMsg_put, outAt_csPut, gTab_csAt]
  · rw [csPlace_inr, gMsg_free]
    obtain ⟨i, hi, h1, -⟩ := free_at hf q
    unfold freeOf
    rw [hi]
    exact (gMask_free μ' tl fr i h1).symm

/-- At a next stage without a row variable the base case's main function is the main table. -/
theorem mainOf_gMsg (hh : s'.h = 0) (hg : s'.g = 0) (j : ℕ) (hj : j < s'.C.l) :
    mainOf s' (gMsg hf μ' tl fr) j = gTab s μ' tl fr (.inl j) := by
  unfold mainOf
  rw [dif_pos hj, gMsg_tab]
  have hk : s'.h + s'.g = 0 := by omega
  have e : Sz.rowNo (fun _ : Fin (s'.h + s'.g) => false) + 2 ^ (s'.h + s'.g) * j = j := by
    rw [rowNo_zero hk, hk, pow_zero, one_mul, zero_add]
  exact congrArg (fun i => gTab s μ' tl fr (.inl i)) e

/-- And its mask function the mask table. -/
theorem maskOf_gMsg (hh : s'.h = 0) (j : ℕ) (hj : j < s'.Z.l) :
    maskOf s' (gMsg hf μ' tl fr) j = gTab s μ' tl fr (.inr j) := by
  unfold maskOf
  rw [dif_pos hj, gMsg_tab]
  have e : Sz.rowNo (fun _ : Fin s'.h => false) + 2 ^ s'.h * j = j := by
    rw [rowNo_zero hh, hh, pow_zero, one_mul, zero_add]
  exact congrArg (fun i => gTab s μ' tl fr (.inr i)) e

end Johnson.Prover.Link
