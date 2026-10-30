-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsHead.lean

The matrix bH of the output head's sub-proof, the planes of the counts of the lookup of its calls,
as a function bH of a reading of the sub-proof's cells; and the relation MidP of the library's
algebra of a padded lookup at it.

Notation. P : PubH is what is public at the head, and cell : NameH → K a reading of the named cells
(OnBytes/Tie/Pv/Lookup/Ends/H.lean) in a field K with decidable equality. Ends.H.kvH P cell q i is
place i of call q's key vector, a term of that file. tabOf K P.L.fs c t is row t of call c's table
(Johnson/HonestTrace/CountsTab.lean). NC, kT, v, d are fields of P.L.fs : Forest.Shape, and n_c, k_c
are FoNums.nOf P.L.fs c, FoNums.kOf P.L.fs c, as in the head of
Johnson/HonestTrace/CountsJoint.lean. V is the size of the vocabulary and JV is V rounded up to
whole blocks; the entries from V to JV - 1 are called filler entries here. "The layout returns"
means Head.layout P.h tau = .ok P.L for some array tau; Head.layout is a function of the Lean
verifier under OnBytes/Model/. A sub-proof has a second lookup, of the smallness test's digits; this
file is not on it.

Main definitions:
* "hitsH P cell": the padding places are padH's (Johnson/HonestTrace/CountsHeadPub.lean). The chosen
  row of a padding place is its call's padding row (padding places are not counted); every other
  place is counted at the first row below 2^(k_c) of its call's table that holds its key.
* "bH P cell r col": the planes' matrix of 2^lmbH rows of these counts ("plane",
  Johnson/HonestTrace/Counts.lean); every value is 0 or 1. It is a function of the whole reading.
* "LaidBH P cell": the cells of matrix number NHf + 2 are bH P cell, of this very reading, at every
  row below 2^lmbH and column below NC * 2^(kT + 5 - lmbH).
* "FillerIsPad P cell": at every place, below the length of its call's key vector, whose column
  holds a filler entry, kvH holds the value of the call's padding row.
* "withBH P cell": cell with bH P cell laid over matrix number NHf + 2. "KeysSkipBH P cell": that
  changes no key, at the places below the length of each call's key vector.

Main theorems. "hin" stands for: for every call c below NC, every place of kvH P cell c below
2^(n_c) holds the value of a row below 2^(k_c) of tabOf.
* "lawH": if the layout returns, with hin, FillerIsPad P cell and LaidBH P cell: at every θ and al
  of K, Cb.Lkp.MidP (Cb/Pv/Lookup/Alg/PadAlg.lean) holds of the joint key vector Ends.H.keyH P cell
  θ, the joint table Ends.H.tabH P θ, the list FoNums.pads P.L.fs and the bits Ends.H.bitsH of cell.
  One reading cell gives both the keys and the bits.
* "sum_bH": if the layout returns, with hin and FillerIsPad P cell: the cells of bH P cell, each
  weighted by 2^(r % 32), and the number P.L.fs.padding add up to 2^v.
* "fillerIsPad_of_JV": if the layout returns and P.L.JV = P.h.V, FillerIsPad P cell holds of every
  cell: no place is asked about.
* "withBH_laid", "inTable_withBH", "filler_withBH": under KeysSkipBH P cell, LaidBH holds of withBH
  P cell, and hin and FillerIsPad pass from cell to withBH P cell.

Limits. No theorem of this file shows, without a premise on the cells, hin, FillerIsPad (where
P.L.JV is not P.h.V), LaidBH or KeysSkipBH of any cell; if the layout returns, KeysSkipBH is shown
in Johnson/HonestTrace/CountsHeadSkip.lean. FillerIsPad is a condition on the cells that the keys
read, not on the counts. Where a key is in no row of its table, hitsH counts it at row 0; fitsH,
lawH and sum_bH have hin, so they do not speak of that case. bH is a specification: a count is a
filter over 2^(n_c) places, and the first row a search through 2^(k_c) rows. bH depends on K through
the comparison of keys with rows (see hitsOf_map, Johnson/HonestTrace/Counts.lean). A table with
fewer than 2^kT rows is repeated in the joint table; bH counts in the first copy. That Head.layout
returns for some shape is not shown in this file. That kvH, keyH, tabH and bitsH are what a verifier
reads is no theorem of Ends/H.lean or of this file.

Not claimed: that a prover's committed cells are these; that MidP makes any claim of the protocol's
lookup argument hold; that a verifier accepts a proof made with these cells; anything on soundness
or zero knowledge.

-/
import Johnson.HonestTrace.CountsLaw
import Johnson.HonestTrace.CountsRect
import Johnson.HonestTrace.CountsHeadPub

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open OnBytes.Ends.H (NameH PubH)

/-! ## The layout's numbers; the definitions -/

/-- If Head.layout h tau returns L, then FoNums.ok L.fs = true and 5 ≤ h.lmbH ≤ L.fs.kT + 5. (From
Fo.Pub2.shapeOf_headLayout and Fo.Pay.shapeOf_ok.) -/
theorem ok_H {h : Head.Shape} {tau : Array F} {L : Head.HL} (hy : Head.layout h tau = .ok L) :
    FoNums.ok L.fs = true ∧ 5 ≤ h.lmbH ∧ h.lmbH ≤ L.fs.kT + 5 :=
  ⟨Fo.Pay.shapeOf_ok (Fo.Pub2.shapeOf_headLayout hy).1, (Fo.Pub2.shapeOf_headLayout hy).2⟩

section Defs
variable {K : Type} [Field K] [DecidableEq K]

/-- The padding places and the chosen rows of the lookup of the head's calls at the reading cell.
The padding places are padH's. The chosen row of a padding place is its call's padding row (padding
places are not counted); every other place is counted at the first row below 2^(k_c) of tabOf that
holds its key Ends.H.kvH P cell (at row 0 if none does). -/
def hitsH (P : PubH) (cell : NameH → K) : Hits :=
  hitsOf P.L.fs (tabOf K P.L.fs) (Ends.H.kvH P cell) (padH P.h P.L)

/-- The planes' matrix of the lookup of the head's calls at the reading cell, as a function of row
and column; every value is 0 or 1: plane at P.L.fs, 2^lmbH rows and hitsH P cell. -/
def bH (P : PubH) (cell : NameH → K) (r col : ℕ) : ℕ :=
  plane P.L.fs P.h.lmbH (hitsH P cell) r col

/-- The cells of matrix number P.h.NHf + 2 are the planes' matrix bH of this very reading, cast into
K, at every row below 2^lmbH and column below NC * 2^(kT + 5 - lmbH). Nothing is asked outside these
rows and columns, where bH is 0 (plane_outside). -/
def LaidBH (P : PubH) (cell : NameH → K) : Prop :=
  ∀ r < 2 ^ P.h.lmbH, ∀ c < P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH),
    cell (.cell (P.h.NHf + 2) r c) = (bH P cell r c : K)

/-- The reading cell with bH P cell, cast into K, laid over matrix number P.h.NHf + 2. -/
def withBH (P : PubH) (cell : NameH → K) : NameH → K
  | .cell m r c => if m = P.h.NHf + 2 then (bH P cell r c : K) else cell (.cell m r c)
  | .w r c => cell (.w r c)

/-- Laying bH P cell over matrix number P.h.NHf + 2 changes no key: for every call q below NC and
every place i below 2^(n_q), Ends.H.kvH at withBH P cell is Ends.H.kvH at cell. -/
def KeysSkipBH (P : PubH) (cell : NameH → K) : Prop :=
  ∀ q < P.L.fs.NC, ∀ i < 2 ^ FoNums.nOf P.L.fs q,
    Ends.H.kvH P (withBH P cell) q i = Ends.H.kvH P cell q i

end Defs

/-! ## The padding places hold the padding row's value -/

/-- For every call q below NC and every place i below 2^(n_q): if Ends.H.colH finds in column i / T
entry x of a segment sn with Head.perEntry sn and P.h.V ≤ Head.firstEntry P.L sn + x (a filler
entry), then Ends.H.kvH P cell q i is the value of the call's padding row. A condition on the cells
that these keys read. -/
def FillerIsPad {K : Type} [Field K] (P : PubH) (cell : NameH → K) : Prop :=
  ∀ q < P.L.fs.NC, ∀ i < 2 ^ FoNums.nOf P.L.fs q, ∀ sn x,
    Ends.H.colH P.L q (i / P.h.T) = some (sn, x) → Head.perEntry sn = true →
    P.h.V ≤ Head.firstEntry P.L sn + x →
    Ends.H.kvH P cell q i = tabOf K P.L.fs q (FoNums.t0Of P.L.fs q)

/-- Let FillerIsPad P cell hold, let P.L.fs have NC calls, q be below NC and i below 2^(n_q). If
padH says that place i of call q is a padding place, Ends.H.kvH P cell q i is the value of the
call's padding row. In a column that no segment lists this is kvH's own text; elsewhere it is
FillerIsPad. -/
theorem kvH_pad {K : Type} [Field K] (P : PubH) (cell : NameH → K) (hfill : FillerIsPad P cell)
    {q i : ℕ} (hq : q < P.L.fs.NC) (hs : P.L.fs.calls.size = P.L.fs.NC)
    (hi : i < 2 ^ FoNums.nOf P.L.fs q) (hp : padH P.h P.L q i = true) :
    Ends.H.kvH P cell q i = tabOf K P.L.fs q (FoNums.t0Of P.L.fs q) := by
  unfold padH at hp
  cases hc : Ends.H.colH P.L q (i / P.h.T) with
  | none =>
    unfold Ends.H.kvH Ends.H.kvOf
    rw [hc]
    exact (tabOf_eq K P.L.fs (by omega) _).symm
  | some a =>
    obtain ⟨sn, x⟩ := a
    rw [hc] at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hfill q hq i hi sn x hc hp.1 hp.2

/-- **Where JV = V nothing is asked.** If Head.layout P.h tau returns P.L and P.L.JV = P.h.V, then
FillerIsPad P cell holds of every cell: by HeadPub.entry_lt no place meets its condition. -/
theorem fillerIsPad_of_JV {K : Type} [Field K] {tau : Array F} (P : PubH)
    (hy : Head.layout P.h tau = .ok P.L) (hJV : P.L.JV = P.h.V) (cell : NameH → K) :
    FillerIsPad P cell := by
  intro q _ i _ sn x hc hp hv
  have k := HeadPub.entry_lt hy hc hp
  omega

/-! ## The relation MidP at the head -/

section Law
variable {K : Type} [Field K] [DecidableEq K]

/-- If 5 ≤ lmbH ≤ kT + 5 and LaidBH P cell holds, then for u below 2^d and j below 32 the bit
Ends.H.bitsH P.h P.L.fs cell (u * 32 + j) is the cell of plane, at hitsH P cell, at
FoNums.cellRC (u / 2^cK, u % 2^cK, j), cast into K. -/
theorem bitsH_plane (P : PubH) (cell : NameH → K) (h5 : 5 ≤ P.h.lmbH)
    (hlm : P.h.lmbH ≤ P.L.fs.kT + 5) (hb : LaidBH P cell) {u j : ℕ}
    (hu : u < 2 ^ P.L.fs.d) (hj : j < 32) :
    Ends.H.bitsH P.h P.L.fs cell (u * 32 + j) =
      (plane P.L.fs P.h.lmbH (hitsH P cell)
        (FoNums.cellRC P.L.fs P.h.lmbH (u / 2 ^ P.L.fs.cK, u % 2 ^ P.L.fs.cK, j)).1
        (FoNums.cellRC P.L.fs P.h.lmbH (u / 2 ^ P.L.fs.cK, u % 2 ^ P.L.fs.cK, j)).2 : K) := by
  have e1 : (u * 32 + j) / 32 = u := by omega
  have e2 : (u * 32 + j) % 32 = j := by omega
  have ht : u / 2 ^ P.L.fs.cK < 2 ^ P.L.fs.kT := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_comm]
    exact hu
  unfold Ends.H.bitsH Ends.H.placeH
  rw [e1, e2]
  by_cases hc : u % 2 ^ P.L.fs.cK < P.L.fs.NC
  · rw [if_pos ⟨hc, hj, hu⟩]
    exact hb _ (cellRC_in _ h5 hlm ht hc hj).1 _ (cellRC_in _ h5 hlm ht hc hj).2
  · rw [if_neg fun q => hc q.1]
    have e : plane P.L.fs P.h.lmbH (hitsH P cell)
        (FoNums.cellRC P.L.fs P.h.lmbH (u / 2 ^ P.L.fs.cK, u % 2 ^ P.L.fs.cK, j)).1
        (FoNums.cellRC P.L.fs P.h.lmbH (u / 2 ^ P.L.fs.cK, u % 2 ^ P.L.fs.cK, j)).2 = 0 := by
      refine plane_outside _ _ _ (Or.inr ?_)
      show _ ≤ u % 2 ^ P.L.fs.cK * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH) + _
      exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_not_lt hc)) (Nat.le_add_right _ _)
    rw [e]
    exact Nat.cast_zero.symm

/-- If Head.layout P.h tau returns P.L, for every call c below NC every place below 2^(n_c) of
Ends.H.kvH P cell c holds the value of a row below 2^(k_c) of tabOf, and FillerIsPad P cell holds,
then Fits holds of P.L.fs, tabOf, Ends.H.kvH P cell and hitsH P cell. -/
theorem fitsH {tau : Array F} (P : PubH) (hy : Head.layout P.h tau = .ok P.L) (cell : NameH → K)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c))
    (hfill : FillerIsPad P cell) :
    Fits P.L.fs (tabOf K P.L.fs) (Ends.H.kvH P cell) (hitsH P cell) :=
  fits_hitsOf P.L.fs _ _ _ (ok_H hy).1 hin
    (fun _ hc _ hi hp => kvH_pad P cell hfill hc (calls_size (ok_H hy).1).1 hi hp) (pubFits_H hy)

/-- **The relation after the challenge (MidP) at the head, for one reading of the cells.** If
Head.layout P.h tau returns P.L, for every call c below NC every place below 2^(n_c) of Ends.H.kvH P
cell c holds the value of a row below 2^(k_c) of tabOf, and FillerIsPad P cell and LaidBH P cell
hold, then for all θ and al Cb.Lkp.MidP holds at Ends.H.keyH P cell θ, Ends.H.tabH P θ, FoNums.pads
P.L.fs and the bits Ends.H.bitsH P.h P.L.fs cell (u * 32 + j). -/
theorem lawH {tau : Array F} (P : PubH) (hy : Head.layout P.h tau = .ok P.L) (cell : NameH → K)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c))
    (hfill : FillerIsPad P cell) (hb : LaidBH P cell) (θ al : K) :
    Cb.Lkp.MidP P.L.fs.v P.L.fs.d 5 32 (Ends.H.keyH P cell θ) (Ends.H.tabH P θ)
      (FoNums.pads P.L.fs) (fun u j => Ends.H.bitsH P.h P.L.fs cell (u * 32 + j)) al := by
  obtain ⟨hok, h5, hlm⟩ := ok_H hy
  exact law_bits P.L.fs (Ends.H.kvH P cell) (padH P.h P.L) hok hin
    (fun _ hc _ hi hp => kvH_pad P cell hfill hc (calls_size hok).1 hi hp) (pubFits_H hy) h5 hlm _
    (fun u hu j hj => bitsH_plane P cell h5 hlm hb hu hj) θ al

/-- Under the premises of fitsH: the cells of bH P cell in the rows below 2^lmbH and the columns
below NC * 2^(kT + 5 - lmbH), each weighted by 2^(r % 32), and P.L.fs.padding add up to 2^v. -/
theorem sum_bH {tau : Array F} (P : PubH) (hy : Head.layout P.h tau = .ok P.L) (cell : NameH → K)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c))
    (hfill : FillerIsPad P cell) :
    ∑ col ∈ range (P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH)), ∑ r ∈ range (2 ^ P.h.lmbH),
        2 ^ (r % 32) * bH P cell r col + P.L.fs.padding = 2 ^ P.L.fs.v := by
  obtain ⟨hok, h5, hlm⟩ := ok_H hy
  exact sum_plane_all P.L.fs _ _ _ hok (fitsH P hy cell hin hfill) h5 hlm

/-! ## Laying the planes into the cells -/

/-- Under KeysSkipBH P cell, hitsH at withBH P cell and at cell agree at all places below 2^(n_c) of
all calls c below NC. -/
theorem hitsH_withBH (P : PubH) (cell : NameH → K) (hs : KeysSkipBH P cell) :
    ∀ c < P.L.fs.NC, ∀ i < 2 ^ FoNums.nOf P.L.fs c,
      (hitsH P (withBH P cell)).pad c i = (hitsH P cell).pad c i ∧
      (hitsH P (withBH P cell)).row c i = (hitsH P cell).row c i := by
  intro c hc i hi
  refine ⟨rfl, ?_⟩
  show (if padH P.h P.L c i = true then FoNums.t0Of P.L.fs c
      else firstRow (tabOf K P.L.fs c) (FoNums.kOf P.L.fs c)
        (Ends.H.kvH P (withBH P cell) c i)) =
    if padH P.h P.L c i = true then FoNums.t0Of P.L.fs c
      else firstRow (tabOf K P.L.fs c) (FoNums.kOf P.L.fs c) (Ends.H.kvH P cell c i)
  rw [hs c hc i hi]

/-- Under KeysSkipBH P cell, LaidBH holds of withBH P cell. -/
theorem withBH_laid (P : PubH) (cell : NameH → K) (hs : KeysSkipBH P cell) :
    LaidBH P (withBH P cell) := by
  intro r _ c _
  show (if P.h.NHf + 2 = P.h.NHf + 2 then (bH P cell r c : K)
    else cell (.cell (P.h.NHf + 2) r c)) = (bH P (withBH P cell) r c : K)
  rw [if_pos rfl]
  exact congrArg Nat.cast (plane_congr _ _ (hitsH_withBH P cell hs) r c).symm

/-- Under KeysSkipBH P cell: if for every call c below NC every place below 2^(n_c) of Ends.H.kvH P
cell c holds the value of a row below 2^(k_c) of tabOf, the same holds of Ends.H.kvH P (withBH P
cell) c. -/
theorem inTable_withBH (P : PubH) (cell : NameH → K) (hs : KeysSkipBH P cell)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c)) :
    ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P (withBH P cell) c) (tabOf K P.L.fs c) := by
  intro c hc b hb
  rw [hs c hc b hb]
  exact hin c hc b hb

/-- Under KeysSkipBH P cell, FillerIsPad passes from cell to withBH P cell. -/
theorem filler_withBH (P : PubH) (cell : NameH → K) (hs : KeysSkipBH P cell)
    (hfill : FillerIsPad P cell) : FillerIsPad P (withBH P cell) := by
  intro q hq i hi sn x hc hp hv
  rw [hs q hq i hi]
  exact hfill q hq i hi sn x hc hp hv

end Law

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.ok_H
#print axioms OnBytes.HonestTrace.kvH_pad
#print axioms OnBytes.HonestTrace.fillerIsPad_of_JV
#print axioms OnBytes.HonestTrace.bitsH_plane
#print axioms OnBytes.HonestTrace.fitsH
#print axioms OnBytes.HonestTrace.lawH
#print axioms OnBytes.HonestTrace.sum_bH
#print axioms OnBytes.HonestTrace.hitsH_withBH
#print axioms OnBytes.HonestTrace.withBH_laid
#print axioms OnBytes.HonestTrace.inTable_withBH
#print axioms OnBytes.HonestTrace.filler_withBH
