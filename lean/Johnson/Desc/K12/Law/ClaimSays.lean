-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ClaimSays.lean: what the first claim of the proximity test's law means: a
bridge from `GroupSays` to the claim at which the law starts. Statements and proofs.

`GroupSays` (Johnson/Desc/Means/Says.lean) tells what a group's row says of the group's tables. The
law of the proximity test starts at the claim `q := stmG s row` (`StartK.behind`,
Johnson/Desc/K12/Law/Top.lean). This file shows that the two say the same.
Main names:
  `sum_table`: a table of 2^k rows and 2^e places, summed index by index, is summed by (row, place):
    the index is row + 2^k · place.
  `msgOf s T`: the group's main and mask table as one message of the stage's tables before the fold
    (`s.cIn.J`): entry (row, place) is the table's entry at row + 2^k · place, which is the order of
    bits of `vecG`.
  `groupValue_vecG`: at the reading in the library's field (`rdE`, OnBytes/Slice/BlkRead.lean, an
    abbreviation of `Model.Reading.gl`, OnBytes/Model/HideLaws.lean; `rdE.val a = readE a` by rfl),
    at a layout with the stage's numbers (L.k = s.h + s.g, L.h = s.h, 2 ^ L.logEll = s.C.l, 2 ^
    L.logEllZk = s.Z.l) and a row without kept forms: `groupValue rdE S L row T = ∑ j, vecG s row j
    * msgOf s T j`.
  `groupSays_iff`: under the same: `GroupSays rdE S L row T ↔ (Slf.idf).Holds (stmG s row) (msgOf s
    T)`. The right side is the proposition that the library's relation before a fold (`Sg.RIn`,
    OnBytes/Slice/Stage.lean) asks of a witness's message.
  `short_eq`: the same as an equation in "short of its target", the form in which `LaysRight`
    (Johnson/Desc/Means/Says.lean) composes.
Limits: nothing is said on where T comes from: that the tables are the committed words' (`tablesOf`,
`Laid`) and that the words are 0 where nobody sent anything (a member may have 18 rows in a table of
32) is left to whoever uses this file. Nothing is said on the batching itself: see
Johnson/Desc/K12/Law/BatMeans.lean. The four premises on L are not shown here of any layout: at the
first stage the block's own guard "the group is the first stage's" reads k and h; that 2 ^ logEll is
the code's message length needs the length to be a power of two. At the last stage the law reads the
row by `stmGk s 1 0`: not treated. No soundness is claimed, and nothing is said on hiding.
Lemmas of `verify-on-bytes`'s library that are called (none runs in a context of that program):
`sum_rowNo` (OnBytes/Slice/Cells.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.JointK
import Johnson.Desc.Means.Says

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open OnBytes.Means

/-- A table of 2^k rows and l = 2^e places, summed index by index, is summed row by row and place by
place: the index of (row, place) is row + 2^k · place. -/
theorem sum_table {M : Type} [AddCommMonoid M] (k e l : ℕ) (hl : 2 ^ e = l) (f : ℕ → M) :
    ∑ J ∈ Finset.range (2 ^ (k + e)), f J =
      ∑ x : (Fin k → Bool) × Fin l, f (Sz.rowNo x.1 + 2 ^ k * x.2.val) := by
  subst hl
  rw [Fintype.sum_prod_type_right]
  have h1 : ∀ y : Fin (2 ^ e), ∑ b : Fin k → Bool, f (Sz.rowNo b + 2 ^ k * y.val) =
      ∑ r : Fin (2 ^ k), f (r.val + 2 ^ k * y.val) := by
    intro y
    rw [sum_rowNo k (fun r => f (r + 2 ^ k * y.val)), Finset.sum_range]
  simp only [h1]
  rw [← Fintype.sum_prod_type (f := fun x : Fin (2 ^ e) × Fin (2 ^ k) => f (x.2.val + 2 ^ k *
      x.1.val)),
    ← Equiv.sum_comp finProdFinEquiv.symm, show 2 ^ (k + e) = 2 ^ e * 2 ^ k by rw [pow_add,
        Nat.mul_comm],
    Finset.sum_range]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 1
  show J.val = J.val % 2 ^ k + 2 ^ k * (J.val / 2 ^ k)
  exact (Nat.mod_add_div _ _).symm

/-- The group's two tables as a message of the stage's tables before the fold. -/
def msgOf (s : Sg) (T : Tables GE) : s.cIn.J → GE
  | .inl x => T.main (Sz.rowNo x.1 + 2 ^ (s.h + s.g) * x.2.val)
  | .inr x => T.mask (Sz.rowNo x.1 + 2 ^ s.h * x.2.val)

/-- The bridge. -/
theorem groupValue_vecG (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (T : Tables GE)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk =
        s.Z.l)
    (h0 : row.kept = #[]) :
    groupValue rdE S L row T = ∑ j : s.cIn.J, vecG s row j * msgOf s T j := by
  unfold groupValue
  have hkept : (∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
      keptSum rdE o i row.kept.toList * T.kept o i) = 0 := by
    rw [h0]
    simp [keptSum]
  rw [hkept, add_zero, hk, hh, sum_table _ _ _ hl, sum_table _ _ _ hz]
  exact (Fintype.sum_sum_type (fun j : s.cIn.J => vecG s row j * msgOf s T j)).symm

/-- What the group's row says of the tables is what the library's relation before a fold asks of
a message. -/
theorem groupSays_iff (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (T : Tables GE)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk =
        s.Z.l)
    (h0 : row.kept = #[]) :
    GroupSays rdE S L row T ↔ (Slf.idf (E := GE) (J := s.cIn.J)).Holds (stmG s row) (msgOf s T) :=
        by
  unfold GroupSays
  rw [groupValue_vecG s S L row T hk hh hl hz h0]
  exact Iff.rfl

/-- The same, as an equation in "short of its target". -/
theorem short_eq (s : Sg) (S : Statement) (L : GroupLayout) (row : GroupRow) (T : Tables GE)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l) (hz : 2 ^ L.logEllZk =
        s.Z.l)
    (h0 : row.kept = #[]) :
    groupValue rdE S L row T - rdE.val row.target =
      (∑ j : s.cIn.J, (stmG s row).2 j * msgOf s T j) - (stmG s row).1 := by
  rw [groupValue_vecG s S L row T hk hh hl hz h0]
  rfl

end H2K.ClaimSays

#print axioms H2K.ClaimSays.groupSays_iff
#print axioms H2K.ClaimSays.short_eq
