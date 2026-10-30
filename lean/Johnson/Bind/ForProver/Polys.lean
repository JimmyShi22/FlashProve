-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Polys.lean: THE LIBRARY'S HONEST POLYNOMIALS OF A COMMITTED TABLE'S ROWS, AT
A MATRIX AND COINS THAT ARE CUT OUT OF THE FRAME'S READERS, ARE THE COEFFICIENTS MADE OF THIS
FOLDER'S ROWS (`polysAt`, Johnson/Bind/ForProver/PolysAt.lean); and what the generator matrix, the
message part and the sample map give at `polysAt`. Statements and proofs; general in the sizes.

Why. The relation under which the decision at the library's link is shown to give "true"
(`Johnson.Prover.Link.Meant`, Johnson/Prover/Link/LinkYesStm.lean) speaks of two tables of
coefficients M₀, M₁. The library pays it at its own honest polynomials (`FlashProve.meant_obj`,
Johnson/Goal/Conditions/LinkMeant.lean). This folder has the encoded index's column (`encAt`) and
the OOD sample's answers (`oodAt`) as sums over `rowTailF` and `rowMsgF`. The equations here are
what carries the one to the other. Two inputs are spoken of below: the goals' (a matrix of cells,
pads and tails on finite ranges: what the library's typed encoder takes) and the frame's (functions
of two plain numbers: what the frame for an honest prover hands out).

Main names (namespace `Bind.ForProver`).
   `storedAt_eq_rowMsgF`: the layout of a row's message out of plain readers (`AtPublicFiles.Key.storedAt`,
      the library's E2E/KeyReaders.lean) is `rowMsgF` at the packing `entryAtF`: where the test
      `rowsFit` passes, at a row below 2^v and EVERY place.
   `polys_below`, `polys_from`: the two branches of `OnBytes.Slice.honestPolys`, by its text.
   **`polysOf_eq_polysAt`**: A LAW ON THE MAPS OF THE TIE (`cellsOfF`, `qOf`): under
      `Bind.Column.Agree sh S cut` and hfit: the library's honest polynomials at the cells
      `cellsOfF` of a matrix w and the coins `qOf` of ρ are `polysAt` at the packing of w and at ρ.
   `mulVec_polysAt`: the library's generator matrix on a row of `polysAt` gives `rowValueF`
      (Johnson/Bind/ForProver/Laws.lean) at the position's point, cast into the extension field.
   `view_polysAt`: the message part of `polysAt` is `msgK` (Johnson/Bind/ForProver/RecRows.lean).
   `val_msgsAt`: the sample map, one sample for each row, on `msgsAt`
      (Johnson/Bind/ForProver/Ood.lean) is the one row's sum over the coefficients from r on.
Limits. EQUATIONS BETWEEN TEXTS OF ONE TABLE'S ROWS: no move, no round and no run is added by them.
`Agree`, hfit and `rowsFit` are premises; at the full size they are theorems without premises
(`Bind.Column.agree_full`, Johnson/Bind/ColumnSizes.lean; `full_fits`,
Johnson/Flat/ClaimsSizes.lean; `rowsFit_full`, Johnson/Bind/ForProver/JoinsSizes.lean).
`storedAt_eq_rowMsgF`'s bound on the row is not idle: so the two texts read: from the row 2^v on
`entryAtF` gives 0 and `storedAt` reads the matrix's reader; no example of this file shows it. What
the fit guards at the readers: storedAt tests the matrix's bound first, so without the fit it would
hand the matrix's entry where the encoder lays a pad: a plain weight for a coin
(E2E/KeyReaders.lean, stored_eq_cell). `polysOf_eq_polysAt` HOLDS AT AN INPUT OF THE GOALS' TYPE
THAT IS MADE OF THE FRAME'S BY TWO DEFINITIONS (`cellsOfF`, `qOf`); THAT THE HONEST PROVER'S INPUT
AT THE PROTOCOL IS SO MADE IS SAID BY NO FILE BENEATH THIS ONE. THE LAW FOR THE OTHER DIRECTION, IN
WHICH THE FRAME'S READERS ARE MADE OF THE GOALS' INPUT, HOLDS AT EVERY MATRIX OF CELLS, not only at
those that `cellsOfF` makes: `polysOf_eq_polysAt_readers`
(Johnson/Bind/ForProver/PolysReaders.lean). The matrix w is a letter: any function of two numbers
into the base field, an index's or not. `mulVec_polysAt`, `view_polysAt` and `val_msgsAt` name no
map of the tie; `view_polysAt` unfolds two definitions under one equation of numbers; `val_msgsAt`
is the library's `Cb.ood_val_rows_same`, which holds of every table of messages, with one branch of
`rowCoefF`. Of `Agree` `mulVec_polysAt` reads a, l and r, `view_polysAt` reads r. One committed
table; which of the protocol's tables it is, the first or a copy, is not said here. No hash
function, no query, no coin's law. This file writes no honest prover. Nothing on completeness, on
index privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.PolysAt
import Johnson.Bind.ForProver.Restr
import Johnson.Bind.ForProver.LawsSizes
import Johnson.Bind.ForProver.K14Rows
import Johnson.Bind.ForProver.RecRows
import Johnson.Bind.ForProver.Ood
import Johnson.Goal.Conditions.LinkMeant

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (Sz GF GE toF ofF honestPolys honestMsgs genOf ptOf)
open OnBytes.Flat (cellWords MatrixNums rowWords tailWords)
open AtPublicFiles.Key (storedAt cellsReader padReader tailReader)
open ProofFile.Honest (TableRand)
open Bind.Twin (Shape)
open Bind.Column (Agree)

/-! ## The meeting place -/

/-- **The layout of a row's message out of plain readers is `rowMsgF` at the packing**: where the
test passes, at a row that the table has and every place. -/
theorem storedAt_eq_rowMsgF (sh : Shape) (kLo rows : ℕ) (hfit : rowsFit sh kLo rows = true)
    (w : ℕ → ℕ → GF) (ρ : TableRand) (b e : ℕ) (hb : b < 2 ^ sh.v) :
    storedAt w ρ.pad rows kLo sh.plain sh.l b e =
      rowMsgF sh (entryAtF kLo rows sh.v w) ρ b e := by
  have h4 : rows * 2 ^ kLo ≤ sh.plain := by
    unfold rowsFit at hfit
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hfit
    exact hfit.2
  unfold storedAt rowMsgF
  rw [toF_entryAtF kLo rows sh.v w b e hb]
  by_cases h1 : e < rows * 2 ^ kLo
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h4), if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : e < sh.plain
    · have n2 : ¬ (sh.plain ≤ e ∧ e < sh.l) := fun h => Nat.not_lt.2 h.1 h2
      rw [if_neg n2, if_pos h2]
    · rw [if_neg h2]
      by_cases h3 : e < sh.l
      · rw [if_pos ⟨Nat.not_lt.1 h2, h3⟩, if_pos h3]
      · have n3 : ¬ (sh.plain ≤ e ∧ e < sh.l) := fun h => h3 h.2
        rw [if_neg n3, if_neg h3]

/-! ## The library's honest polynomials, branch by branch -/

/-- Below r a coefficient of the library's honest polynomials is the tail's word, read in the field.
By that definition's text. -/
theorem polys_below (S : Sz) (msg tl : ℕ → List UInt64) (β : S.ix.Row) (k : S.Co)
    (hk : k.val < S.P.T.r) :
    honestPolys S msg tl β k = algebraMap GF GE (toF ((tl (Sz.rowNo β)).getD k.val 0)) := by
  show algebraMap GF GE
    (if k.val < S.P.T.r then toF ((tl (Sz.rowNo β)).getD k.val 0)
      else toF ((msg (Sz.rowNo β)).getD (k.val - S.P.T.r) 0)) = _
  rw [if_pos hk]

/-- From r on it is the message's entry. By that definition's text. -/
theorem polys_from (S : Sz) (msg tl : ℕ → List UInt64) (β : S.ix.Row) (k : S.Co)
    (hk : ¬ k.val < S.P.T.r) (hj : k.val - S.P.T.r < S.P.T.l) :
    honestPolys S msg tl β k = honestMsgs S msg (β, ⟨k.val - S.P.T.r, hj⟩) := by
  show algebraMap GF GE
    (if k.val < S.P.T.r then toF ((tl (Sz.rowNo β)).getD k.val 0)
      else toF ((msg (Sz.rowNo β)).getD (k.val - S.P.T.r) 0)) =
    algebraMap GF GE (toF ((msg (Sz.rowNo β)).getD (k.val - S.P.T.r) 0))
  rw [if_neg hk]

/-! ## The one new equation -/

/-- **The library's honest polynomials, at the goals' input made of the frame's, are `polysAt`.** A
law on the maps of the tie: the matrix of cells is `cellsOfF` of w and the coins are `qOf` of ρ, by
definition; that the honest prover's input at the protocol is so made is said by no file beneath
this one. -/
theorem polysOf_eq_polysAt {S : Sz} {Zs : Cb.Ood.Sample GE S.En} {cut : ℕ} {N : MatrixNums}
    {sh : Shape} (h : Agree sh S cut) (hfit : N.rows * 2 ^ N.kLo ≤ cut) (w : ℕ → ℕ → GF)
    (ρ : TableRand) :
    FlashProve.polysOf S Zs cut N (cellsOfF S Zs cut N w) (qOf S cut ρ) =
      polysAt S sh (entryAtF N.kLo N.rows S.P.v w) ρ := by
  have hc : cut + 3 * sh.s = sh.l := h.cut
  have hp : sh.plain = cut := by
    show sh.l - 3 * sh.s = cut
    omega
  have hrf : rowsFit sh N.kLo N.rows = true := (rowsFit_iff h _ _).2 hfit
  funext β k
  have hb : Sz.rowNo β < 2 ^ S.P.v := OnBytes.Slice.rowNo_lt β
  have hb' : Sz.rowNo β < 2 ^ sh.v := by
    rw [h.v]
    exact hb
  show honestPolys S
      (rowWords S (honestMsgs S (cellWords S Zs cut N (cellsOfF S Zs cut N w) (qOf S cut ρ).1)))
      (tailWords S (qOf S cut ρ).2) β k =
    algebraMap GF GE (rowCoefF sh (entryAtF N.kLo N.rows S.P.v w) ρ (Sz.rowNo β) k.val)
  by_cases hk : k.val < S.P.T.r
  · have hk' : k.val < sh.r := by
      rw [h.r]
      exact hk
    rw [polys_below S _ _ β k hk, AtPublicFiles.Key.tail_eq, rowCoefF_tail sh _ ρ _ _ hk']
    exact congrArg _ (tailReader_restr S ρ.tail _ _ hb hk)
  · have hj : k.val - S.P.T.r < S.P.T.l := by
      have h5 := k.isLt
      omega
    have e1 : rowCoefF sh (entryAtF N.kLo N.rows S.P.v w) ρ (Sz.rowNo β) k.val =
        rowMsgF sh (entryAtF N.kLo N.rows S.P.v w) ρ (Sz.rowNo β) (k.val - S.P.T.r) := by
      unfold rowCoefF
      rw [h.r, if_neg hk]
    have key := storedAt_eq_rowMsgF sh N.kLo N.rows hrf w ρ (Sz.rowNo β) (k.val - S.P.T.r) hb'
    rw [hp, h.l, h.v] at key
    rw [polys_from S _ _ β k hk hj, OnBytes.Flat.honestMsgs_rowWords,
      AtPublicFiles.Key.stored_eq_hold S cut N Zs hfit, e1]
    exact congrArg _ ((storedAt_restr S Zs cut N w ρ.pad _ _ hb).trans key)

/-! ## What the link reads of `polysAt` -/

/-- **The generator matrix on a row of `polysAt` gives the value of the row's polynomial at the
position's point.** -/
theorem mulVec_polysAt (S : Sz) {sh : Shape} {cut : ℕ} (h : Agree sh S cut)
    (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (β : S.ix.Row) (x : S.Pos) :
    S.ix.G.mulVec (polysAt S sh entry ρ β) x =
      algebraMap GF GE (rowValueF sh entry ρ (Sz.rowNo β) (toF (Fmt.M1.point sh.a x.val))) := by
  show ∑ k : Fin (S.P.T.r + S.P.T.l), genOf S.P.T x k * polysAt S sh entry ρ β k = _
  unfold rowValueF
  rw [h.a, h.r, h.l, map_add, map_sum, map_sum, Fin.sum_univ_add, Finset.sum_range,
    Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun q _ => ?_
    have hq : q.val < sh.r := by
      rw [h.r]
      exact q.isLt
    show algebraMap GF GE (ptOf S.P.T.a x ^ q.val) *
      algebraMap GF GE (rowCoefF sh entry ρ (Sz.rowNo β) q.val) = _
    rw [rowCoefF_tail sh entry ρ _ _ hq, map_mul]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : rowCoefF sh entry ρ (Sz.rowNo β) (S.P.T.r + j.val) =
        rowMsgF sh entry ρ (Sz.rowNo β) j.val := by
      rw [← h.r]
      exact rowCoefF_msg sh entry ρ _ _
    show algebraMap GF GE (ptOf S.P.T.a x ^ (S.P.T.r + j.val)) *
      algebraMap GF GE (rowCoefF sh entry ρ (Sz.rowNo β) (S.P.T.r + j.val)) = _
    rw [hj, map_mul]
    rfl

/-- **The message part of `polysAt`.** It unfolds the two definitions, under r = r. -/
theorem view_polysAt (S : Sz) {sh : Shape} {cut : ℕ} (h : Agree sh S cut)
    (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (n : S.ix.Row × S.En) :
    S.ix.view (polysAt S sh entry ρ) n = msgK sh entry ρ (Sz.rowNo n.1) n.2.val := by
  have hj : rowCoefF sh entry ρ (Sz.rowNo n.1) (S.P.T.r + n.2.val) =
      rowMsgF sh entry ρ (Sz.rowNo n.1) n.2.val := by
    rw [← h.r]
    exact rowCoefF_msg sh entry ρ _ _
  show algebraMap GF GE (rowCoefF sh entry ρ (Sz.rowNo n.1) (S.P.T.r + n.2.val)) =
    algebraMap GF GE (rowMsgF sh entry ρ (Sz.rowNo n.1) n.2.val)
  rw [hj]

/-- **The sample map on the rows' messages is, row by row, the sum over that row's coefficients from
r on.** The library's law on "one sample for each row", which holds of every table of messages, with
one branch of `rowCoefF`. -/
theorem val_msgsAt (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (σ : Seed sh)
    (β : Fin sh.v → Bool) (s : Fin sh.s) :
    ((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val σ (msgsAt sh entry ρ)
        (β, s) =
      ∑ j : Fin sh.l, (OnBytes.Slice.recZ sh.l sh.cube sh.s).mat σ s j *
        algebraMap GF GE (rowCoefF sh entry ρ (Sz.rowNo β) (sh.r + j.val)) := by
  refine (Cb.ood_val_rows_same GE (Fin sh.l) (Fin sh.v → Bool)
    (OnBytes.Slice.recZ sh.l sh.cube sh.s) σ (msgsAt sh entry ρ) β s).trans ?_
  show ∑ j : Fin sh.l, (OnBytes.Slice.recZ sh.l sh.cube sh.s).mat σ s j *
    msgsAt sh entry ρ (β, j) = _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rowCoefF_msg]
  rfl

end Bind.ForProver

end

#print axioms Bind.ForProver.storedAt_eq_rowMsgF
#print axioms Bind.ForProver.polys_below
#print axioms Bind.ForProver.polys_from
#print axioms Bind.ForProver.polysOf_eq_polysAt
#print axioms Bind.ForProver.mulVec_polysAt
#print axioms Bind.ForProver.view_polysAt
#print axioms Bind.ForProver.val_msgsAt
