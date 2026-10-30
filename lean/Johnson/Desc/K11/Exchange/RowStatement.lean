-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/RowStatement.lean: FROM THE EQUATION ON THE MERGE's END VALUE, WITH THE
ROW WEIGHTS FOLDED OVER ALL ROWS OF THE LAYOUT, TO "THE PENDING ROW HOLDS" IN THE SENSE OF THE LAW
ON THE PILE OF PENDING ROWS (`Holds`, Johnson/Desc/K13/Law/Means.lean), of every row that the reader
off the verifier's state gives (`rowBy`, `rowAt`, Johnson/Top/H0/Walk/FrameRow.lean): STATEMENTS
ALONE: two, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and neither is one
of the library's goals: they are lemmas' statements. The texts are the verifier's and the table's;
no prover is named.

Why. The table of joints' sentence on what a link's own rounds leave for the row on the weights
(`woAt`, Johnson/Top/H0/Fill/FillP1.lean) is: every row that the reader gives at the state holds of
the witness's matrix and mask entries. A law on the merge ends in an equation on what the merge has
left.

  `RowSaysBehind`    the equation gives "the row holds", said plainly of the row's four fields
                     (`RowSays`, Johnson/Top/H0/MergeLaw/WoRow.lean)
  `RowHoldsBehind`   and so in the pile's own sense, at a witness whose matrix is the cells and
                     whose mask entries of the index masks' message are idx

THE EQUATION: with Gam folded by `wsGammaAdd` over what the merge has left from m0 zeros: the sum
over the rows y below m0 of Gam's member times row y of the cells read at the merge's point, and
beta times the mask entry idx c, is the shown end value; c: THE ENTRY THAT THE INDEX MASKS' LEDGER
GIVES NEXT AT THE STATE.

IT IS AN "IF": where the reader gives no row nothing is said, and no return is owed. It cuts both
ways: where the older routine refuses (the layout's rows are not the matrix's; another number of
claims; the span of rows) the sentence holds for nothing.

Limits. "left" is a letter: any reader of what a link's sub-proof has left (at the head's link:
`leftOf`, with `leftOf_of_head`, Johnson/Top/H0/Walk/FrameRow.lean). That what is left has the form
in which the merge's hearing lays it (hrecs) is a premise. Which mask entry c names, and that the
witness's entry there is any prover's coin, is not said. Nothing on any property.
-/
import Johnson.Top.H0.MergeLaw.RowHolds
import Johnson.Road.Rows.StretchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open OnBytes (E zeroE oneE mulE TensorRow)
open OnBytes.Model (Reading WsLay WsClaim WsForkOut wsRowPart wsEpsT wsGammaAdd)
open OnBytes.Road (Wm)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.First.MergeLaw (RowSays)
open VerifiableInference.Desc.K13.Law (Wit Holds lowBits)
open Johnson.Desc.First.Walk.Law (rowBy ledgerAt)

/-- The statement that the equation gives "the row holds", said plainly. left: a reader of what a
link's sub-proof has left. n: the plan's number of the sub-proof's claims on the weights. cr: the
claims, each with its batching factor. Not proved here; a lemma's statement, none of the library's
goals. -/
def RowSaysBehind : Prop :=
  ∀ (left : S → Option WsForkOut) (lay : WsLay) (n : ℕ) (lin : OnBytes.Params.LinShape) (s : S)
    (wo : WsForkOut) (cr : List (WsClaim × E)) (Gam : Array E) (cells : Wm Cb.Gl.E)
    (idx : ℕ → Cb.Gl.E),
    left s = some wo →
    wo.recs = cr.map (fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))) →
    wo.recs.foldlM (fun A r => wsGammaAdd A lay r oneE) (Array.replicate lay.m0 zeroE) =
      .ok Gam →
    (∀ l c l', ledgerAt s = some l → takeEntry l = some (c, l') →
      ∑ y ∈ Finset.range lay.m0, Reading.gl.val (Gam.getD y zeroE) *
          OnBytes.Road.rowAt Reading.gl lay.lk wo.rm cells y +
        Reading.gl.val wo.beta * idx c = Reading.gl.val wo.fvp) →
    ∀ r : TensorRow, rowBy left lay n lin s = some r → RowSays lay.lk lin.kRow cells idx r

/-- The statement in the pile's own sense. wK: a witness of nR rows and kC column bits, kC a letter
that is the layout's number of column bits by a premise, so that a witness typed at another term for
that number can be laid in without a cast: its matrix is the cells, which are 0 from row nR on; its
mask entries of the index masks' message are idx. Not proved here; a lemma's statement, none of the
library's goals. -/
def RowHoldsBehind : Prop :=
  ∀ (left : S → Option WsForkOut) (lay : WsLay) (n : ℕ) (lin : OnBytes.Params.LinShape) (s : S)
    (wo : WsForkOut) (cr : List (WsClaim × E)) (Gam : Array E) (cells : Wm Cb.Gl.E)
    (idx : ℕ → Cb.Gl.E) (nR kC : ℕ) (wK : Wit Cb.Gl.E nR kC),
    lay.lk = kC →
    left s = some wo →
    wo.recs = cr.map (fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))) →
    wo.recs.foldlM (fun A r => wsGammaAdd A lay r oneE) (Array.replicate lay.m0 zeroE) =
      .ok Gam →
    (∀ l c l', ledgerAt s = some l → takeEntry l = some (c, l') →
      ∑ y ∈ Finset.range lay.m0, Reading.gl.val (Gam.getD y zeroE) *
          OnBytes.Road.rowAt Reading.gl lay.lk wo.rm cells y +
        Reading.gl.val wo.beta * idx c = Reading.gl.val wo.fvp) →
    nR ≤ 2 ^ lin.kRow → (∀ j, nR ≤ j → ∀ C, cells j C = 0) →
    (∀ (i : Fin nR) (C : ℕ), C < 2 ^ kC → wK.mat i (lowBits kC C) = cells i C) →
    (∀ c, wK.mask ⟨s.out.indexMasks, c⟩ = idx c) →
    ∀ r : TensorRow, rowBy left lay n lin s = some r → Holds Reading.gl wK r

end Johnson.Desc.First.ForkMerge.Exchange
