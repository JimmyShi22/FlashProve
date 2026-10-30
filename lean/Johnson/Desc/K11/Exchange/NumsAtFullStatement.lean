-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/NumsAtFullStatement.lean: THE NUMBERS OF THE DATA OF THE COMPOSED MEANING
AT THE FULL SIZE AGAINST THE NUMBERS OF THE LOT OF THE MERGE OF THE CLAIMS ON THE WEIGHTS, UNDER THE
ONE HEAD (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) AND ONE TEST WITH CODE ON THE PUBLIC PART:
STATEMENTS ALONE: four, each a definition of a proposition. NOTHING IS PROVED IN THIS FILE, and none
of the four is one of the library's goals: they are lemmas' statements. The texts are the
description's and the table's; no prover is named.

THE TEST: `numsB Zp 24 nR` (Johnson/Top/H0/MergeLaw/PlanNumsAt.lean), three in one: the planner's
segment 24 has as many slots as the public data's head; nR is the number of rows of the committed
table's layout; the row's shape has as many column bits as the layout. IT IS THE TEST tn FROM WHICH
THE LIBRARY's OWN `mergeFill_atAll` (Johnson/K11R/AtAll.lean) DRAWS THE LIKE EQUATIONS. nR here is
the index of the data's type: the written number of rows (`OnBytes.Flat.numsFull.rows`).

  `ColBitsAtFull`    under the head, at what the maker's own `ProofFile.baseOf` returns at the head's
                     public part, and under the test: the lot's layout has as many column bits as
                     the data's row's shape; and the data's index is the number of rows of the
                     data's layout
  `RowGivenFits`     no head, no test: wherever the reader of the pending row gives a row (`rowAt`,
                     Johnson/Top/H0/Walk/FrameRow.lean), the layout's rows are at most 2 to the row
                     bits of the shape: it is one of the reader's own tests
  `RowsFitAtFull`    under the head and the test: wherever the reader gives a row at the data's own
                     layout and shape: the data's index is at most 2 to the row bits of that shape
  `PlaceOfLot`       where the lot's number of the link is 24: the place of the kind's block at the
                     lot's numbers is the library's address of the kind (`IM.k11Place`,
                     Johnson/IMR/K11Seat.lean)

Limits. THE TEST IS A PREMISE HERE: the file that defines it says that it is shown true at no public
part there; `LT28.K11Tests.numsB_head_of_public` (Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean)
has its yes from the scope, the public files' readings and 18 column bits. The head is a premise.
`RowsFitAtFull` speaks only of states at which the reader gives a row: a sentence that asks the same
at no state is not shown by it; `RowsFitAtHead` (RowsFitStatement.lean of this folder) has the same
end under the head alone, with no test and no row. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.AtFullStatement
import Johnson.Top.H0.MergeLaw.PlanNumsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open OnBytes (TensorRow)
open OnBytes.Model (WsLay)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (numsB)
open ProofFile (Cl)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)
open Johnson.Desc.First.Walk.Law (rowAt)

/-- The statement on the column bits and the index. The letters: as in `HeadMergeAtFull`. Not proved
here; a lemma's statement, none of the library's goals. -/
def ColBitsAtFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    numsB Zp 24 OnBytes.Flat.numsFull.rows = true →
    (K11.parOf Zp Bs.G₀).lay.lk = h.𝔇.P13.lin.kCol ∧
      OnBytes.Flat.numsFull.rows = h.𝔇.d1.lay.m0

/-- The statement on the reader's own test. Not proved here; a lemma's statement, none of the
library's goals. -/
def RowGivenFits : Prop :=
  ∀ (lay : WsLay) (n : ℕ) (lin : OnBytes.Params.LinShape) (s : S) (r : TensorRow),
    rowAt lay n lin s = some r → lay.m0 ≤ 2 ^ lin.kRow

/-- The statement that the rows fit. The letters: as in `HeadMergeAtFull`. Not proved here; a
lemma's statement, none of the library's goals. -/
def RowsFitAtFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : ℕ) (s : S) (row : TensorRow),
    numsB Zp 24 OnBytes.Flat.numsFull.rows = true →
    rowAt h.𝔇.d1.lay n h.𝔇.d1.lin s = some row →
    OnBytes.Flat.numsFull.rows ≤ 2 ^ h.𝔇.d1.lin.kRow

/-- The statement on the place. Not proved here; a lemma's statement, none of the library's goals.
-/
def PlaceOfLot : Prop :=
  ∀ (Z : ProofFile.Pub) (G : ProofFile.Ground), (K11.parOf Z G).link = 24 →
    (headClaimMergeKind (K11.parOf Z G)).place = IM.k11Place

end Johnson.Desc.First.ForkMerge.Exchange

#print axioms Johnson.Desc.First.ForkMerge.Exchange.ColBitsAtFull
#print axioms Johnson.Desc.First.ForkMerge.Exchange.RowGivenFits
#print axioms Johnson.Desc.First.ForkMerge.Exchange.RowsFitAtFull
#print axioms Johnson.Desc.First.ForkMerge.Exchange.PlaceOfLot
