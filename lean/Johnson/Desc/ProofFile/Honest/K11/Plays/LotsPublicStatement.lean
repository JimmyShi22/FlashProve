-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsPublicStatement.lean: WHETHER THE TEXTS `k11MaskLot` AND
`k11IndexLot` (MsgLotsStatement.lean of this folder) ANSWER AT AN ENTRY IS A FUNCTION OF THE BOOK,
THE CHAIN's NUMBER, THE PLACE, THE PLAN's NUMBERS AND THE ENTRY: OF NO RUN, NO INPUT AND NO
CHALLENGE. Two definitions (a row of parts; a Bool) and five definitions of propositions. NOTHING IS
PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `k11PublicRow` P   the merge's row of parts BEFORE IT IS SEATED: the draw's part, and the inner
                    term of `headMergeSum` (Honest/K11/Part.lean): typed at Unit and at the sum's
                    own input
  `k11Lends`         `lendsRow` (Honest/Small/LendsRow.lean, another group of authors') at that row:
                    it names the book, the chain's number, the place and P alone
  `LendsAtRow`       at every claims and weights: `lendsRow` at the seated row is `k11Lends`
  `LentIff`          at every run: `k11Lent` returns if and only if `k11Lends` says yes
  `MaskLotAnswers`   the first text answers just where `k11Lends` says yes and the entry lies inside
                    the text's own fence
  `IndexLotAnswers`  the like for the second text
  `LotsAnswerAlike`  so at two runs, two inputs and two lists of challenges each text answers at the
                    same entries

Why the first statement holds. The seat (`Part.lift`, Honest/Frame.lean) keeps a part's three counts
by its text, and `lendsRow` reads of a part these three alone: claims and weights enter the seated
row through the seat's reader of the input, which is not among them. Of `k11PublicRow` the three
counts alone are read here: it is a further text of the row's inner terms, tied to the seated row by
`LendsAtRow` as far as these counts go, and no further.

WHAT IT IS NOT. Nothing on WHAT a text answers. That any book lends the row is not said. No lot is
laid.

NEAR. `handed_public`, `msgTxt_isSome` (Honest/K2/Law/LotsAnswer.lean): the like for the switches'
texts, at two runs and with a test on the run's handing. `lotsSilent` (LotsRuns.lean of this
folder): a refusal makes both texts silent; with `lendRow_refuses` (LendsRow.lean): where `k11Lends`
says no, at every run.

Limits. Unfoldings over one law of the frame's level. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLotsStatement
import Johnson.Desc.ProofFile.Honest.Small.LendsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Place)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- The merge's row of parts before it is seated: for the counts alone: never laid as a row. -/
def k11PublicRow (P : HeadMergeP) : List (Part Unit HeadMergeAsk Unit) :=
  [headMergeDraw, sumPart (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
    (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay)]

/-- **Whether the book lends the merge's row**: of the book, the chain's number, the place and the
plan's numbers. -/
def k11Lends (Bk : ProverCoinCounts) (ch : Nat) (pl : Place) (P : HeadMergeP) : Bool :=
  lendsRow Bk ch pl (k11PublicRow P)

/-- The statement on the seated row. Not proved here; a lemma's statement, none of the library's
goals. -/
def LendsAtRow : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights),
    lendsRow Bk ch pl (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts =
      k11Lends Bk ch pl P

/-- The statement on where the row is lent. Not proved here; a lemma's statement, none of the
library's goals. -/
def LentIff : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (k : Coins Bk),
    (∃ c, k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .ok c) ↔
      k11Lends Bk ch pl P = true

/-- The statement on where the first text answers. Not proved here; a lemma's statement, none of the
library's goals. -/
def MaskLotAnswers : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (row place : Nat),
    ((k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd mask row
        place).isSome =
      (k11Lends Bk ch pl P &&
        decide (mask = true ∧ row = 0 ∧ ν₀ ≤ place ∧ place < ν₀ + (2 * P.lay.lk + 2)))

/-- The statement on where the second text answers. Not proved here; a lemma's statement, none of
the library's goals. -/
def IndexLotAnswers : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n r p : Nat)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (row place : Nat),
    ((k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n r p).txt k w hd mask row
        place).isSome =
      (k11Lends Bk ch pl P && decide (mask = true ∧ row = r ∧ place = p))

/-- The statement at two runs. Not proved here; a lemma's statement, none of the library's goals. -/
def LotsAnswerAlike : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ n' r p : Nat)
    (k k' : Coins Bk) (w w' : Local W₀ Rc Xi Tr) (hd hd' : List Fmt.Drawn) (mask : Bool)
    (row place : Nat),
    ((k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd mask row
        place).isSome =
      ((k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k' w' hd' mask row
        place).isSome ∧
    ((k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n' r p).txt k w hd mask row
        place).isSome =
      ((k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n' r p).txt k' w' hd' mask row
        place).isSome

end ProofFile.Honest.K11
