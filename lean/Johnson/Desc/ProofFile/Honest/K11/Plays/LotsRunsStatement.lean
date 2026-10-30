-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsRunsStatement.lean: THE TWO RUNS THAT THE TEXTS
`k11MaskLot` AND `k11IndexLot` (MsgLotsStatement.lean of this folder) READ HAVE THEIR FULL LENGTHS,
AT WHATEVER THE MERGE's ROW OF PARTS IS HANDED: THE FIRST RUN HAS 2 lk + 2 MEMBERS, THE END RUN HAS
ONE. SO NEITHER TEXT EVER FALLS BACK ON zeroE: WHAT IT READS IS A MEMBER OF THE RUN (which member's
value that is, 0 or not, is not said). WHERE THE ROW IS HANDED NOTHING BOTH TEXTS ARE SILENT.
STATEMENTS ALONE: five definitions of propositions; no definition of another kind. NOTHING IS PROVED
IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

Why. The first text guards `(firstRun c.2.1).getD (place - ν₀) zeroE` by a number of the plan, 2 lk
+ 2, not by the run's own length; the second reads `(endRun c.2.1).headD zeroE` behind no test of
length. Were a run shorter, a text would answer the reading of zeroE, in silence.

  `FirstRunFull`    at every c of the type `RowCoins` of the merge's row: the first run has
                    2 lk + 2 members
  `EndRunOne`       at every such c: the end run has one member
  `MaskLotReads`    so, inside the first text's guard, what it reads is a member of the first run
  `IndexLotReads`   so what the second text reads is the end run's one member
  `LotsSilent`      where `k11Lent` refuses, both texts answer none at every row and place

The first two speak of every c of that type, so of every c that `k11Lent` returns: `lendRow`
(Honest/Frame.lean) returns a member of that type. The lengths are fixed by the type: no book can
hand the row a shorter run. Where the book has too few for the row, `lendRow` refuses
(`lendRow_refuses`, Honest/Small/LendsRow.lean, another group of authors': where their public test
on the book's counts says no; not called here), and by the fifth statement the texts are then
silent: a short book brings silence, not zeroE.

WHAT IT IS NOT. Nothing on which entries of the book the runs are, nor on where a text answers at
all. No lot is laid.

NEAR. `firstRun_count`, `endRun_count` (Honest/SumLaw/SumShown.lean), `endRun_length`
(Honest/SumLaw/FitsAt.lean): the two lengths at any job of the sum's part, by the type.
Other groups of authors have the like inside proofs, at their own jobs, none as a lemma of its own:
the end run's count in Honest/K4/Law/MergeValue.lean; the first run's in Honest/K4/Law/SlotsOwn.lean
and Honest/K5/Law/Slots.lean.

Limits. Two counts, two corollaries and an unfolding. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLotsStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Place)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open ProofFile.Honest.SumLaw (firstRun endRun)

/-- The statement on the first run. Not proved here; a lemma's statement, none of the library's
goals. -/
def FirstRunFull : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : RowCoins (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts),
    (firstRun c.2.1).length = 2 * P.lay.lk + 2

/-- The statement on the end run. Not proved here; a lemma's statement, none of the library's
goals. -/
def EndRunOne : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : RowCoins (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts),
    (endRun c.2.1).length = 1

/-- The statement on what the first text reads. Not proved here; a lemma's statement, none of the
library's goals. -/
def MaskLotReads : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : RowCoins (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts)
    (ν₀ place : Nat), ν₀ ≤ place → place < ν₀ + (2 * P.lay.lk + 2) →
    (firstRun c.2.1)[place - ν₀]? = some ((firstRun c.2.1).getD (place - ν₀) zeroE)

/-- The statement on what the second text reads. Not proved here; a lemma's statement, none of the
library's goals. -/
def IndexLotReads : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights)
    (c : RowCoins (headMergeHalf (Rc := Rc) (Tr := Tr) (X := X) claims weights P).parts),
    endRun c.2.1 = [(endRun c.2.1).headD zeroE]

/-- The statement on where the row is handed nothing. Not proved here; a lemma's statement, none of
the library's goals. -/
def LotsSilent : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Xi Tr X : Type) (ch : Nat) (pl : Place) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (n ν₀ n' r p : Nat)
    (k : Coins Bk) (e : String),
    k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k = .error e →
    ∀ (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (row place : Nat),
      (k11MaskLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n ν₀).txt k w hd mask row
          place = none ∧
        (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights n' r p).txt k w hd mask row
          place = none

end ProofFile.Honest.K11
