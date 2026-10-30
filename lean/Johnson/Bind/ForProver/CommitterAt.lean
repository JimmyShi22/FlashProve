-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/CommitterAt.lean: the index committer's share in a session's honest side
(`ProofFile.Honest.Committer`, Johnson/Desc/ProofFile/Honest/Committer.lean), filled with the encoded
index's columns (`encW`, Johnson/Bind/ForProver/Enc.lean) and the key of the out-of-domain (OOD)
sample (`oodSh`, Johnson/Bind/ForProver/Ood.lean).

Main names (namespace `Bind.ForProver`).
  **`committerAt sh Z xi key tie`**   the structure at a shape sh and a public part Z, both letters:
    the seed is typed at sh, so its type does not depend on Z. The columns are `encW Z` at the item
    0; the sample is `oodSh sh Z`. The builder of the explicit input, what the linear claim's shared
    rounds (the shared chain) read of it, and that the second of the first is the sample, are the
    caller's: three letters.
  `committerAt_enc`, `committerAt_ood`   the two fields that this file fills, by unfolding.
  `answersAt sh Z k`   the sample's answers as a list: those of `oodSh sh Z k`, by definition.
  **`columnsAndAnswersFromIndexAndCoins`**   where sh is Z's shape and the test `rowsFit` passes, at a position below 2^a,
    columns and answers are told through one function of index and coins, `rowMsgF`
    (Johnson/Bind/ForProver/Rows.lean), at the same entries and the same coins: a column is, row by
    row, the value of the row's polynomial, whose coefficients behind the tail are `rowMsgF`
    (`rowValueF`, Johnson/Bind/ForProver/Laws.lean); the answers are the library's sample map
    (`OnBytes.Slice.recZ`) at the typed seed on the messages `rowMsgF` (`msgsAt`). At the
    structure's own fields: `joinedAt` (Johnson/Bind/ForProver/JoinedAt.lean).

Limits. One committed table; which of the protocol's tables it is, the first or a copy, is not said
here. The item 0 is a session's numbering, not the link's (Johnson/Bind/ForProver/Enc.lean, Limits,
"Which item"). `tie` is a premise, which each caller has to meet. No public part is shown here at
which `rowsFit` passes: `rowsFit_of_ok` (Johnson/Bind/ForProver/K14Rows.lean) gives it from the
verifier's own test on the shape; `rowsFit_inScope` and `shapeOf_inScope`
(Johnson/Bind/ForProver/ShapeInScope.lean) from files in scope at which the maker of the public part
(`ProofFile.pubPlain`) returns; no theorem here gives it from files out of scope at
which it returns. The name `committerAt` stands in another namespace too: `FlashProve.committerAt`
(Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean) is another term: a stand-in committer, an algorithm that
returns a commitment (lean/TERMS.md names it among its examples); this one is a structure that a
prover's honest side reads. At another sh than Z's shape the columns are at Z's shape and the
answers at sh: two shapes in one value; `columnsAndAnswersFromIndexAndCoins` does not speak there. It is one table's share at sh
= `shapeOf Z` alone: without that equation, which `columnsAndAnswersFromIndexAndCoins` asks, a statement over it speaks of
columns and answers at two shapes. `columnsAndAnswersFromIndexAndCoins` sets two equations side by side; that the sample map's
answers are consistent with the columns as a code's words is the library's matter, not shown here.
Nothing here says that the Lean verifier accepts anything. No test of this file evaluates
`committerAt`. No correctness of extraction, no binding of the commitment (the opening form,
`BindsWith`, VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index
privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Ood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E TableKey)
open ProofFile.Honest (TableRand Weights Isk Committer)

variable {X Xi : Type}

/-- **The index committer's share, at a shape and a public part that are letters.** -/
def committerAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (xi : Isk Weights (ℕ → TableRand) (Seed sh × ℕ) → X → Xi) (key : Xi → TableKey)
    (tie : ∀ k x, key (xi k x) = oodSh sh Z k) :
    Committer Weights (ℕ → TableRand) (Seed sh × ℕ) X Xi TableKey :=
  ⟨fun w rc x => encW Z w rc 0 x, oodSh sh Z, xi, key, tie⟩

/-- Its columns. -/
theorem committerAt_enc (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (xi : Isk Weights (ℕ → TableRand) (Seed sh × ℕ) → X → Xi) (key : Xi → TableKey)
    (tie : ∀ k x, key (xi k x) = oodSh sh Z k) :
    (committerAt sh Z xi key tie).enc = fun w rc x => encW Z w rc 0 x := rfl

/-- Its sample. -/
theorem committerAt_ood (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (xi : Isk Weights (ℕ → TableRand) (Seed sh × ℕ) → X → Xi) (key : Xi → TableKey)
    (tie : ∀ k x, key (xi k x) = oodSh sh Z k) :
    (committerAt sh Z xi key tie).ood = oodSh sh Z := rfl

/-- The sample's answers, as a list. -/
def answersAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) : List E :=
  (oodSh sh Z k).record.toList

/-- **Columns and answers through one function of index and coins.** -/
theorem columnsAndAnswersFromIndexAndCoins (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (h : sh = shapeOf Z)
    (hfit : rowsFit sh (linOf Z).kLo (linOf Z).matrixRows = true)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) (x : ℕ) (hx : x < 2 ^ sh.a) :
    encW Z k.index k.coins 0 x =
        some ((List.range (2 ^ sh.v)).map fun b =>
          rowValueF sh (entryOfPub Z k.index) (k.coins 0) b
            (OnBytes.Slice.toF (Fmt.M1.point sh.a x))) ∧
      answersAt sh Z k =
        OnBytes.K.IdTable.spellAns sh.v sh.s
          (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val k.seed.1
            (msgsAt sh (entryOfPub Z k.index) (k.coins 0))) := by
  subst h
  have h3 : 3 * (shapeOf Z).s ≤ (shapeOf Z).l := by
    unfold rowsFit at hfit
    rw [Bool.and_eq_true, decide_eq_true_eq] at hfit
    exact hfit.1
  exact ⟨encW_values Z k.index k.coins x hfit hx, answers_oodSh (shapeOf Z) Z k h3⟩

end Bind.ForProver

#print axioms Bind.ForProver.committerAt_enc
#print axioms Bind.ForProver.committerAt_ood
#print axioms Bind.ForProver.columnsAndAnswersFromIndexAndCoins
#print axioms Bind.ForProver.committerAt
#print axioms Bind.ForProver.answersAt
