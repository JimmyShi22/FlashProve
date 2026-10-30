-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/XiAt.lean: a builder of the explicit input of a session, which lays the key
of the out-of-domain (OOD) sample (`oodSh`, Johnson/Bind/ForProver/Ood.lean) into it; with it a term
of the type `ProofFile.Honest.Committer` at the description's own explicit input; and what the prover that
the frame's maker of an honest prover yields reads of such an input. (`ProofFile.Inst`, which the
library's comment calls the instance, is the explicit input of a session: the instance proper, here
the two files' bytes, with the table's key.)

Why. The frame's maker of an honest prover (`ProofFile.Honest.onlineProverFromPublicFiles`,
Johnson/Desc/ProofFile/Honest/AtPure.lean) has no field for the OOD sample: the prover that it
yields reads the key off the explicit input (`ProofFile.Honest.pureKey`,
Johnson/Desc/ProofFile/Honest/Frame.lean). So a theorem on `oodSh` is a sentence on that prover only
at an input that holds `oodSh` as its key. The explicit input is a plain structure: the request
file's bytes, the key, the reply file's bytes (`ProofFile.Inst`, Johnson/Desc/ProofFile/Pub.lean).

Main names (namespace `Bind.ForProver`).
  **`xiAt sh Z k x`**   the explicit input with the request's and the reply's bytes x and the key
    `oodSh sh Z k`. `pureKey_xiAt`: its key, as the description reads it, is `oodSh sh Z k`: by
    unfolding.
  **`committerPure sh Z`**   `committerAt` (Johnson/Bind/ForProver/CommitterAt.lean) at that builder
    and at `pureKey`: its field `tie` is paid by unfolding. `committerPure_ood`, `committerPure_xi`,
    `committerPure_key`: three of its fields, by unfolding.
  **`key_atPure`**   where the maker yields, at every filling: the key that the yielded prover reads
    of `xiAt sh A.Z k x` is `oodSh sh A.Z k`: over the maker's own theorem (`ProofFile.Honest.atPure_ok`,
    Johnson/Desc/ProofFile/Honest/AtPureLaw.lean).
  `okSeeds_xiAt`   the test on the words of the seeds passes at that input's key.
  `xiIdxAt`, `pureKey_xiIdxAt`, `committerIdxPure`, `key_atPure_idx`   the same at the index type
    `Cm.Idx` (`oodIdxSh`, `committerIdxAt`, Johnson/Bind/ForProver/OodAtIndex.lean);
    `committerIdxPure_ood`, `committerIdxPure_xi`, `committerIdxPure_key`: three fields of the
    third.

Limits. The key is one committed table's; which of the protocol's tables it is, the first or a copy,
is not said here. The item 0 is a session's numbering, not the link's
(Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). The key stands in the explicit input
because this builder lays it there: `key_atPure` would hold of any key that a builder lays; nothing
here says that an input from elsewhere holds this one, and nothing here ties the key to the bytes of
a key file or of a copy's file. What the key's answers are, and where that is silent:
Johnson/Bind/ForProver/Ood.lean, Limits. k, a part of the index secret key, is a letter: nothing
here says that its index and coins are those at which the yielded prover's columns are read; the
theorem holds at fillings of another index type too. The five facts on the table and its key
(`FiveFields`) at the prover that `onlineProverFromPublicFiles` returns at one filling, under the head, from a premise
that ties the input's key to its index and coins: `five_of_validAt`; that premise at `xiAt`, at
every filling: `validAt_made` (AtFullSide/K14/FiveValid.lean, side library; there: NOT IN FRONT OF A
LAW OVER COINS: w is a letter and the premise ties its key to its coins). Z is any value of
`ProofFile.Pub`; in `key_atPure` and `key_atPure_idx` it is A.Z, which the maker made of its three files;
elsewhere nothing here says that it was made of three public files. That the maker yields is a
premise; sh is a letter, and only at A.Z's own shape do the theorems that join columns and answers
speak: `committerPure` and `committerIdxPure` hold the columns at `shapeOf Z` and the answers at sh,
two shapes in one value, one table's at sh = `shapeOf Z` alone; without that equation a statement
over them speaks of columns and answers at two shapes. Where `rowsFit` fails at Z the share has no
column and still a key. `ProofFile.Honest.Committer.prover` lays the columns at every item of the
statement; the prover that the maker yields at the columns `encW` has none at items other than 0: no
theorem here names `Committer.prover`. The form that lays the columns at one item is
`ProofFile.Honest.Committer.proverAt` (Johnson/Desc/ProofFile/Honest/CommitterAt.lean, another file than
Johnson/Bind/ForProver/CommitterAt.lean). The prover of that frame has fields that no text fills;
this file writes no honest prover. No test of this file evaluates these definitions. No correctness
of extraction, no binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index privacy; nothing
on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.OodAtIndex
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (TableKey)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest (TableRand Weights Isk Committer pureKey OnlineProverParts OnlineProverWithDescription onlineProverFromPublicFiles atPure_ok)

/-- **The explicit input that holds the key of the OOD sample**: x is the request file's bytes and
the reply file's. Of k the key reads the index, the coins of the item 0 alone (k.coins 0) and the
typed seed (k.seed.1), through `oodSh`; its own field `item` is 0. The coins of another item and the
copy's number (k.seed.2) are not in it. -/
def xiAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ))
    (x : ByteArray × ByteArray) : ProofFile.Inst :=
  ⟨⟨x.1, oodSh sh Z k⟩, x.2⟩

/-- Its key, as the description reads it. -/
theorem pureKey_xiAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) (x : ByteArray × ByteArray) :
    pureKey (xiAt sh Z k x) = oodSh sh Z k := rfl

/-- **The index committer's share at the description's own explicit input.** Its columns are
`encW Z` at the item 0: at the shape `shapeOf Z`, of the coins rc 0 alone; none from 2^a on, and
none at any position where the test `rowsFit` fails at Z. Its sample is `oodSh sh Z`, at the shape
sh, which gives a key there all the same. One table's share at sh = `shapeOf Z` alone (the head's
Limits). -/
def committerPure (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    Committer Weights (ℕ → TableRand) (Seed sh × ℕ) (ByteArray × ByteArray) ProofFile.Inst TableKey :=
  committerAt sh Z (xiAt sh Z) pureKey fun _ _ => rfl

/-- The test on the words of the seeds passes at that input's key. -/
theorem okSeeds_xiAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) (x : ByteArray × ByteArray) :
    OnBytes.Maker.okSeeds (xiAt sh Z k x).pub.key = true :=
  okSeeds_oodSh sh Z k

/-- The same builder at the index type `Cm.Idx`. -/
def xiIdxAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ))
    (x : ByteArray × ByteArray) : ProofFile.Inst :=
  ⟨⟨x.1, oodIdxSh sh Z k⟩, x.2⟩

/-- Its key, as the description reads it. -/
theorem pureKey_xiIdxAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ)) (x : ByteArray × ByteArray) :
    pureKey (xiIdxAt sh Z k x) = oodIdxSh sh Z k := rfl

/-- The index committer's share at the description's own explicit input, at the index type `Cm.Idx`:
its columns are `encIdx Z` at the item 0, its sample `oodIdxSh sh Z`; the rest as at
`committerPure`. -/
def committerIdxPure (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    Committer Cm.Idx (ℕ → TableRand) (Seed sh × ℕ) (ByteArray × ByteArray) ProofFile.Inst TableKey :=
  committerIdxAt sh Z (xiIdxAt sh Z) pureKey fun _ _ => rfl

/-- The field `ood` of `committerPure`, by unfolding. -/
theorem committerPure_ood (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    (committerPure sh Z).ood = oodSh sh Z := rfl

/-- Its field `xi`. -/
theorem committerPure_xi (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    (committerPure sh Z).xi = xiAt sh Z := rfl

/-- Its field `key`. -/
theorem committerPure_key (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    (committerPure sh Z).key = pureKey := rfl

/-- The field `ood` of `committerIdxPure`, by unfolding. -/
theorem committerIdxPure_ood (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    (committerIdxPure sh Z).ood = oodIdxSh sh Z := rfl

/-- Its field `xi`. -/
theorem committerIdxPure_xi (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    (committerIdxPure sh Z).xi = xiIdxAt sh Z := rfl

/-- Its field `key`. -/
theorem committerIdxPure_key (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) :
    (committerIdxPure sh Z).key = pureKey := rfl

section
variable {W₀ Rc Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  {Φ : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **What the prover that the maker yields reads of such an input**, at every filling. -/
theorem key_atPure (hA : onlineProverFromPublicFiles o pol lay KL Φ = .ok A) (sh : Bind.Twin.Shape)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) (x : ByteArray × ByteArray) :
    A.H.key (xiAt sh A.Z k x) = oodSh sh A.Z k := by
  rw [(atPure_ok hA).2.2.2.2.2.2.1]
  rfl

/-- The same at the index type `Cm.Idx`. -/
theorem key_atPure_idx (hA : onlineProverFromPublicFiles o pol lay KL Φ = .ok A) (sh : Bind.Twin.Shape)
    (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ)) (x : ByteArray × ByteArray) :
    A.H.key (xiIdxAt sh A.Z k x) = oodIdxSh sh A.Z k := by
  rw [(atPure_ok hA).2.2.2.2.2.2.1]
  rfl

end

end Bind.ForProver

#print axioms Bind.ForProver.pureKey_xiAt
#print axioms Bind.ForProver.okSeeds_xiAt
#print axioms Bind.ForProver.pureKey_xiIdxAt
#print axioms Bind.ForProver.committerPure_ood
#print axioms Bind.ForProver.committerPure_xi
#print axioms Bind.ForProver.committerPure_key
#print axioms Bind.ForProver.committerIdxPure_ood
#print axioms Bind.ForProver.committerIdxPure_xi
#print axioms Bind.ForProver.committerIdxPure_key
#print axioms Bind.ForProver.key_atPure
#print axioms Bind.ForProver.key_atPure_idx
#print axioms Bind.ForProver.xiAt
#print axioms Bind.ForProver.committerPure
#print axioms Bind.ForProver.xiIdxAt
#print axioms Bind.ForProver.committerIdxPure
