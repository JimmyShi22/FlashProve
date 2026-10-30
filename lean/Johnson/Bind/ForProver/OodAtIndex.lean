-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/OodAtIndex.lean: the key of the out-of-domain (OOD) sample and the index
committer's share, where the index is a well-formed matrix of digits (`Cm.Idx`, Cm/RelBase.lean)
that is read through the library's reader of an index's digits (`OnBytes.HonestTrace.entryOf`,
Johnson/HonestTrace/IndexReaders.lean). Definitions, and laws that are instances of those at a
matrix in the field.

Main names (namespace `Bind.ForProver`).
  `iskOfIdx k`   what the prover keeps, with the index read through that reader.
  `oodIdx_eq`   `oodIdx Z k` (Johnson/Bind/ForProver/OodPlaces.lean), which reads the casts of the
    matrix's integers, is `ood` at that reader: by unfolding.
  **`oodIdxSh sh Z k`**   `oodSh` (Johnson/Bind/ForProver/Ood.lean) at that reader: the seed typed
    at a shape sh that is a letter. `oodIdxSh_shapeOf`: at Z's own shape it is `oodIdx Z k`.
  `okSeeds_oodIdxSh`, `okKey_oodIdxSh`, `keyFits_oodIdxSh`, `keyFits_oodIdxSh_of`   it passes the
    description's tests on an explicit input's key.
  `answers_oodIdxSh`   what its answers are: the library's sample map at the typed seed, on the
    rows' messages.
  **`committerIdxAt sh Z xi key tie`**   `ProofFile.Honest.Committer` at the index type `Cm.Idx`: the
    columns are `encIdx Z` (Johnson/Bind/ForProver/AtIndex.lean) at the item 0, the sample is
    `oodIdxSh sh Z`; the other three fields are the caller's.
  **`joinedIdx`**   `columnsAndAnswersFromIndexAndCoins` (Johnson/Bind/ForProver/CommitterAt.lean) at that reader: where sh is
    Z's shape and the test `rowsFit` passes, at a position below 2^a, columns and answers are told
    through one `rowMsgF`. At the structure's own fields: `joinedIdxAt`
    (Johnson/Bind/ForProver/JoinedAt.lean).

Limits. Columns and key are one committed table's; which of the protocol's tables it is, the first
or a copy, is not said here. The item 0 is a session's numbering, not the link's
(Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). `committerIdxAt` holds the columns at
`shapeOf Z` and the answers at sh: two shapes in one value, one table's at sh = `shapeOf Z` alone;
without that equation, which `joinedIdx` asks, a statement over it speaks of columns and answers at
two shapes. All of it means something at the full size's shape alone: `Cm.Idx` is typed at the
reference sizes. `tie` is a premise, which each caller has to meet. No public part is shown here at
which `rowsFit` passes: `rowsFit_of_ok` (Johnson/Bind/ForProver/K14Rows.lean) gives it from the
verifier's own test on the shape; `rowsFit_inScope` and `shapeOf_inScope`
(Johnson/Bind/ForProver/ShapeInScope.lean) from files in scope at which the maker of the public part
(`ProofFile.pubPlain`) returns; no theorem here gives it from files out of scope at
which it returns. Every law here is an instance of a law at a matrix in the field and says no more
than that law. No test of this file evaluates these definitions. Nothing here says that the Lean
verifier accepts anything. No correctness of extraction, no binding of the commitment (the opening
form, `BindsWith`, VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index
privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.OodPlaces
import Johnson.Bind.ForProver.CommitterAt
import Johnson.Bind.ForProver.AtIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E TableKey)
open ProofFile.Honest (TableRand Weights Isk Committer)
open VerifiableInference.Desc.Own (keyFits)

/-- What the prover keeps, the index read through the library's reader of an index's digits. -/
def iskOfIdx {Sd : Type} (k : Isk Cm.Idx (ℕ → TableRand) Sd) : Isk Weights (ℕ → TableRand) Sd :=
  ⟨⟨OnBytes.HonestTrace.entryOf k.index⟩, k.coins, k.seed⟩

/-- `oodIdx` is `ood` at that reader. -/
theorem oodIdx_eq (Z : ProofFile.Pub) (k : Isk Cm.Idx (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) :
    oodIdx Z k = ood Z (iskOfIdx k) := rfl

/-- **The key, the index a matrix of digits, the seed typed at a shape that is a letter.** -/
def oodIdxSh (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ)) : TableKey :=
  oodSh sh Z (iskOfIdx k)

/-- At the public part's own shape it is `oodIdx`. -/
theorem oodIdxSh_shapeOf (Z : ProofFile.Pub)
    (k : Isk Cm.Idx (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) :
    oodIdxSh (shapeOf Z) Z k = oodIdx Z k := rfl

section
variable (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ))

/-- The test on the seeds' words passes. -/
theorem okSeeds_oodIdxSh : OnBytes.Maker.okSeeds (oodIdxSh sh Z k) = true :=
  okSeeds_oodSh sh Z _

/-- The test of the linear claim's shared rounds (the shared chain) on the explicit input passes. -/
theorem okKey_oodIdxSh (c : OnBytes.Model.Verify.Chains) (before : List (Nat × Nat)) :
    Desc.K14.okKey (Desc.K14.p14Of c before) (oodIdxSh sh Z k) = true :=
  okKey_oodSh sh Z _ c before

/-- The key's sizes fit the shape sh. -/
theorem keyFits_oodIdxSh : keyFits (oodIdxSh sh Z k) (indexOf sh) = true :=
  keyFits_oodSh sh Z _

/-- They fit the public part's shape where sh is that shape. -/
theorem keyFits_oodIdxSh_of (h : sh = shapeOf Z) :
    keyFits (oodIdxSh sh Z k) (linOf Z).fold.index = true :=
  keyFits_oodSh_of sh Z _ h

/-- What its answers are. -/
theorem answers_oodIdxSh (h : 3 * sh.s ≤ sh.l) :
    (oodIdxSh sh Z k).record.toList =
      OnBytes.K.IdTable.spellAns sh.v sh.s
        (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val k.seed.1
          (msgsAt sh (entryOfPub Z ⟨OnBytes.HonestTrace.entryOf k.index⟩) (k.coins 0))) :=
  answers_oodSh sh Z (iskOfIdx k) h

end

variable {X Xi : Type}

/-- **The index committer's share at the index type `Cm.Idx`.** -/
def committerIdxAt (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (xi : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ) → X → Xi) (key : Xi → TableKey)
    (tie : ∀ k x, key (xi k x) = oodIdxSh sh Z k) :
    Committer Cm.Idx (ℕ → TableRand) (Seed sh × ℕ) X Xi TableKey :=
  ⟨fun i rc x => encIdx Z i rc 0 x, oodIdxSh sh Z, xi, key, tie⟩

/-- **Columns and answers through one function of index and coins.** -/
theorem joinedIdx (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (h : sh = shapeOf Z)
    (hfit : rowsFit sh (linOf Z).kLo (linOf Z).matrixRows = true)
    (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ)) (x : ℕ) (hx : x < 2 ^ sh.a) :
    encIdx Z k.index k.coins 0 x =
        some ((List.range (2 ^ sh.v)).map fun b =>
          rowValueF sh (entryOfPub Z ⟨OnBytes.HonestTrace.entryOf k.index⟩) (k.coins 0) b
            (OnBytes.Slice.toF (Fmt.M1.point sh.a x))) ∧
      (oodIdxSh sh Z k).record.toList =
        OnBytes.K.IdTable.spellAns sh.v sh.s
          (((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val k.seed.1
            (msgsAt sh (entryOfPub Z ⟨OnBytes.HonestTrace.entryOf k.index⟩) (k.coins 0))) :=
  columnsAndAnswersFromIndexAndCoins sh Z h hfit (iskOfIdx k) x hx

end Bind.ForProver

#print axioms Bind.ForProver.oodIdx_eq
#print axioms Bind.ForProver.oodIdxSh_shapeOf
#print axioms Bind.ForProver.okSeeds_oodIdxSh
#print axioms Bind.ForProver.okKey_oodIdxSh
#print axioms Bind.ForProver.keyFits_oodIdxSh
#print axioms Bind.ForProver.keyFits_oodIdxSh_of
#print axioms Bind.ForProver.answers_oodIdxSh
#print axioms Bind.ForProver.joinedIdx
#print axioms Bind.ForProver.iskOfIdx
#print axioms Bind.ForProver.oodIdxSh
#print axioms Bind.ForProver.committerIdxAt
