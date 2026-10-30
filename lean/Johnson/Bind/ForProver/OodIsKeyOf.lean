-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/OodIsKeyOf.lean: the key of the out-of-domain (OOD) sample that is made of
what the prover keeps (`oodSh`, Johnson/Bind/ForProver/Ood.lean) is the library's key written of a
typed OOD sample, seed and answers (`OnBytes.Slice.keyOf`, OnBytes/Slice/KeyOfRec.lean): of the
prover's typed seed and the sample map's answers at the rows' messages.

Why. On the verifier's side the library builds the description's explicit input (`ProofFile.Inst`) out of
a typed OOD sample, a seed with the answers of every row, and writes the key of it by `keyOf`: at
the full size `LPFD.Full.instanceAsPlainRecord` (Johnson/Desc/Laid/ProofFull.lean) through `LPFD.Full.instPartsOf`
(Johnson/Top/Fire/Code/Vals/FastFull.lean); at the small size, which is out of the goals' scope,
`LPFD.Small.instOf` (Johnson/Desc/Laid/ProofSmall.lean) through `LPFD.Small.instPartsOf`
(Johnson/Top/Fire/Code/Vals/FastSmall.lean). On the prover's side `xiAt`
(Johnson/Bind/ForProver/XiAt.lean) lays `oodSh`, which runs the stand-in committer's text on words.
This file says that `oodSh` is such a written key: `keyOf`, at the same reading of factors, of the
typed OOD sample `recOfIsk`.

Main names (namespace `Bind.ForProver`).
  `tableKey_ext`   two keys with the same item, answers and seeds are one.
  `recOfIsk sh Z k`   the typed OOD sample: k's typed seed, and the library's sample map
    (`OnBytes.Slice.recZ`) at that seed on the rows' messages (`msgsAt`).
  `seeds_eq_keyOf`   a spelled seed is the list of seeds that `keyOf` writes: no premise.
  **`oodSh_eq_keyOf`**   `oodSh sh Z k` is `keyOf` of `recOfIsk sh Z k`. Asked: a message has room
    for its pads (3 s ≤ l).
  `xiAt_eq_keyOf`   so the explicit input `xiAt sh Z k x` holds that written key.
    `xiIdxAt_eq_keyOf`: the same of `xiIdxAt`, at the index type `Cm.Idx`, through the reader
    `iskOfIdx`.

Limits. The key is one committed table's; which of the protocol's tables it is, the first or a copy,
is not said here. No theorem here names `instanceAsPlainRecord` or `instPartsOf`: the verifier's side writes
`keyOf` of whatever typed OOD sample stands in its input; that this sample is `recOfIsk` is not said
here. At the full size's numerals the key written of the typed OOD sample `recAt` is held against
this folder's key in Johnson/Bind/ForProver/KeyOfRecAt.lean. `recOfIsk` has no code (the cast into
the extension field): it stands in statements alone. Nothing where 3 s > l. Nothing here says that
the seeds are those of the table's name. Z is any value of `ProofFile.Pub`: nothing here says that it was
made of three public files. Nothing here says that the Lean verifier accepts anything. No
correctness of extraction, no binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index privacy; nothing
on any program. Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.XiAt
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey)
open OnBytes.Slice (NZ keyOf RecP)
open ProofFile.Honest (TableRand Weights Isk)

/-- Two keys with the same item, answers and seeds are one. -/
theorem tableKey_ext : ∀ a b : TableKey, a.item = b.item → a.record = b.record →
    a.seeds = b.seeds → a = b
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

/-- **The typed OOD sample**: the prover's typed seed, and the sample map's answers at the rows'
messages. Of k it reads the index, the coins of the item 0 alone (`k.coins 0`) and the seed
(`k.seed.1`); the number beside the seed (`k.seed.2`) is dropped. -/
noncomputable def recOfIsk (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) : RecP NZ sh.v sh.cube sh.s :=
  (k.seed.1, ((OnBytes.Slice.recZ sh.l sh.cube sh.s).rows (Fin sh.v → Bool)).val k.seed.1
    (msgsAt sh (entryOfPub Z k.index) (k.coins 0)))

/-- A spelled seed is the list of seeds that `keyOf` writes. -/
theorem seeds_eq_keyOf (sh : Bind.Twin.Shape) (r : RecP NZ sh.v sh.cube sh.s) :
    spell sh r.1 = (keyOf (fun β : NZ => β.val) r).seeds := by
  unfold spell OnBytes.K.IdTable.spellSeedL OnBytes.K.IdTable.spellSeed1 keyOf
  rw [List.map_ofFn]
  rfl

/-- **The key made of what the prover keeps is the library's key written of the typed OOD sample.**
-/
theorem oodSh_eq_keyOf (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) (h3 : 3 * sh.s ≤ sh.l) :
    oodSh sh Z k = keyOf (fun β : NZ => β.val) (recOfIsk sh Z k) := by
  refine tableKey_ext _ _ rfl ?_ (seeds_eq_keyOf sh (recOfIsk sh Z k))
  apply Array.ext'
  rw [answers_oodSh sh Z k h3]
  unfold keyOf OnBytes.K.IdTable.spellAns
  rw [Array.toList_ofFn]
  rfl

/-- So the explicit input that the builder makes holds that written key. -/
theorem xiAt_eq_keyOf (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ)) (h3 : 3 * sh.s ≤ sh.l)
    (x : ByteArray × ByteArray) :
    xiAt sh Z k x = ⟨⟨x.1, keyOf (fun β : NZ => β.val) (recOfIsk sh Z k)⟩, x.2⟩ := by
  unfold xiAt
  rw [oodSh_eq_keyOf sh Z k h3]

/-- The same at the index type `Cm.Idx`. -/
theorem xiIdxAt_eq_keyOf (sh : Bind.Twin.Shape) (Z : ProofFile.Pub)
    (k : Isk Cm.Idx (ℕ → TableRand) (Seed sh × ℕ)) (h3 : 3 * sh.s ≤ sh.l)
    (x : ByteArray × ByteArray) :
    xiIdxAt sh Z k x =
      ⟨⟨x.1, keyOf (fun β : NZ => β.val) (recOfIsk sh Z (iskOfIdx k))⟩, x.2⟩ :=
  xiAt_eq_keyOf sh Z (iskOfIdx k) h3 x

end Bind.ForProver

#print axioms Bind.ForProver.tableKey_ext
#print axioms Bind.ForProver.recOfIsk
#print axioms Bind.ForProver.seeds_eq_keyOf
#print axioms Bind.ForProver.oodSh_eq_keyOf
#print axioms Bind.ForProver.xiAt_eq_keyOf
#print axioms Bind.ForProver.xiIdxAt_eq_keyOf
