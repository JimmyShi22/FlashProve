-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/OodPlaces.lean: where an answer stands in the key of a committed table's
out-of-domain (OOD) sample; and that key at an index that is a matrix of digits.

Main names (namespace `Bind.ForProver`).
  `getElem?_numbered`, `getElem?_flatMap_range`   two laws on lists.
  **`answers_place`**   in the list `Bind.Twin.answers sh T seeds` (Johnson/Bind/Twin.lean) the
    answer of row r under seed number i stands at r times the number of seeds, plus i: for r below
    2^v and i below the number of seeds. It is `Bind.Twin.answerAt` at that row, that number and
    that seed.
  **`record_place`**   so in `keyAt sh T sd` (Johnson/Bind/ForProver/Key.lean), where sd has sh.s
    seeds, it stands at r · s + i: what the comment at the type's field asks (`OnBytes.TableKey`,
    OnBytes/Iop/Foldeq.lean). `place_keyAt`: the same with the seed read off the key's own field of
    seeds.
  `place_ood`   the same of `ood Z k` (Johnson/Bind/ForProver/Ood.lean): no premise on the seeds,
    since a spelled seed has sh.s of them.
  **`oodIdx Z k`**   `ood` where the index is a well-formed matrix of digits (`Cm.Idx`,
    Cm/RelBase.lean): each integer read in the field, as `enc` reads it
    (Johnson/Bind/ForProver/Enc.lean). `okSeeds_oodIdx`, `okKey_oodIdx`, `keyFits_oodIdx`: it passes
    the description's tests on an explicit input's key.

Limits. One committed table; which of the protocol's tables it is, the first or a copy, is not said
here. The item 0 is a session's numbering, not the link's (Johnson/Bind/ForProver/Enc.lean, Limits,
"Which item"). The law on places says where a value of the committer's own text
(`Bind.Twin.answerAt`) stands, not that the value is right: what the answers are is `answers_ood`
(Johnson/Bind/ForProver/Ood.lean). At a list of another length than sh.s the stride is that length,
and the type's comment is not met. `encW` has no column where the matrix does not fit the table's
rows (`rowsFit`); `ood` and `oodIdx` give a key there all the same: nothing here ties key and
columns (`columnsAndAnswersFromIndexAndCoins`, Johnson/Bind/ForProver/CommitterAt.lean, sets the two side by side). A like law
to `getElem?_flatMap_range`, at any list, stands at Johnson/RunOne/Sound/KeyMapAtFK.lean
(`getElem?_flatMap_const`); this one stands here so that the file does not import that file's cone.
`Cm.Idx` is typed at the reference sizes: at a public part of another size `oodIdx` reads a cut or a
padding of such a matrix. No correctness of extraction, no binding of the commitment (the opening
form, `BindsWith`, VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index
privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Ood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey)
open ProofFile.Honest (TableRand Weights Isk)
open VerifiableInference.Desc.Own (keyFits)

/-! ### Two laws on lists -/

/-- The member number i of a numbered list. -/
theorem getElem?_numbered {β : Type} :
    ∀ (l : List β) (c i : ℕ), (Fmt.numbered c l)[i]? = l[i]?.map fun x => (c + i, x)
  | [], _, _ => by simp [Fmt.numbered]
  | _ :: _, _, 0 => by simp [Fmt.numbered]
  | x :: l, c, i + 1 => by
    show ((c, x) :: Fmt.numbered (c + 1) l)[i + 1]? = (x :: l)[i + 1]?.map _
    rw [List.getElem?_cons_succ, List.getElem?_cons_succ, getElem?_numbered l (c + 1) i]
    have e : c + 1 + i = c + (i + 1) := by omega
    rw [e]

/-- Lists of one length k, one behind the other: member i of list r stands at r k + i. -/
theorem getElem?_flatMap_range {β : Type} (f : ℕ → List β) (k : ℕ)
    (hf : ∀ b, (f b).length = k) :
    ∀ (n r i : ℕ), r < n → i < k → ((List.range n).flatMap f)[r * k + i]? = (f r)[i]?
  | 0, r, _, hr, _ => absurd hr (Nat.not_lt_zero r)
  | n + 1, r, i, hr, hi => by
    have hlen : ((List.range n).flatMap f).length = n * k := by
      rw [Bind.Twin.length_flatMap_const f k hf, List.length_range]
    rw [List.range_succ, List.flatMap_append]
    by_cases h : r < n
    · have h2 : (r + 1) * k ≤ n * k := Nat.mul_le_mul_right k h
      rw [Nat.add_mul, Nat.one_mul] at h2
      rw [List.getElem?_append_left (by rw [hlen]; omega)]
      exact getElem?_flatMap_range f k hf n r i h hi
    · have e : r = n := by omega
      subst e
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      have e2 : r * k + i - r * k = i := by omega
      rw [e2]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ### Where an answer stands -/

/-- **The answer of row r under seed number i stands at r times the number of seeds, plus i.** -/
theorem answers_place (sh : Bind.Twin.Shape) (T : Bind.Twin.Table)
    (seeds : List (List Fmt.Ext × Fmt.Ext)) (r i : ℕ) (hr : r < 2 ^ sh.v)
    (y : List Fmt.Ext × Fmt.Ext) (hy : seeds[i]? = some y) :
    (Bind.Twin.answers sh T seeds)[r * seeds.length + i]? =
      some (Bind.Twin.answerAt sh T r i (Bind.Twin.eqTable y.1 sh.plain) y.2) := by
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hy
  unfold Bind.Twin.answers
  show ((List.range sh.rows).flatMap fun b =>
    (Fmt.numbered 0 (seeds.map fun y => (Bind.Twin.eqTable y.1 sh.plain, y.2))).map fun w =>
      Bind.Twin.answerAt sh T b w.1 w.2.1 w.2.2)[r * seeds.length + i]? = _
  rw [getElem?_flatMap_range _ seeds.length
    (fun b => by rw [List.length_map, Bind.Twin.length_numbered, List.length_map]) sh.rows r i hr
    hi]
  rw [List.getElem?_map, getElem?_numbered, List.getElem?_map, hy]
  simp only [Option.map_some, Nat.zero_add]

/-- **In the key, where there are sh.s seeds, it stands at r · s + i.** -/
theorem record_place (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed)
    (h : sd.length = sh.s) (r i : ℕ) (hr : r < 2 ^ sh.v) (y : SampleSeed)
    (hy : sd[i]? = some y) :
    (keyAt sh T sd).record[r * sh.s + i]? =
      some (E.ofTriple (Bind.Twin.answerAt sh T r i
        (Bind.Twin.eqTable (y.z.map E.triple) sh.plain) y.beta.triple)) := by
  have hw : (wordsOf sd)[i]? = some (y.z.map E.triple, y.beta.triple) := by
    unfold wordsOf
    rw [List.getElem?_map, hy]
    rfl
  show (((Bind.Twin.answers sh T (wordsOf sd)).map E.ofTriple).toArray)[r * sh.s + i]? = _
  rw [List.getElem?_toArray, List.getElem?_map, ← h, ← length_wordsOf sd,
    answers_place sh T (wordsOf sd) r i hr _ hw]
  rfl

/-- **The same with the seed read off the key itself**: so the law ties the answers and the seeds of
one key. -/
theorem place_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed)
    (h : sd.length = sh.s) (r i : ℕ) (hr : r < 2 ^ sh.v) (y : SampleSeed)
    (hy : (keyAt sh T sd).seeds[i]? = some y) :
    (keyAt sh T sd).record[r * sh.s + i]? =
      some (E.ofTriple (Bind.Twin.answerAt sh T r i
        (Bind.Twin.eqTable (y.z.map E.triple) sh.plain) y.beta.triple)) :=
  record_place sh T sd h r i hr y hy

/-- The same of `ood Z k`. -/
theorem place_ood (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed (shapeOf Z) × ℕ))
    (r i : ℕ) (hr : r < 2 ^ (shapeOf Z).v) (y : SampleSeed)
    (hy : (spell (shapeOf Z) k.seed.1)[i]? = some y) :
    (ood Z k).record[r * (shapeOf Z).s + i]? =
      some (E.ofTriple (Bind.Twin.answerAt (shapeOf Z)
        (tableOfRand (entryOfPub Z k.index) (k.coins 0)) r i
        (Bind.Twin.eqTable (y.z.map E.triple) (shapeOf Z).plain) y.beta.triple)) :=
  record_place (shapeOf Z) _ _ (fits_spell _ _).1 r i hr y hy

/-! ### The index as a matrix of digits -/

/-- **The key off the public part and what the prover keeps, the index a matrix of digits.** -/
def oodIdx (Z : ProofFile.Pub) (k : Isk Cm.Idx (ℕ → TableRand) (Seed (shapeOf Z) × ℕ)) : TableKey :=
  ood Z ⟨⟨fun y c => ((k.index.mat y c : ℤ) : Cb.Gl.F)⟩, k.coins, k.seed⟩

section
variable (Z : ProofFile.Pub) (k : Isk Cm.Idx (ℕ → TableRand) (Seed (shapeOf Z) × ℕ))

/-- The test on the seeds' words passes. -/
theorem okSeeds_oodIdx : OnBytes.Maker.okSeeds (oodIdx Z k) = true := okSeeds_ood Z _

/-- The test of the linear claim's shared rounds (the shared chain) on the explicit input passes. -/
theorem okKey_oodIdx (c : OnBytes.Model.Verify.Chains) (before : List (Nat × Nat)) :
    Desc.K14.okKey (Desc.K14.p14Of c before) (oodIdx Z k) = true := okKey_ood Z _ c before

/-- The key's sizes fit the public part's shape. -/
theorem keyFits_oodIdx : keyFits (oodIdx Z k) (linOf Z).fold.index = true := keyFits_ood Z _

end

end Bind.ForProver

#print axioms Bind.ForProver.getElem?_numbered
#print axioms Bind.ForProver.getElem?_flatMap_range
#print axioms Bind.ForProver.answers_place
#print axioms Bind.ForProver.record_place
#print axioms Bind.ForProver.place_keyAt
#print axioms Bind.ForProver.place_ood
#print axioms Bind.ForProver.okSeeds_oodIdx
#print axioms Bind.ForProver.okKey_oodIdx
#print axioms Bind.ForProver.keyFits_oodIdx
#print axioms Bind.ForProver.oodIdx
