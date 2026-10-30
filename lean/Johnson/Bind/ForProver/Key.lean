-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/Key.lean: a committed table's key, as the linear claim's shared rounds (the
shared chain) read it (`OnBytes.TableKey`, OnBytes/Iop/Foldeq.lean), made of a table of the stand-in
committer on byte strings (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean) and a list of seeds; and
that it passes the description's tests on an explicit input's key.

Main names (namespace `Bind.ForProver`).
  `indexOf sh`   the shape as the verifier has it: the six numbers in the same order.
  `keyAt sh T sd`   the key: the statement's item 0; the committer's own OOD answers
    (`Bind.Twin.answers`) of the table T at the seeds sd, each triple of words as one element; the
    seeds sd. The type has no root: the item is the number of the statement's item that holds it.
  `ok_answers`   every word of every answer is below the prime: at every table and all seeds.
  `size_keyAt`   there are 2^v answers for each seed that is handed.
  **`keyFits_keyAt`**, `fits_keyAt`   under `SeedsFit` (Johnson/Bind/ForProver/Seeds.lean) the key's
    sizes fit the shape: the description's own test and the older one.
  **`okSeeds_keyAt`**   under `SeedsFit` the test on the seeds' words passes.
  `recordOk_keyAt`   the test on the answers' words passes: no premise.
  **`okKey_keyAt`**   under `SeedsFit` the shared rounds' test on the explicit input passes, at
    parameters whose item is 0. `okKey_p14Of`: those that are read off the planner's chains are
    such.
  `factors_keyAt`   under `SeedsFit` no factor is the triple of zeros (in the older test's
    spelling).

Limits. The key is one committed table's; which of the protocol's tables it is, the first or a copy,
is not said here. The item 0 is a session's numbering, not the link's
(Johnson/Bind/ForProver/Enc.lean, Limits, "Which item"). The order of the answers is read off the
text of `Bind.Twin.answers` (by row, within a row by seed); no theorem here states a place
(Johnson/Bind/ForProver/OodPlaces.lean does). By that text the stride is the number of seeds that
are handed: where sd has sh.s seeds the answer of row r under seed i stands at r · s + i, as the
type's own comment asks; at another number it does not, and `SeedsFit` is what rules that out. No
root, no hash function and no salt enter. Nothing here says that the seeds are those of the table's
name. These are tests on sizes and words: that a key passes them says
nothing on whether its answers are right; that they are the sample map's at seeds that spell a typed
seed is `Bind.Twin.answers_spelled` (Johnson/Bind/TwinAnswers.lean). Nothing here says that the Lean
verifier accepts anything. No correctness of extraction, no binding of the commitment (the opening
form, `BindsWith`, VerifiableInference/MoreStatements.lean), no soundness, no completeness, no index
privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.Seeds
import Johnson.Bind.TwinDom
import Johnson.Desc.K14.Blocks
import OnBytes.Maker.OkViewLaws
import OnBytes.Slice.SimBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey okE isZeroE)
open VerifiableInference.Desc.Own (seedsOk recordOk keyFits)

/-- The shape as the verifier has it. -/
def indexOf (sh : Bind.Twin.Shape) : OnBytes.Params.IndexShape :=
  ⟨⟨sh.a, sh.l, sh.r⟩, sh.v, sh.s, sh.sigma⟩

/-- The verifier asks for as many coordinates as the committer's text reads. -/
theorem cubeBits_indexOf (sh : Bind.Twin.Shape) : (indexOf sh).cubeBits = sh.cube := rfl

/-- **The key of a table at given seeds.** Total at every list of seeds. `keyFits_keyAt`,
`fits_keyAt`, `okSeeds_keyAt`, `okKey_keyAt` and `factors_keyAt` ask `SeedsFit`
(Johnson/Bind/ForProver/Seeds.lean) by name; `size_keyAt` and `recordOk_keyAt` ask nothing. -/
def keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed) : TableKey :=
  ⟨0, ((Bind.Twin.answers sh T (wordsOf sd)).map E.ofTriple).toArray, sd⟩

/-- **Every word of every answer is below the prime.** -/
theorem ok_answers (sh : Bind.Twin.Shape) (T : Bind.Twin.Table)
    (seeds : List (List Fmt.Ext × Fmt.Ext)) :
    ∀ a ∈ Bind.Twin.answers sh T seeds, Fmt.Fld.two.okE a = true := by
  intro a ha
  unfold Bind.Twin.answers at ha
  obtain ⟨b, -, hb⟩ := List.mem_flatMap.1 ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hb
  exact OnBytes.Slice.okE_addE _ _

/-- The number of answers in the key. -/
theorem size_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed) :
    (keyAt sh T sd).record.size = 2 ^ sh.v * sd.length := by
  show ((Bind.Twin.answers sh T (wordsOf sd)).map E.ofTriple).toArray.size = _
  rw [List.size_toArray, List.length_map, Bind.Twin.length_answers, length_wordsOf]

/-- **The key's sizes fit the shape**: the description's own test. -/
theorem keyFits_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed)
    (h : SeedsFit sh sd) : keyFits (keyAt sh T sd) (indexOf sh) = true := by
  rw [VerifiableInference.Desc.Own.keyFits_iff]
  refine ⟨?_, h.1, fun x hx => ?_⟩
  · rw [size_keyAt, h.1]
    rfl
  · rw [cubeBits_indexOf]
    exact (h.2 x hx).1

/-- The same of the older test. -/
theorem fits_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed)
    (h : SeedsFit sh sd) : (keyAt sh T sd).fits (indexOf sh) = true := by
  rw [← VerifiableInference.Desc.Own.keyFits_eq]
  exact keyFits_keyAt sh T sd h

/-- **The test on the seeds' words passes.** -/
theorem okSeeds_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed)
    (h : SeedsFit sh sd) : OnBytes.Maker.okSeeds (keyAt sh T sd) = true := by
  rw [OnBytes.Maker.okSeeds_iff]
  intro x hx
  exact ⟨(h.2 x hx).2.1, (h.2 x hx).2.2.1⟩

/-- **The test on the answers' words passes.** -/
theorem recordOk_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed) :
    recordOk (keyAt sh T sd) = true := by
  rw [VerifiableInference.Desc.Own.recordOk_eq]
  show (((Bind.Twin.answers sh T (wordsOf sd)).map E.ofTriple).toArray.all okE) = true
  rw [← Array.all_toList, List.toList_toArray, List.all_eq_true]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  rw [OnBytes.okE_triple, E.triple_ofTriple]
  exact ok_answers sh T _ a ha

/-- **The shared rounds' test on the explicit input passes**, at parameters whose item is 0. -/
theorem okKey_keyAt (P : Desc.K14.P14) (hP : P.item = 0) (sh : Bind.Twin.Shape)
    (T : Bind.Twin.Table) (sd : List SampleSeed) (h : SeedsFit sh sd) :
    Desc.K14.okKey P (keyAt sh T sd) = true := by
  unfold Desc.K14.okKey
  rw [VerifiableInference.Desc.Own.seedsOk_eq, okSeeds_keyAt sh T sd h, recordOk_keyAt sh T sd, hP]
  rfl

/-- The parameters that are read off the planner's chains have the item 0. -/
theorem okKey_p14Of (c : OnBytes.Model.Verify.Chains) (before : List (Nat × Nat))
    (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed) (h : SeedsFit sh sd) :
    Desc.K14.okKey (Desc.K14.p14Of c before) (keyAt sh T sd) = true :=
  okKey_keyAt _ rfl sh T sd h

/-- No factor of the key is the triple of zeros. -/
theorem factors_keyAt (sh : Bind.Twin.Shape) (T : Bind.Twin.Table) (sd : List SampleSeed)
    (h : SeedsFit sh sd) : ((keyAt sh T sd).seeds.all fun x => !isZeroE x.beta) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [(h.2 x hx).2.2.2]
  rfl

end Bind.ForProver

#print axioms Bind.ForProver.cubeBits_indexOf
#print axioms Bind.ForProver.ok_answers
#print axioms Bind.ForProver.size_keyAt
#print axioms Bind.ForProver.keyFits_keyAt
#print axioms Bind.ForProver.fits_keyAt
#print axioms Bind.ForProver.okSeeds_keyAt
#print axioms Bind.ForProver.recordOk_keyAt
#print axioms Bind.ForProver.okKey_keyAt
#print axioms Bind.ForProver.okKey_p14Of
#print axioms Bind.ForProver.factors_keyAt
#print axioms Bind.ForProver.indexOf
#print axioms Bind.ForProver.keyAt
