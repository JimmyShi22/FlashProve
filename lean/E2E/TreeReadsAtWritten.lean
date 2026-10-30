-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TreeReadsAtWritten.lean: the property `FileWithin` (E2E/TreeReads.lean) at the library's written
rounds' data and written sizes of the full size: for the key file, the proof file and a copy's file.
By evaluations in Lean's kernel. Statements and proofs.

In plain words. For every tree that a run of one of the three protocols sends, the sampled positions
of all declared rounds that open it, repeats counted, are at most r, the number of elements of
encoding randomness of each row beneath it: over the three chains (Fiat-Shamir hash chains) of a
file, and in the proof file over all 64 requests of a batch.

The written values. Rounds' data: `writtenKFull`, `writtenPFull`
(Johnson/Flat/Dec/FitAtWritten.lean; 18,948 and 48,390 rounds) and `PV.EntryFive.dsF` (41 rounds).
Sizes, with the codes: `keyFull`, `proofSizedFull`, `writtenLink`, `recordCodes`, `recordSet`: the
parts of `writtenSized` (Johnson/Goal/Written/Made.lean).

What is shown.
  `keyOpens`, `proofOpens`: the rounds that open a tree, written out: 18 of the key file's, 45 of
    the proof file's. `same_key`, `same_proof`: they are those of the written rounds' data, chain by
    chain, and the first two chains send 6 and 11, and 83 and 11, trees.
  **`file_key`**: `FileWithin` for the key file: one run; 21 trees.
  **`file_proof`**: for the proof file: a batch of 64 requests; 98 trees.
  **`file_link`**: for a copy's file: one run; 5 trees.
  Each says: the table of the file's trees is made, that is, every sending round's trees have the
  number, the depths and the widths that the library's `layTrees` gives for the oracle messages
  which the sizes list for it; `Within`; every round that opens a tree opens a filled one; and the
  rows with more encoding randomness than reads are just those of `keySlack`, `proofSlack`, none.
  **`proof_more_breaks`**, `key_more_breaks`, `link_more_breaks`: ONE SAMPLED POSITION MORE IN ANY
    ROUND THAT OPENS A TREE MAKES `Within` FALSE.
  **`proof_65_breaks`**: at 65 requests `Within` is false: Omega's tree (number 84) is opened at 51
    positions by the batch's shared rounds and at 55 by each request's own: 51 + 64 · 55 = 3571 = r.
  `key_2_breaks`: the like for the key file's data, at 2 in the place of its one run.

NOT EVERY ROW IS FILLED. Three rows a file have more encoding randomness than reads (an entry of the
lists stands for the main rows, or the mask rows, of one oracle message; each of these is one row):
  the main row of W (proof file: tree 82, r = 3571, 55 reads; key file: tree 5, r = 98, 49 reads):
    it stands under Omega's code; W's mask rows, in the same tree, are filled;
  the fresh mask beside the folded row (tree 83, r = 152, 101 reads; tree 6, r = 146, 97 reads): it
    stands under the mask code of the split's mask message; the folded row, in the same tree, is
    filled;
  the fresh mask that the first fold of Omega's test sends itself (tree 90, r = 152, 51 reads; tree
    13, r = 146, 49 reads): THE ONE TREE OF EACH FILE WITHOUT A FILLED ROW. The round that opens it
    opens Omega's tree and the split's mask message as well, and these are filled.
Every other row of every tree has exactly as many elements of encoding randomness as there are reads
of its tree (`filled_of_not_slack`, E2E/TreeReads.lean).

Limits.
- THE THEOREMS SPEAK OF WRITTEN VALUES. That these are the rounds' data and the sizes of the IOP as
  written in Lean, at public files in scope at which its gate is open, is in
  E2E/TreeReadsAtFiles.lean.
- It speaks of the verifier's declared rounds alone: no prover, no coin and no witness occurs.
- A NEW round that opened tree 90 (13) alone, at up to 101 (97) positions, would not break `Within`.
- EVERY r HERE RESTS ON A READING: which oracle messages lie beneath a tree, and under which codes,
  is taken from E2E/TreeRows.lean's lists, and what holds these against the rounds' data is the
  number of trees, their depths and their widths alone. In a tree with main rows nothing of the mask
  rows' code is seen (44 of the proof file's 98 trees, 17 of the key file's 21, all 5 of a copy's
  file). Codes of one length differ in r. With another of the file's codes of the same length the
  property would FAIL: in the proof file at the trees 84 (r = 55 for 3571), 88 (46 for 54), 94 (51
  for 55) and 95 (41 or 44 for 55), and at tree 90 (51 reads), whose depth and width, (13, 3), also
  fit the mask codes with r = 46, 51, 55: at the first of them; in the key file at tree 13 (49
  reads; r = 41, 49, 49): at the first.
- Under which mask code tree 90 (13) stands rests on the library's `foldMaskNotice`. The library's
  verifier program receives a fold's own mask under that notice and tests that it names the stage's
  mask code (`foldMaskOk`, OnBytes/Iop/Fold.lean). Whether the decision from which `VerifierAndGoals.verify`
  is compiled asks the like was not read.
- THE COUNT IS BY TREE. The proof file's first chain sends some oracle messages again from segment
  to segment, each time in a new tree, and each of these trees is read at 219 positions. That each
  sending has encoding randomness of its own is a matter of the prover, of which nothing is said.
- OOD answers, plain parts of messages and sums hang on rows too. They are not counted here.
- 64 is a numeral here. It is the written sizes' number of requests in a batch
  (E2E/TreeReadsAtFiles.lean, `written_slots`).
- How often a run is made is no matter of this file: each run sends its own trees.
- The committed tables are not among these trees: their columns are counted in
  E2E/ReadsAtWritten.lean.
- All limits of E2E/TreeReads.lean and E2E/TreeRows.lean stand. Nothing on hiding is stated.

The statements under `Spec` may be read as part of a goal. They count as none.


-/
import E2E.TreeRows
import Johnson.Flat.Dec.FitAtWritten
import Johnson.Goal.Written.Made
import Johnson.Top.Fire.Code.Vals.EntryFive

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.TreeReads
open VerifiableInference VerifiableInference.PlanWritten VerifiableInference.Number.ByRuns
open OnBytes OnBytes.Params Johnson.G Johnson.G.MadeFree Lk6.AtPlan
open OnBytes.Maker (WholeD RDT)

/-! ## 1. The rounds that open a tree -/

/-- The key file's rounds that open a tree: how many positions each samples; the trees' numbers. -/
def keyOpens : Opens where
  first := [(49, [1]), (39, [2]), (33, [3]), (25, [4])]
  shared :=
    [(97, [6, 8]), (52, [9]), (52, [10]), (52, [11]), (49, [12]), (49, [7, 8, 13]), (49, [14]),
    (49, [15]), (39, [16])]
  second := [(49, [0, 5, 7]), (49, [17]), (49, [18]), (41, [19]), (29, [20])]
  t₁ := 6
  t₂ := 11

/-- The proof file's. -/
def proofOpens : Opens where
  first :=
    [(219, [0, 2, 3]), (219, [4, 5, 6]), (219, [7, 8, 9]), (219, [10, 11, 12]), (219, [13, 14, 15]),
    (219, [16, 17, 18]), (219, [19, 20, 21]), (219, [22, 23, 24]), (219, [25, 26, 27]),
    (219, [28, 29, 30]), (219, [31, 32, 33]), (219, [34, 35, 36]), (219, [37, 38, 39]),
    (219, [40, 41, 42]), (219, [43, 44, 45]), (219, [46, 47, 48]), (219, [49, 50, 51]),
    (219, [52, 53, 54]), (219, [55, 56, 57]), (219, [58, 59, 60]), (219, [61, 62, 63]),
    (219, [64, 65, 66]), (219, [67, 68, 69]), (219, [70, 71, 72]), (219, [73, 74, 75]), (219, [76]),
    (55, [77]), (55, [78]), (55, [79]), (46, [80]), (44, [81])]
  shared :=
    [(101, [83, 85]), (54, [86]), (54, [87]), (54, [88]), (51, [89]), (51, [84, 85, 90]),
    (51, [91]), (51, [92]), (41, [93])]
  second := [(55, [1, 82, 84]), (55, [94]), (55, [95]), (46, [96]), (44, [97])]
  t₁ := 83
  t₂ := 11

set_option maxRecDepth 1000000 in
theorem thin_key₁ : thinIs dKeyFull.ds₁ keyOpens.first = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem thin_key₂ : thinIs dKeyFull.ds₂ keyOpens.shared = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem thin_key₃ : thinIs dKeyFull.ds₃ keyOpens.second = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem thin_proof₁ : thinIs dProofFull.ds₁ proofOpens.first = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem thin_proof₂ : thinIs dProofFull.ds₂ proofOpens.shared = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem thin_proof₃ : thinIs dProofFull.ds₃ proofOpens.second = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem t_key : dKeyFull.t₁ = 6 ∧ dKeyFull.t₂ = 11 := by
  show (dKeyFull.ds₁.map (·.trees.length)).sum = 6 ∧ (dKeyFull.ds₂.map (·.trees.length)).sum = 11
  rw [sum_eq_sumE, sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem t_proof : dProofFull.t₁ = 83 ∧ dProofFull.t₂ = 11 := by
  show (dProofFull.ds₁.map (·.trees.length)).sum = 83 ∧
    (dProofFull.ds₂.map (·.trees.length)).sum = 11
  rw [sum_eq_sumE, sum_eq_sumE]
  decide +kernel

/-- The key file's written rounds' data open what `keyOpens` lists. -/
theorem same_key : SameOpens writtenKFull keyOpens := by
  rw [writtenKFull_eq]
  exact ⟨thin_key₁, thin_key₂, thin_key₃, t_key.1, t_key.2⟩

/-- The proof file's written rounds' data open what `proofOpens` lists. -/
theorem same_proof : SameOpens writtenPFull proofOpens := by
  rw [writtenPFull_eq]
  exact ⟨thin_proof₁, thin_proof₂, thin_proof₃, t_proof.1, t_proof.2⟩

/-! ## 2. The three tests -/

/-- The key file's rows with more encoding randomness than reads: the tree, the code ⟨logarithm of
the length, entries of a message, elements of encoding randomness⟩, the reads of the tree. -/
def keySlack : List (ℕ × Code × ℕ) :=
  [(5, ⟨22, 262144, 98⟩, 49), (6, ⟨13, 64, 146⟩, 97), (13, ⟨13, 64, 146⟩, 49)]

/-- The proof file's. -/
def proofSlack : List (ℕ × Code × ℕ) :=
  [(82, ⟨22, 262144, 3571⟩, 55), (83, ⟨13, 64, 152⟩, 101), (90, ⟨13, 64, 152⟩, 51)]

set_option maxRecDepth 1000000 in
theorem test_link : fileB (opensOne PV.EntryFive.dsF) 1
    (tableLink PV.EntryFive.dsF writtenLink recordCodes recordSet.samples) 5 [] = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem test_key : fileB keyOpens 1 (tableKey dKeyFull keyFull recordSet.samples) 21 keySlack =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem test_proof : fileB proofOpens 64 (tableProof dProofFull proofSizedFull recordSet.samples) 98
    proofSlack = true := by decide +kernel

/-! ## 3. The statements -/

/-- The statement of `file_key`. -/
def Spec.file_key : Prop :=
  FileWithin (opensOf writtenKFull) 1 (tableKey writtenKFull keyFull recordSet.samples) 21 keySlack

/-- At the short lists. -/
theorem short_key :
    FileWithin keyOpens 1 (tableKey writtenKFull keyFull recordSet.samples) 21 keySlack := by
  rw [writtenKFull_eq]
  exact file_of_test test_key

/-- **The key file**: one run; 21 trees. -/
theorem file_key : Spec.file_key := same_key.file short_key

/-- The statement of `file_proof`. -/
def Spec.file_proof : Prop :=
  FileWithin (opensOf writtenPFull) 64 (tableProof writtenPFull proofSizedFull recordSet.samples) 98
    proofSlack

/-- At the short lists. -/
theorem short_proof :
    FileWithin proofOpens 64 (tableProof writtenPFull proofSizedFull recordSet.samples) 98
      proofSlack := by
  rw [writtenPFull_eq]
  exact file_of_test test_proof

/-- **The proof file**: a batch of 64 requests; 98 trees. -/
theorem file_proof : Spec.file_proof := same_proof.file short_proof

/-- The statement of `file_link`. -/
def Spec.file_link : Prop :=
  FileWithin (opensOne PV.EntryFive.dsF) 1
    (tableLink PV.EntryFive.dsF writtenLink recordCodes recordSet.samples) 5 []

/-- **A copy's file**: one run; 5 trees; every row is filled. -/
theorem file_link : Spec.file_link := file_of_test test_link

/-! ## 4. It can fail -/

/-- **The proof file: one sampled position more in any round that opens a tree makes `Within`
false.** c: the chain, from 0. i: the round's number in the chain's data, from 0. -/
theorem proof_more_breaks {T : List Beneath}
    (e : tableProof writtenPFull proofSizedFull recordSet.samples = some T) (c i : ℕ)
    (p : ℕ × List ℕ) (hp : ((opensOf writtenPFull).chain c)[i]? = some p) (hne : p.2 ≠ []) :
    ¬ Within ((opensOf writtenPFull).more c i) 64 T :=
  FileWithin.more_breaks file_proof (by decide) e c i p hp hne

/-- The key file: the same. -/
theorem key_more_breaks {T : List Beneath}
    (e : tableKey writtenKFull keyFull recordSet.samples = some T) (c i : ℕ)
    (p : ℕ × List ℕ) (hp : ((opensOf writtenKFull).chain c)[i]? = some p) (hne : p.2 ≠ []) :
    ¬ Within ((opensOf writtenKFull).more c i) 1 T :=
  FileWithin.more_breaks file_key (by decide) e c i p hp hne

/-- A copy's file: the same. -/
theorem link_more_breaks {T : List Beneath}
    (e : tableLink PV.EntryFive.dsF writtenLink recordCodes recordSet.samples = some T) (c i : ℕ)
    (p : ℕ × List ℕ) (hp : ((opensOne PV.EntryFive.dsF).chain c)[i]? = some p) (hne : p.2 ≠ []) :
    ¬ Within ((opensOne PV.EntryFive.dsF).more c i) 1 T :=
  FileWithin.more_breaks file_link (by decide) e c i p hp hne

/-- **The proof file: at 65 requests `Within` is false**: by Omega's tree, number 84. -/
theorem proof_65_breaks {T : List Beneath}
    (e : tableProof writtenPFull proofSizedFull recordSet.samples = some T) :
    ¬ Within (opensOf writtenPFull) 65 T :=
  same_proof.request_breaks (j := 84) short_proof e (by decide) (by decide) (by decide) (by decide)

/-- The key file's data: at 2 in the place of the one run `Within` is false: by Omega's tree, number
7. -/
theorem key_2_breaks {T : List Beneath}
    (e : tableKey writtenKFull keyFull recordSet.samples = some T) :
    ¬ Within (opensOf writtenKFull) 2 T :=
  same_key.request_breaks (j := 7) short_key e (by decide) (by decide) (by decide) (by decide)

end AtPublicFiles.TreeReads

#print axioms AtPublicFiles.TreeReads.thin_key₁
#print axioms AtPublicFiles.TreeReads.thin_key₂
#print axioms AtPublicFiles.TreeReads.thin_key₃
#print axioms AtPublicFiles.TreeReads.thin_proof₁
#print axioms AtPublicFiles.TreeReads.thin_proof₂
#print axioms AtPublicFiles.TreeReads.thin_proof₃
#print axioms AtPublicFiles.TreeReads.t_key
#print axioms AtPublicFiles.TreeReads.t_proof
#print axioms AtPublicFiles.TreeReads.same_key
#print axioms AtPublicFiles.TreeReads.same_proof
#print axioms AtPublicFiles.TreeReads.test_link
#print axioms AtPublicFiles.TreeReads.test_key
#print axioms AtPublicFiles.TreeReads.test_proof
#print axioms AtPublicFiles.TreeReads.short_key
#print axioms AtPublicFiles.TreeReads.short_proof
#print axioms AtPublicFiles.TreeReads.file_key
#print axioms AtPublicFiles.TreeReads.file_proof
#print axioms AtPublicFiles.TreeReads.file_link
#print axioms AtPublicFiles.TreeReads.proof_more_breaks
#print axioms AtPublicFiles.TreeReads.key_more_breaks
#print axioms AtPublicFiles.TreeReads.link_more_breaks
#print axioms AtPublicFiles.TreeReads.proof_65_breaks
#print axioms AtPublicFiles.TreeReads.key_2_breaks
