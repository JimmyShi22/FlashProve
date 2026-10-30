--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/SpReads.lean: the declared rounds' count at ONE tree's number: the number of
the tree beneath which the split's mask message o_sp lies. Stated over the general count of
E2E/TreeReads.lean: for a tree's number, each declared round's number of sampled positions, once for
each time that the round lists that number, added up over a file's three chains (the shared chain's
rounds once, the other two chains' once for each request of a batch). That file calls the sum "the
reads of the tree" and holds it against the encoding randomness r of each row beneath the tree. Its
definitions and theorems are called; no count is defined here.

WHAT THE THEOREMS ON THE COUNT ARE: equations between two natural numbers: a sum of DECLARED numbers
of positions, repeats counted, and a code's field r. They do not speak of a run, and they do not say
"distinct". Distinct positions at a verifier over the rounds' data:
Johnson/Desc/K14/Honest/SpPoints.lean.

  beneath_sp      for all codes and shapes: where the test on the plan accepts (SpRow,
                  Johnson/Desc/K14/Honest/SpRow.lean), the general file's own function beneathOf, at
                  the two notices of "send o_omega", gives two trees, and the second has the length
                  of spCode, three words a column, and ONE row, under spCode
  spRow_written   the test accepts at the written sizes of the proof file (decide +kernel); at the
                  key file's: spRow_key (SpRow.lean)
  sp_entry_proof, sp_entry_key   in the general file's tables of the two files' trees, the entry at
                  the number 83 + 2 = 85, and 6 + 2 = 8, is one row under spCode (decide +kernel).
                  THE ENTRY's VALUE DOES NOT TELL THAT TREE FROM ANOTHER: tree 90 (13), the mask
                  that the first fold of Omega's test sends, has the same. What tells them apart is
                  the number
  **sp_reads_proof**   the proof file's written rounds' data, 64 requests: the sum at the number 85
                  IS the r of spCode: 152
  **sp_reads_key**     the key file's written rounds' data, one run: the sum at 8 IS 146
  each_of_same, sp_each_proof, sp_each_key   chain by chain, at the data: the shared chain 101 + 51
                  (97 + 49); the first chain 0; the last chain 0
  sp_who_proof, sp_who_key     the rounds that list the number, in the general file's short lists
  sp_rounds_proof, sp_rounds_key   their places in the shared chain's data: 18 and 50, in both files
  **sp_one_more_proof**, **sp_one_more_key**   IT CAN FAIL, AT THIS NUMBER: one sampled position
                  more in ANY round that lists the number, and the sum exceeds the r of spCode;
                  sp_one_more_at: so at the four rounds named

What stands beside the count, not beneath it. sp_reads_proof and sp_reads_key rest on the general
file's file_proof, file_key and filled_of_not_slack, and on the two evaluated entries. They call
neither beneath_sp nor anything of SpRow.lean but spCode. THAT THE TREE WITH THE NUMBER 85 (8) IS
o_sp's is not said in this file.

What is assumed: nothing: the theorems at numbers speak of the library's written rounds' data and
written sizes. For the PROOF file these are the data and sizes of the IOP as written in Lean, at
public files that pass two tests of the library: E2E/TreeReadsAtFiles.lean,
E2E/TreeReadsDeclared.lean, Johnson/Desc/K14/Honest/SpReadsDeclared.lean. For the KEY file no file
treats the IOP as written in Lean: sp_reads_key speaks of written values alone.
What is not claimed. That a later sub-protocol reads the positions modulo the code's length. That an
honest prover's tail has r coins. What else hangs on that row (its out-of-domain answer, the scalar
at "SPLIT", what the two proximity tests send) is not counted. Nothing on soundness or on hiding.

-/
import E2E.TreeReadsAtWritten
import Johnson.Desc.K14.Honest.SpRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Maker Johnson.G Desc.Plain
open AtPublicFiles.TreeReads
open Lk6.AtPlan (keyFull)
open VerifiableInference VerifiableInference.Number.ByRuns Johnson.G.MadeFree

/-- **What the general file's own function says lies beneath the trees of "send o_omega".** -/
theorem beneath_sp {codes : Codes} {S : LinShape} {layU layO : TreeLay}
    (hS : S.sharedSplitNeeded = true) (hO : layTrees codes (withOmega S) = some layO)
    (h : SpRow codes S layU layO) :
    ∃ B0, beneathOf codes (linMessageOmega S).toList =
      some [B0, ⟨(spCode codes S).logN, 3, [spCode codes S]⟩] := by
  obtain ⟨s0, s1, hs⟩ : ∃ s0 s1, layO.shapes.toList = [s0, s1] := by
    have hl : layO.shapes.toList.length = 2 := by rw [Array.length_toList]; exact h.twoTrees
    match hm : layO.shapes.toList, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have hs1 : s1 = oneMaskRow (spCode codes S) := by
    have e : layO.shapes[1]? = some s1 := by
      rw [← Array.getElem?_toList, hs]
      rfl
    have e2 := h.shape
    rw [Array.getD_eq_getD_getElem?, e] at e2
    exact e2
  have hsent : (linMessageOmega S).toList =
      [⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] := by
    simp [linMessageOmega, hS]
  have hO' : layTrees codes (linMessageOmega S).toList.toArray = some layO := by
    rw [Array.toArray_toList]
    exact hO
  refine ⟨⟨s0.logN, s0.mainWidth + s0.maskWidth,
    rowCodes codes ⟨S.omega, S.omegaLeafClass⟩⟩, ?_⟩
  unfold beneathOf
  rw [hO', hsent, Option.map_some, hs, hs1]
  have a0 : layO.tree[0]?.getD 0 = 0 := by
    have e := h.omegaFirst
    rwa [Array.getD_eq_getD_getElem?] at e
  have a1 : layO.tree[1]?.getD 0 = 1 := by
    have e := h.spSecond
    rwa [Array.getD_eq_getD_getElem?] at e
  simp [List.zipIdx, List.filter, a0, a1, rowCodes, h.noMain, h.oneRow, h.code, spCode,
    oneMaskRow, TreeShape.mainWidth, TreeShape.maskWidth]

/-! ## At the written sizes and rounds' data -/

open VerifiableInference.PlanWritten (proofSizedFull)

/-- The code of o_sp's row at the proof file's written sizes. -/
abbrev zProof : Code := spCode proofSizedFull.codes proofSizedFull.batch.shape

/-- The like at the key file's. -/
abbrev zKey : Code := spCode keyFull.codes keyFull.once.shape

theorem spRow_written :
    ((withU proofSizedFull.batch.shape).any
        (spRowB proofSizedFull.codes proofSizedFull.batch.shape) &&
      spTailB proofSizedFull.batch proofSizedFull.codes) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- In the table of the proof file's trees the entry number 85 is one row under o_sp's code. -/
theorem sp_entry_proof :
    ((tableProof dProofFull proofSizedFull recordSet.samples).any fun T =>
      decide (T[85]? = some ⟨zProof.logN, 3, [zProof]⟩)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- In the table of the key file's trees the entry number 8 is one row under o_sp's code. -/
theorem sp_entry_key :
    ((tableKey dKeyFull keyFull recordSet.samples).any fun T =>
      decide (T[8]? = some ⟨zKey.logN, 3, [zKey]⟩)) = true := by
  decide +kernel

/-- **The proof file's written rounds' data, 64 requests**: the rounds' numbers of sampled
positions, once for each time that a round lists the number 85, add up to the field r of spCode. -/
theorem sp_reads_proof : (opensOf writtenPFull).inBatch 64 85 = zProof.r := by
  obtain ⟨T, hT, _, hW, _, hs⟩ : FileWithin (opensOf writtenPFull) 64
      (tableProof writtenPFull proofSizedFull recordSet.samples) 98 proofSlack := file_proof
  have he := sp_entry_proof
  rw [← writtenPFull_eq, hT] at he
  simp only [Option.any_some, decide_eq_true_eq] at he
  refine filled_of_not_slack hW he (List.mem_singleton.2 rfl) ?_
  rw [hs]
  intro s hsm hh
  simp only [proofSlack, List.mem_cons, List.not_mem_nil, or_false] at hsm
  rcases hsm with rfl | rfl | rfl <;> exact absurd hh.1 (by decide)

/-- **The key file's written rounds' data, one run**: the like at the number 8. -/
theorem sp_reads_key : (opensOf writtenKFull).inBatch 1 8 = zKey.r := by
  obtain ⟨T, hT, _, hW, _, hs⟩ : FileWithin (opensOf writtenKFull) 1
      (tableKey writtenKFull keyFull recordSet.samples) 21 keySlack := file_key
  have he := sp_entry_key
  rw [← writtenKFull_eq, hT] at he
  simp only [Option.any_some, decide_eq_true_eq] at he
  refine filled_of_not_slack hW he (List.mem_singleton.2 rfl) ?_
  rw [hs]
  intro s hsm hh
  simp only [keySlack, List.mem_cons, List.not_mem_nil, or_false] at hsm
  rcases hsm with rfl | rfl | rfl <;> exact absurd hh.1 (by decide)

/-- The numbers. -/
theorem sp_numbers : (zProof.logN, zProof.ell, zProof.r) = (13, 64, 152) ∧
    (zKey.logN, zKey.ell, zKey.r) = (13, 64, 146) := by
  decide +kernel

/-- **Which rounds.** Of the rounds that list a tree (the general file's short lists, which
same_proof and same_key hold against the written rounds' data): two of the shared chain list the
number 85; none of the first chain; none of the last. -/
theorem sp_who_proof :
    proofOpens.shared.filter (·.2.contains 85) = [(101, [83, 85]), (51, [84, 85, 90])] ∧
      proofOpens.first.filter (·.2.contains 85) = [] ∧
      proofOpens.second.filter (·.2.contains 85) = [] ∧ proofOpens.t₁ + 2 = 85 := by
  decide

/-- **Which rounds**, in the key file's short lists: two of the shared chain list the number 8; none
of the first chain; none of the last. -/
theorem sp_who_key :
    keyOpens.shared.filter (·.2.contains 8) = [(97, [6, 8]), (49, [7, 8, 13])] ∧
      keyOpens.first.filter (·.2.contains 8) = [] ∧
      keyOpens.second.filter (·.2.contains 8) = [] ∧ keyOpens.t₁ + 2 = 8 := by
  decide

/-- Chain by chain, a file's data count as the short lists do. -/
theorem each_of_same {D : WholeD} {O : Opens} (h : SameOpens D O) (j : ℕ) :
    readsOn (opensOf D).shared j = readsOn O.shared j ∧
      readsOn (opensOf D).first j = readsOn O.first j ∧
      readsOn (opensOf D).second j = readsOn O.second j :=
  ⟨thinIs_readsOn h.h₂ j, thinIs_readsOn h.h₁ j, thinIs_readsOn h.h₃ j⟩

/-- **Chain by chain, at the proof file's written rounds' data.** -/
theorem sp_each_proof : readsOn (opensOf writtenPFull).shared 85 = 101 + 51 ∧
    readsOn (opensOf writtenPFull).first 85 = 0 ∧ readsOn (opensOf writtenPFull).second 85 = 0 := by
  obtain ⟨a, b, c⟩ := each_of_same same_proof 85
  exact ⟨a.trans (by decide +kernel), b.trans (by decide +kernel), c.trans (by decide +kernel)⟩

/-- **Chain by chain, at the key file's written rounds' data.** -/
theorem sp_each_key : readsOn (opensOf writtenKFull).shared 8 = 97 + 49 ∧
    readsOn (opensOf writtenKFull).first 8 = 0 ∧ readsOn (opensOf writtenKFull).second 8 = 0 := by
  obtain ⟨a, b, c⟩ := each_of_same same_key 8
  exact ⟨a.trans (by decide +kernel), b.trans (by decide +kernel), c.trans (by decide +kernel)⟩

set_option maxRecDepth 1000000 in
/-- The two rounds' places in the shared chain's written data. -/
theorem sp_rounds_proof : ((opensOf dProofFull).chain 1)[18]? = some (101, [83, 85]) ∧
    ((opensOf dProofFull).chain 1)[50]? = some (51, [84, 85, 90]) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The two rounds' places in the key file's shared chain's written data. -/
theorem sp_rounds_key : ((opensOf dKeyFull).chain 1)[18]? = some (97, [6, 8]) ∧
    ((opensOf dKeyFull).chain 1)[50]? = some (49, [7, 8, 13]) := by
  decide +kernel

/-- **It can fail, at this number**: one sampled position more in any round, of any of the three
chains, that lists the number 85, and the sum exceeds the r of spCode. -/
theorem sp_one_more_proof (c i : ℕ) (p : ℕ × List ℕ)
    (hp : ((opensOf writtenPFull).chain c)[i]? = some p) (hj : 85 ∈ p.2) :
    zProof.r < ((opensOf writtenPFull).more c i).inBatch 64 85 := by
  have h := inBatch_more (opensOf writtenPFull) (N := 64) (by decide) c i p hp 85 hj
  rw [sp_reads_proof] at h
  exact h

/-- **It can fail, at this number**: one sampled position more in any round, of any of the key
file's three chains, that lists the number 8, and the sum exceeds the r of spCode. -/
theorem sp_one_more_key (c i : ℕ) (p : ℕ × List ℕ)
    (hp : ((opensOf writtenKFull).chain c)[i]? = some p) (hj : 8 ∈ p.2) :
    zKey.r < ((opensOf writtenKFull).more c i).inBatch 1 8 := by
  have h := inBatch_more (opensOf writtenKFull) (N := 1) (by decide) c i p hp 8 hj
  rw [sp_reads_key] at h
  exact h

/-- So at the four rounds that list the number. -/
theorem sp_one_more_at :
    zProof.r < ((opensOf writtenPFull).more 1 18).inBatch 64 85 ∧
      zProof.r < ((opensOf writtenPFull).more 1 50).inBatch 64 85 ∧
      zKey.r < ((opensOf writtenKFull).more 1 18).inBatch 1 8 ∧
      zKey.r < ((opensOf writtenKFull).more 1 50).inBatch 1 8 := by
  obtain ⟨a, b⟩ := sp_rounds_proof
  obtain ⟨c, d⟩ := sp_rounds_key
  rw [← writtenPFull_eq] at a b
  rw [← writtenKFull_eq] at c d
  exact ⟨sp_one_more_proof 1 18 _ a (by decide), sp_one_more_proof 1 50 _ b (by decide),
    sp_one_more_key 1 18 _ c (by decide), sp_one_more_key 1 50 _ d (by decide)⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.beneath_sp
#print axioms Desc.K14.Honest.spRow_written
#print axioms Desc.K14.Honest.sp_entry_proof
#print axioms Desc.K14.Honest.sp_entry_key
#print axioms Desc.K14.Honest.sp_reads_proof
#print axioms Desc.K14.Honest.sp_reads_key
#print axioms Desc.K14.Honest.sp_numbers
#print axioms Desc.K14.Honest.sp_who_proof
#print axioms Desc.K14.Honest.sp_who_key
#print axioms Desc.K14.Honest.each_of_same
#print axioms Desc.K14.Honest.sp_each_proof
#print axioms Desc.K14.Honest.sp_each_key
#print axioms Desc.K14.Honest.sp_rounds_proof
#print axioms Desc.K14.Honest.sp_rounds_key
#print axioms Desc.K14.Honest.sp_one_more_proof
#print axioms Desc.K14.Honest.sp_one_more_key
#print axioms Desc.K14.Honest.sp_one_more_at
