-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestClaims.lean: the front's test on the open rows of the group under
a proximity test (`claimsB`, Johnson/Desc/K12/Honest/Shape/TestDoor.lean) is compared with the mark
on a group's open rows (`claimsAtB`, Johnson/Desc/Ground/Shape/Claims.lean): each gives the other
at the group under test; from the mark to the test there are two hypotheses. And what the test gives
of the rows that a proximity test takes in: they may have written-out factors, and are in order
(`DenseRow`, OnBytes/Slice/BlkProxDense.lean); of the members' sample rows among them that is a
hypothesis. General in the structure t and the group G. Four theorems, no definition. The file rests
on Claims.lean, which it imports: the mark's definition and the two theorems that prove the
comparison are there.

In the list: t is the structure inside a proximity test (`T12`, Johnson/Desc/K12/Join.lean); among
its fields are the statement `st` and the number `g` of the group under test. A group G (`Group`,
OnBytes/Iop/Ground.lean) has members (`members`: numbers of oracle messages of the statement), open
rows (`rows`) and the Bool `inRun`: its proximity test has begun. An oracle message (`Oracle`) has
sample rows (`sampleRows`). A row (`Row`) has, among its summands, terms (`terms`, each with a
tensor) and whole coefficient vectors (`forms`, each with a form, which has a list of tensors).
`claimsB t` says: group number `t.g` is there, and each of its open rows passes, at the statement
`t.st`, all clauses of the call that adds an open row (`Ground.rowL`,
Johnson/Desc/First/Base/Ground.lean). TestDoor.lean names it as the front's test; the front is the
proximity test's first part (`frontJ`, Join.lean). The mark `claimsAtB S g` says: if group number g
of the statement S is there, each of its open rows is no sample row and passes the clauses of
`Ground.rowL` that read the row's summands (`rowRestB`, Johnson/Desc/Ground/Shape/Ground.lean). It
is called a mark because it is meant to be carried along a chain of sub-protocols and not computed
anew: Claims.lean proves, function by function (`join_claims`, `addRow_claims` and others there),
that functions of First/Base/Ground.lean keep it, `admit_claims` and `elsewhere_claims` under a
further hypothesis. `DenseRow r` says of each tensor of the row's terms and of its whole coefficient
vectors: no written-out variable is named twice, each has the pair (1, 1), and the slice lies inside
its vector or no variable is written out. The rows that the test takes in are `runRows t.st G`
(OnBytes/Slice/BlkBegin.lean): the open rows of the kind plain, each member's sample rows, the open
rows of the kind generator.

  `runRows_dense`: under the three hypotheses below, every row of `runRows t.st G` is a `DenseRow`
  `open_dense`: where group number `t.g` is G and `claimsB t` passes, every open row of G is a
    `DenseRow`
  `claimsB_of_mark`: where group number `t.g` is G, no test of G has begun (`G.inRun = false`) and
    the mark passes at `t.st` and `t.g`: `claimsB t` passes. Where the group is not there the mark
    is true and `claimsB` is false
  `mark_of_claimsB`: the converse, with no other hypothesis: where `claimsB t` passes, the mark
    passes at `t.st` and `t.g`

By what. `claimsB_of_mark` is `rowsPass_of_claims`, and `mark_of_claimsB` is `claims_of_rowsPass`
(both: Claims.lean), at the statement `t.st` and the number `t.g`; their Bool is `claimsB t`
unfolded. `open_dense`: `rowL_clauses` (Johnson/Desc/First/Batch/Law/DoorTests.lean) turns a row's
pass into the propositions of `RowClauses`; of these the proof uses only the test on each term's
tensor and the test on each whole coefficient vector, rewrites them by `Own.tensorInOrder_agrees`
and `Own.formFits_agrees` (Johnson/Desc/Own/ShapesAgree.lean), and ends by `denseRow_of_tests`
(Johnson/Desc/Means/Dense.lean). `runRows_dense` unfolds `runRows`: `open_dense` for the open rows,
`mem_samples` (Johnson/Desc/Means/Order.lean) and the third hypothesis for the sample rows.

Hypotheses of `runRows_dense`. `hG`: group number `t.g` of `t.st` is G. `h`: `claimsB t` passes.
`hs`: for every member o of G and every oracle message x at the number o of `t.st`, every sample
row of x is a `DenseRow`.

Limits. That the members' sample rows are `DenseRow`s is a hypothesis of `runRows_dense`: they are
plain (`PlainRow`, OnBytes/Slice/BlkPlain.lean: no written-out factor) where the mark on sample rows
holds (`stSamplesB`, `samples_rows`, Johnson/Desc/Ground/Shape/Samples.lean), and a plain row is a
`DenseRow` (`denseRow_of_plain`, BlkProxDense.lean); this file calls none of the three. Neither
`claimsB` nor the mark ranges over the members' sample rows. That the mark, or `claimsB`, passes at
any structure is not shown here. That the mark is carried along any chain is not shown here: what
Claims.lean proves of that, and what it does not, is said in its own limits. That the front asks
`claimsB` is not stated here. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestDoor
import Johnson.Desc.Ground.Shape.Claims
import Johnson.Desc.Means.Dense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open OnBytes.Slice.ProxRun (DenseRow)

theorem claimsB_of_mark {t : T12} {G : Group} (hG : t.st.groups[t.g]? = some G)
    (hrun : G.inRun = false) (h : claimsAtB t.st t.g = true) : claimsB t = true :=
  rowsPass_of_claims hG hrun h

theorem mark_of_claimsB {t : T12} (h : claimsB t = true) : claimsAtB t.st t.g = true :=
  claims_of_rowsPass h

/-- Where `claimsB t` passes, every open row of the group under test is a `DenseRow`. -/
theorem open_dense {t : T12} {G : Group} (hG : t.st.groups[t.g]? = some G)
    (h : claimsB t = true) : ∀ r ∈ G.rows.toList, DenseRow r := by
  unfold claimsB at h
  rw [hG] at h
  have h' : ∀ row ∈ G.rows.toList, Ground.ok (Ground.rowL t.st t.g row) = true :=
    List.all_eq_true.1 h
  intro r hr
  obtain ⟨G', _, hc⟩ := K9L.rowL_clauses t.st t.g r (h' r hr)
  refine denseRow_of_tests (fun u hu => ?_) fun f hf => ⟨t.st.tableBits f.oracle .main, ?_⟩
  · rw [← Own.tensorInOrder_agrees]
    exact (hc.terms u (Array.mem_toList_iff.1 hu)).1
  · rw [← Own.formFits_agrees]
    exact (hc.forms f (Array.mem_toList_iff.1 hf)).2

/-- **Every row that the test takes in is a `DenseRow`**, where `claimsB t` passes and the members'
sample rows are. -/
theorem runRows_dense {t : T12} {G : Group} (hG : t.st.groups[t.g]? = some G)
    (h : claimsB t = true)
    (hs : ∀ o ∈ G.members.toList, ∀ x, t.st.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, DenseRow r) :
    ∀ r ∈ (runRows t.st G).toList, DenseRow r := by
  intro r hr
  unfold runRows at hr
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
  rcases hr with (c | c) | c
  · exact open_dense hG h r c.1
  · rw [← Array.foldl_toList] at c
    rcases mem_samples t.st r _ _ c with c' | ⟨o, ho, x, hx, hr''⟩
    · simp at c'
    · exact hs o ho x hx r hr''
  · exact open_dense hG h r c.1

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.claimsB_of_mark
#print axioms ProofFile.Honest.Sh.mark_of_claimsB
#print axioms ProofFile.Honest.Sh.open_dense
#print axioms ProofFile.Honest.Sh.runRows_dense
