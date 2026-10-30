-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/OwnFoldFirst.lean: what is asked in front of a fold that sends its own fresh
mask table (`FoldFrontOwn`, Johnson/Desc/K12/Honest/OwnFold.lean) at the first stage, at the
structure behind the batching: from named facts on the structure in front of the proximity test.
The form for a mask that has come earlier is `foldFront_first`
(Johnson/Prover/Link/FormFirst.lean), whose proof is followed step by step.

Main names.
  `TestFrontOwn p cur nxt t G i n`   premises on the structure t in front of the test, as far as
      such a first fold reads it: the clauses of `TestFront` (FormFirst.lean) but for the two on a
      mask that has come; instead: no message is named as the mask; statement and book count the
      same number of oracle messages. One clause asks more than `TestFront`'s: `plain`, no row
      that the test takes in has a written-out factor, where `TestFront` asks `dense` (`DenseRow`,
      OnBytes/Slice/BlkProxDense.lean), which follows from it (`denseRow_of_plain`, there).
  `begun_size`   the test's beginning leaves the number of oracle messages.
  **`foldFrontOwn_first`**   the statement, at `batT` (FormFirst.lean).

Limits. `TestFrontOwn` is a premise: it is shown here of no structure.
Its clause `plain` excludes a test
that takes in a row with a written-out factor. Its clause `order` speaks of every group of the
statement, also of those that an earlier test of the same chain has left. That the batching's part
returns `batT` is `bat5_yes_own` (Johnson/Desc/K12/Honest/OwnFoldDoor.lean), under more premises.
That the batching returns a row is a premise here. Nothing on completeness, on soundness or on what
is hidden.
-/
import Johnson.Desc.K12.Honest.OwnFold
import Johnson.Prover.Link.FormFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link

/-- **The structure in front of a proximity test whose first fold sends its own fresh table**, as
far as that fold reads it. -/
structure TestFrontOwn (p : P12) (cur nxt : Fmt.M1.Stage) (t : T12) (G : Group) (i n : Nat × Nat) :
    Prop where
  group : t.st.groups[t.g]? = some G
  order : InOrder t.st
  plain : ∀ r ∈ (runRows t.st G).toList, PlainRow r
  idx0 : p.idx[0]? = some i
  idx1 : p.idx[1]? = some n
  code : G.code = i.1
  maskCode : G.maskCode = i.2
  base : t.st.codes.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩
  maskC : t.st.codes.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩
  base1 : t.st.codes.base[n.1]? = some ⟨nxt.C.a, nxt.C.l, nxt.C.r⟩
  mask1 : t.st.codes.mask[n.2]? = some ⟨nxt.Z.a, nxt.Z.l, nxt.Z.r⟩
  layK : (layoutOf t.st G).k = cur.k
  layH : (layoutOf t.st G).h = cur.h
  main : ∃ j < G.members.size, ∃ x, t.st.oracles[G.members.getD j noId]? = some x ∧
    0 < x.shape.mainRows
  noKept : ∀ j, G.kept.getD j false = false
  mask : t.mask = none
  inStep : t.st.oracles.size = t.book.place.size
  stage : K12.stageOk false cur = true
  stage1 : nxt.Z.a ≤ nxt.C.a
  vars : cur.k + ceilLog2 cur.C.l ≤ 63

/-- The test's beginning leaves the number of oracle messages. -/
theorem begun_size (S : Statement) (g : Nat) (G : Group) :
    (begun S g G).oracles.size = S.oracles.size :=
  ProxRun.closeLedgers_size _ _

/-- **`FoldFrontOwn` at the first stage, behind the batching.** x: the element that "BAT" sampled.
-/
theorem foldFrontOwn_first {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group}
    {i n : Nat × Nat} (H : TestFrontOwn p cur nxt t G i n) (x : E) (row : GroupRow)
    (hc : Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ x = some row) :
    FoldFrontOwn p 0 cur (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n := by
  have hE := extends_begun t.st t.g G
  have hG' := begun_group t.st t.g G H.group
  have hOk := H.order.groups t.g G H.group
  have hOk' : GroupOk (begun t.st t.g G) { G with inRun := true, rows := #[] } :=
    hOk.extends hE rfl rfl rfl rfl
  have hL' : (begun t.st t.g G).layout t.g = some (layoutOf t.st G) := by
    rw [layout_eq _ t.g _ hG',
      layoutOf_extends (G' := { G with inRun := true, rows := #[] }) hE hOk rfl rfl rfl rfl]
  have hr' : ∀ r ∈ (runRows t.st G).toList,
      RowIn (begun t.st t.g G) { G with inRun := true, rows := #[] } r :=
    fun r h => RowIn.extends (G := G) hE (fun _ c => c) (H.order.runRows t.g G H.group r h)
  obtain ⟨s1, s2, s3, s4, s5⟩ := stageOk_of H.stage
  have hk : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hc fun j => H.noKept j
  have eB : (begun t.st t.g G).codes.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩ := by
    rw [hE.codes]
    exact H.base
  have eZ : (begun t.st t.g G).codes.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩ := by
    rw [hE.codes]
    exact H.maskC
  refine ⟨rfl, ?_, H.idx1, ?_, H.mask, (begun_size _ _ _).trans H.inStep, ?_, ?_⟩
  · unfold stageAt
    rw [H.idx0]
    rfl
  · obtain ⟨j, hj, y, hy, hy1⟩ := H.main
    obtain ⟨y', hy', ey⟩ := hE.shape _ y hy
    exact shapeFits_of_group hG' hL' hOk' ⟨i.1, i.2, cur.k, cur.h⟩ H.layK.symm H.layH.symm H.code
      H.maskCode _ _ eB eZ s4 s3 s2 s5 ⟨j, hj, y', hy', by rw [ey]; exact hy1, H.noKept j⟩
  · refine rowFits_of_combine hG' hL' hOk' hr' hc
      (fun r hr => OnBytes.Slice.ProxRun.denseRow_of_plain (H.plain r hr)) hk
      ⟨i.1, i.2, cur.k, cur.h⟩ H.layK.symm H.layH.symm H.code H.maskCode ?_ ?_
    · have e : (layoutOf t.st G).logEll = ceilLog2 cur.C.l := by
        show (t.st.codes.base.getD G.code default).logEll = _
        rw [H.code, Array.getD_eq_getD_getElem?, H.base]
        rfl
      rw [H.layK, e]
      exact H.vars
    · show ((begun t.st t.g G).codes.mask.getD i.2 default).ell =
        2 ^ ceilLog2 ((begun t.st t.g G).codes.mask.getD i.2 default).ell
      rw [Array.getD_eq_getD_getElem?, eZ]
      show cur.Z.l = 2 ^ ceilLog2 cur.Z.l
      rw [← s1, ceilLog2_two_pow]
  · unfold Ground.ok Ground.newGroupL Ground.groupL
    show ([("newGroup: the main code is there", ((begun t.st t.g G).codes.base[n.1]?).isSome),
      ("newGroup: the mask code is there", ((begun t.st t.g G).codes.mask[n.2]?).isSome),
      ("newGroup: the mask code is not longer than the main",
        Ground.has (begun t.st t.g G).codes.base[n.1]? fun c =>
          Ground.has (begun t.st t.g G).codes.mask[n.2]? fun z => decide (z.logN ≤ c.logN))] :
        Ground.Clauses).all (·.2) = true
    rw [hE.codes, H.base1, H.mask1]
    simp [Ground.has, H.stage1]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.begun_size
#print axioms ProofFile.Honest.K12.foldFrontOwn_first
#print axioms ProofFile.Honest.K12.TestFrontOwn
