-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFirst.lean: THE FORM's HALF: **FoldFront (Johnson/Prover/Link/FormFold.lean)
AT THE FIRST STAGE, AT THE RECORD BEHIND THE BATCHING**, from named facts on the record in front of
the proximity test (TestFront).

Main names.
  TestFront p cur nxt t G i n id   A RECORD OF PREMISES on the record t in front of the test, as far
    as the first fold reads it: the group under test is there; the statement is in order (InOrder,
    Johnson/Desc/Means/Order.lean); every row that the test takes in is dense (DenseRow,
    OnBytes/Slice/BlkProxDense.lean); the plan's first two pairs of code numbers; the group's
    two codes have the first pair's numbers; the four codes at these numbers are the two stages';
    the layout's k and h are the first stage's; some member has a main row; no member is kept; the
    first fold's mask has come: a message without a main row, of 2^h mask rows under the first
    stage's mask code's number, not sampled, counting no answer, not spent, no member; three tests
    on the plan's numbers.
  batT t G row     a record, written out: THAT guardedProximityTestParts.bat RETURNS IT is not shown in this file: it
    is bat5_yes (Johnson/Prover/Link/FormBatLaws.lean), under more premises (BatOwes).
  begun_at         the test's beginning leaves a message that is no member as it was.
  foldFront_first  THE STATEMENT.

What pays what. shape: shapeFits_of_group (FormShape.lean). rowFits: rowFits_of_combine
(FormRow.lean); no kept form: combine_noKept0 (Johnson/Desc/K12/Law/BatNoKept.lean). The
group and its rows behind the beginning: GroupOk.extends, RowIn.extends, layoutOf_extends
(Johnson/Desc/Means/Keeps.lean).

Limits. TestFront IS A PREMISE HERE. Behind the link's steps: testFront_of_ran (DoorPay.lean), from
the library's facts on the link's rounds (LinkRanR), the plan's share (DoorPlan) and "in order"; at
the full size: door_full (DoorFull.lean). It was also evaluated, as far as it is Boolean, at one
made-up small example. It is a proposal for the invariant's part on form
in front of a test: the invariant itself is another file's. That the batching returns a row is a
premise here (in the library: begin_inOrder). Rows that are not dense are not served.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFold
import Johnson.Prover.Link.FormRow
import Johnson.Prover.Link.FormShape
import Johnson.Desc.Means.Order
import Johnson.Desc.K12.Law.BatNoKept
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Slice.ProxRun (DenseRow)

/-- **The carried record in front of a proximity test**, as far as the first fold reads it. The
field `fresh` says of the message number id: it is there; `mainRows = 0`; `maskRows = 2 ^ cur.h`;
its `maskCode` is i.2; `sampled = false`; `answers = 0`; `spentAsMask = false`; it is no member of
G. -/
structure TestFront (p : P12) (cur nxt : Fmt.M1.Stage) (t : T12) (G : Group) (i n : Nat × Nat)
    (id : Nat) : Prop where
  group : t.st.groups[t.g]? = some G
  order : InOrder t.st
  dense : ∀ r ∈ (runRows t.st G).toList, DenseRow r
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
  mask : t.mask = some id
  fresh : ∃ o, t.st.oracles[id]? = some o ∧ o.shape.mainRows = 0 ∧ o.shape.maskRows = 2 ^ cur.h ∧
    o.shape.maskCode = i.2 ∧ o.sampled = false ∧ o.shape.answers = 0 ∧ o.spentAsMask = false ∧
    id ∉ G.members
  stage : K12.stageOk false cur = true
  stage1 : nxt.Z.a ≤ nxt.C.a
  vars : cur.k + ceilLog2 cur.C.l ≤ 63

/-- The record that the batching's part returns where the masks come early: shown in
Johnson/Prover/Link/FormBatLaws.lean (bat5_yes), not here. -/
def batT (t : T12) (G : Group) (row : GroupRow) : T12 :=
  { t with st := begun t.st t.g G, pass := .claim row (layoutOf t.st G) }

/-- The test's beginning leaves a message that is no member as it was. -/
theorem begun_at (S : Statement) (g : Nat) (G : Group) (o : Nat) (h : o ∉ G.members) :
    (begun S g G).oracles[o]? = S.oracles[o]? := by
  show (closeLedgers S G.members.toList).oracles[o]? = _
  have hn : ¬ o ∈ G.members.toList := fun c => h (Array.mem_toList_iff.1 c)
  rw [ProxRun.closeLedgers_get]
  simp only [hn, if_false]
  cases S.oracles[o]? <;> rfl

theorem stageOk_of {s : Fmt.M1.Stage} (h : K12.stageOk false s = true) :
    2 ^ Nat.log2 s.Z.l = s.Z.l ∧ s.Z.a ≤ s.C.a ∧ s.h ≤ s.k ∧ 1 ≤ s.k ∧
      2 * s.k + 1 - s.h ≤ s.Z.l := by
  unfold K12.stageOk K12.pow2 at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true, if_false] at h
  exact ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.2, h.2.1, h.2.2⟩

/-- **FoldFront AT THE FIRST STAGE, BEHIND THE BATCHING.** x: the element that "BAT" drew. -/
theorem foldFront_first {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i n : Nat × Nat}
    {id : Nat} (H : TestFront p cur nxt t G i n id) (x : E) (row : GroupRow)
    (hc : Bat.combine (begun t.st t.g G) t.g ⟨layoutOf t.st G, runRows t.st G⟩ x = some row) :
    FoldFront p 0 cur (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n id := by
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
  obtain ⟨o, o0, o1, o2, o3, o4, o5, o6, o7⟩ := H.fresh
  have hid : (begun t.st t.g G).oracles[id]? = some o := (begun_at _ _ _ _ o7).trans o0
  have hk : row.kept = #[] := H2K.Pin.combine_noKept0 _ _ _ _ _ hc fun j => H.noKept j
  have eB : (begun t.st t.g G).codes.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩ := by
    rw [hE.codes]
    exact H.base
  have eZ : (begun t.st t.g G).codes.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩ := by
    rw [hE.codes]
    exact H.maskC
  refine ⟨rfl, ?_, H.idx1, ?_, H.mask, ?_, ?_, ?_, ?_⟩
  · unfold stageAt
    rw [H.idx0]
    rfl
  · obtain ⟨j, hj, y, hy, hy1⟩ := H.main
    obtain ⟨y', hy', ey⟩ := hE.shape _ y hy
    exact shapeFits_of_group hG' hL' hOk' ⟨i.1, i.2, cur.k, cur.h⟩ H.layK.symm H.layH.symm H.code
      H.maskCode _ _ eB eZ s4 s3 s2 s5 ⟨j, hj, y', hy', by rw [ey]; exact hy1, H.noKept j⟩
  · rw [Own.foldMaskFits_iff]
    exact ⟨o, hid, o1, o2, o3, o4, o5, o7⟩
  · unfold Ground.ok Ground.spendAsMaskL
    show ([("spendAsMask: the message is there", ((begun t.st t.g G).oracles[id]?).isSome),
      ("spendAsMask: not sampled", Ground.has (begun t.st t.g G).oracles[id]? (!·.sampled)),
      ("spendAsMask: its shape counts no answer",
        Ground.has (begun t.st t.g G).oracles[id]? (·.shape.answers == 0)),
      ("spendAsMask: not spent before",
        Ground.has (begun t.st t.g G).oracles[id]? (!·.spentAsMask))] :
        Ground.Clauses).all (·.2) = true
    rw [hid]
    simp [Ground.has, o4, o5, o6]
  · refine rowFits_of_combine hG' hL' hOk' hr' hc H.dense hk ⟨i.1, i.2, cur.k, cur.h⟩ H.layK.symm
      H.layH.symm H.code H.maskCode ?_ ?_
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

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.begun_at
#print axioms Johnson.Prover.Link.stageOk_of
#print axioms Johnson.Prover.Link.foldFront_first
