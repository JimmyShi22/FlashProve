-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FoldParts.lean: the three tests in front of the fold of a segment's closing (K10),
on a record and its `BaseData` (Johnson/Desc/K10/Honest/Base.lean), from plain facts on the statement in front of the
closing. No run, no head.

  `main_of_shapes`   a group that holds a written list's members, where the list has a member that is not kept, has a member
                     with a main row that is not kept
  `shape_of_parts`   the test on the fold's shape, at the statement behind the beginning of the test
  `mask_of_parts`    the test on the fresh mask and the test on its being spent, at that statement

Limits. Every fact on the statement is a premise here.
-/
import Johnson.Desc.K10.Honest.Base
import Johnson.Prover.Link.FormFirst
import Johnson.Desc.First.Close.Law.LayoutOfShapes
import Johnson.Desc.Means.Entry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Rec ShapesAre)
open ProofFile.Honest.K10.YesFree (BaseData)

/-- A group that holds a written list's members has a member with a main row that is not kept, where the list has a
member that is not kept. -/
theorem main_of_shapes {T : Statement} {G : Group} {lo : List (OracleShape × Nat)} {kb : Fin lo.length → Bool}
    {no : Fin lo.length → Nat} (H : ShapesAre T G lo kb no)
    (hk : ((VerifiableInference.Desc.First.Close.membersOf lo).any fun i => !kb i) = true) :
    ∃ i < G.members.size, ∃ x, T.oracles[G.members.getD i noId]? = some x ∧ 0 < x.shape.mainRows ∧
      G.kept.getD i false = false := by
  obtain ⟨i, hi, ki⟩ := List.any_eq_true.1 hk
  obtain ⟨j, hj, ej⟩ := List.getElem_of_mem hi
  have mi : (lo.get i).1.mainRows ≠ 0 := by
    unfold VerifiableInference.Desc.First.Close.membersOf at hi
    simpa using hi
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.1 (H.shape i hi)
  refine ⟨j, by rw [H.size]; exact hj, x, ?_, ?_, ?_⟩
  · rw [H.member hj, ej]
    exact hx
  · rw [ex]
    exact Nat.pos_of_ne_zero mi
  · have e : G.kept[j]? = some (kb i) := by
      rw [← Array.getElem?_toList, H.kept, List.getElem?_map, List.getElem?_eq_getElem hj, ej]
      rfl
    rw [Array.getD_eq_getD_getElem?, e]
    simpa using ki

/-- **The test on the fold's shape, from plain facts on the statement in front of the closing.** -/
theorem shape_of_parts {s : Rec} {B : BaseData} (hG : s.st.groups[s.frame.group]? = some B.G)
    (hOk : GroupOk s.st B.G) (hcode : B.G.code = s.frame.shape.code)
    (hmask : B.G.maskCode = s.frame.shape.maskCode)
    (hkh : (Own.layoutOf s.st B.G).k = B.Gq.k ∧ (Own.layoutOf s.st B.G).h = B.Gq.h) (cd zk : Code)
    (hb : s.st.codes.base[s.frame.shape.code]? = some cd)
    (hz : s.st.codes.mask[s.frame.shape.maskCode]? = some zk)
    (n1 : 1 ≤ B.Gq.k) (n2 : B.Gq.h ≤ B.Gq.k) (n3 : zk.logN ≤ cd.logN)
    (n4 : 2 * B.Gq.k + 1 - B.Gq.h ≤ zk.ell)
    (hmain : ∃ i < B.G.members.size, ∃ x, s.st.oracles[B.G.members.getD i noId]? = some x ∧
      0 < x.shape.mainRows ∧ B.G.kept.getD i false = false) :
    Own.foldShapeFits (B.S1 s) (B.F s) = true := by
  have hE := extends_begun s.st s.frame.group B.G
  have hG' := OnBytes.Means.begun_group s.st s.frame.group B.G hG
  have hOk' : GroupOk (B.S1 s) { B.G with inRun := true, rows := #[] } :=
    hOk.extends hE rfl rfl rfl rfl
  have eL := YesFree.layoutOf_same hG
  have hL' : (B.S1 s).layout s.frame.group = some (Own.layoutOf s.st B.G) := by
    show (Slice.begun s.st s.frame.group B.G).layout s.frame.group = _
    rw [layout_eq _ _ _ hG', eL,
      layoutOf_extends (G' := { B.G with inRun := true, rows := #[] }) hE hOk rfl rfl rfl rfl]
  obtain ⟨i, hi, x, hx, hp, hk⟩ := hmain
  obtain ⟨x', hx', ex⟩ := hE.shape _ _ hx
  exact Johnson.Prover.Link.shapeFits_of_group hG' hL' hOk'
    { code := s.frame.shape.code, maskCode := s.frame.shape.maskCode, k := B.Gq.k, h := B.Gq.h }
    hkh.1.symm hkh.2.symm hcode hmask cd zk (by rw [hE.codes]; exact hb) (by rw [hE.codes]; exact hz) n1 n2 n3 n4
    ⟨i, hi, x', hx', by rw [ex]; exact hp, hk⟩

/-- **The test on the fresh mask and the test on its being spent, from plain facts on the statement in front of the
closing.** -/
theorem mask_of_parts {s : Rec} {B : BaseData} {x : OnBytes.Oracle} (hG : s.st.groups[s.frame.group]? = some B.G)
    (hS : SampledMembers s.st) (hx : s.st.oracles[B.m]? = some x) (m0 : x.shape.mainRows = 0)
    (m1 : x.shape.maskRows = 2 ^ B.Gq.h) (m2 : x.shape.maskCode = s.frame.shape.maskCode)
    (m3 : x.shape.answers = 0)
    (hfresh : ∀ y, s.st.oracles[B.m]? = some y → y.sampled = false ∧ y.spentAsMask = false) :
    Own.foldMaskFits (B.S1 s) (B.F s) B.m = true ∧
      Ground.ok (Ground.spendAsMaskL (B.S1 s) B.m) = true := by
  have hno : B.m ∉ B.G.members := fun c => by
    obtain ⟨y, hy, e⟩ := hS _ _ hG _ (Array.mem_toList_iff.2 c)
    have := (hfresh y hy).1
    rw [e] at this
    cases this
  have hat : (B.S1 s).oracles[B.m]? = some x :=
    (Johnson.Prover.Link.begun_at s.st s.frame.group B.G B.m hno).trans hx
  obtain ⟨f1, f2⟩ := hfresh x hx
  constructor
  · rw [Own.foldMaskFits_iff]
    exact ⟨x, hat, m0, m1, m2, f1, m3, hno⟩
  · simp only [Ground.ok, Ground.spendAsMaskL, hat]
    simp [Ground.has, f1, f2, m3]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.main_of_shapes
#print axioms ProofFile.Honest.K10.shape_of_parts
#print axioms ProofFile.Honest.K10.mask_of_parts
