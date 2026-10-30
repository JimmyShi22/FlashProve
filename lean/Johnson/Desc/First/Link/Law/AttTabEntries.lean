-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AttTabEntries.lean: AT AN ATTENTION SEGMENT: A TABLE OF THE VECTOR OF
READS HAS AT MOST ITS WRITTEN NUMBER OF ENTRIES: for each of the five sorts of matrix of the
smallness test's list (`Attention.matrices`, OnBytes/Model/AttentionPlan.lean): its columns times
its stretches of rows are at most the matching term of `Attention.Shape.tableElems`
(OnBytes/Model/AttentionShape.lean). GENERAL IN THE SHAPE S AND IN i: no scope, no head, no numeral,
no divisibility. GENERAL IN THE MAP φ that a planner's routine lays over the list, as long as it
keeps a matrix's rows and columns: two such maps have names in the library
(`OnBytes.Road.L5.fixed`, `Fo.PlaneMat.markQ`). Statements with their proofs. The statements are
those used for `u3_cols_att` (Att/Door/Law/K5U3Cols.lean), but for φ; the text is taken from
Johnson/Desc/First/Link/Law/K9PosAttPaid.lean, so that that file and that law's files call one text.

  `tab_own_le`, `tab_rows_le`, `tab_long_le`   arithmetic
  `att_tab_as`, `att_tab_ah`, `att_tab_ao`, `att_tab_bA`, `att_tab_qa`   the five sorts
  `held_le`   of the two segments fm and fd a call holds at most as many as it has segments
  `plan_nW`   where `Attention.plan` returns X: X.nW = X.S.tableElems: one opening of
      the planner's text, in the manner of `plan_mats` (Johnson/Road/Lane5AttLabel.lean)

What is not claimed. Nothing on where the tables lie. Nothing on soundness.

-/
import Johnson.Goal.Meaning.HidPlanSizes
import Johnson.Road.Lane5AttLabel

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks

open OnBytes OnBytes.Model
open OnBytes.Road.L5 (jp_ok bind_ok)

/-- A table with one run of rows has at most its matrix's columns. -/
theorem tab_own_le (k m : ℕ) : k * (m / m) ≤ k :=
  (Nat.mul_le_mul_left k (Nat.div_le_of_le_mul (by rw [Nat.mul_one]) : m / m ≤ 1)).trans
    (Nat.mul_one k).le

/-- f / w columns, w · T rows, runs of c rows: at most f · T / c entries. -/
theorem tab_long_le (f w T c : ℕ) : f / w * (w * T / c) ≤ f * T / c := by
  refine (Nat.mul_div_le_mul_div_assoc _ _ _).trans (Nat.div_le_div_right ?_)
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)

/-- f / w columns, w · T rows, runs of T rows: at most f entries. -/
theorem tab_rows_le (f w T : ℕ) : f / w * (w * T / T) ≤ f :=
  (tab_long_le f w T T).trans (Nat.div_le_of_le_mul (by rw [Nat.mul_comm]))

section
variable (φ : TMat → TMat) (hm : ∀ M, (φ M).m = M.m) (hk : ∀ M, (φ M).k = M.k)
  (S : Attention.Shape) (i : Attention.In)
include hm hk

theorem tail_at (j : ℕ) (M : TMat)
    (hM : (#[Attention.ownMatrix i "ah" (S.cf.wcH * S.T) (S.fillH / S.cf.wcH) S.cf.NAs i.wph,
      Attention.ownMatrix i "ao" (S.cf.wcO * S.T) (S.fillO / S.cf.wcO) (S.cf.NAs + 1) i.wpo,
      Attention.ownMatrix i "bA" (2 ^ S.cf.lmb) S.kbA (S.cf.NAs + 2) i.wpbA,
      { name := "qa", m := S.cf.wcQ * S.T, k := S.fillQ / S.cf.wcQ, kind := 1, foreign := some 0,
        aId := i.midQ, wp := i.wpq }] : Array TMat)[j]? = some M) :
    (((Attention.matrices S i).map φ).getD (S.cf.NAs + j) {}).m = M.m ∧
      (((Attention.matrices S i).map φ).getD (S.cf.NAs + j) {}).k = M.k := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, _root_.Meaning.matrices_tail, hM]
  exact ⟨hm M, hk M⟩

theorem att_tab_as {q : ℕ} (hq : q < S.cf.NAs) :
    (((Attention.matrices S i).map φ).getD q {}).k *
      ((((Attention.matrices S i).map φ).getD q {}).m / 2 ^ S.cf.lmS) ≤ S.kAs / S.cf.NAs := by
  have e : ((Attention.matrices S i).map φ).getD q {} =
      φ (Attention.ownMatrix i ("as" ++ toString q) (2 ^ S.cf.lmS) (S.kAs / S.cf.NAs) q
        i.wpS) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    unfold Attention.matrices
    rw [Array.getElem?_append_left (by simpa using hq)]
    simp [hq]
  rw [e, hm, hk]
  exact tab_own_le _ _

theorem att_tab_ah :
    (((Attention.matrices S i).map φ).getD S.cf.NAs {}).k *
      ((((Attention.matrices S i).map φ).getD S.cf.NAs {}).m / S.T) ≤ S.fillH := by
  obtain ⟨e1, e2⟩ := tail_at φ hm hk S i 0 _ rfl
  rw [Nat.add_zero] at e1 e2
  rw [e1, e2]
  exact tab_rows_le _ _ _

theorem att_tab_ao :
    (((Attention.matrices S i).map φ).getD (S.cf.NAs + 1) {}).k *
      ((((Attention.matrices S i).map φ).getD (S.cf.NAs + 1) {}).m / 2 ^ S.cf.la) ≤
      S.fillO * S.T / 2 ^ S.cf.la := by
  obtain ⟨e1, e2⟩ := tail_at φ hm hk S i 1 _ rfl
  rw [e1, e2]
  exact tab_long_le _ _ _ _

theorem att_tab_bA :
    (((Attention.matrices S i).map φ).getD (S.cf.NAs + 2) {}).k *
      ((((Attention.matrices S i).map φ).getD (S.cf.NAs + 2) {}).m / 2 ^ S.cf.lmb) ≤ S.kbA := by
  obtain ⟨e1, e2⟩ := tail_at φ hm hk S i 2 _ rfl
  rw [e1, e2]
  exact tab_own_le _ _

theorem att_tab_qa :
    (((Attention.matrices S i).map φ).getD (S.cf.NAs + 3) {}).k *
      ((((Attention.matrices S i).map φ).getD (S.cf.NAs + 3) {}).m / 2 ^ S.cf.la) ≤
      S.fillQ * S.T / 2 ^ S.cf.la := by
  obtain ⟨e1, e2⟩ := tail_at φ hm hk S i 3 _ rfl
  rw [e1, e2]
  exact tab_long_le _ _ _ _

end

/-- Of the two segments fm and fd a call holds at most as many as it has segments. -/
theorem held_le (c : Attention.ACall) :
    ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length ≤
      c.segs.length := by
  have hn : ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).Nodup :=
    List.Nodup.filter _ (by decide)
  refine (List.subperm_of_subset hn fun s hs => ?_).length_le
  exact List.contains_iff_mem.1 (List.mem_filter.1 hs).2

/-- The plan's length of the third vector is the shape's number of the tables' entries. -/
theorem plan_nW {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings i cf = Except.ok X) :
    X.nW = X.S.tableElems := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam0, h0, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam, h1, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  rfl

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.tab_own_le
#print axioms VerifiableInference.Desc.K9Asks.tab_long_le
#print axioms VerifiableInference.Desc.K9Asks.tab_rows_le
#print axioms VerifiableInference.Desc.K9Asks.tail_at
#print axioms VerifiableInference.Desc.K9Asks.att_tab_as
#print axioms VerifiableInference.Desc.K9Asks.att_tab_ah
#print axioms VerifiableInference.Desc.K9Asks.att_tab_ao
#print axioms VerifiableInference.Desc.K9Asks.att_tab_bA
#print axioms VerifiableInference.Desc.K9Asks.att_tab_qa
#print axioms VerifiableInference.Desc.K9Asks.held_le
#print axioms VerifiableInference.Desc.K9Asks.plan_nW
