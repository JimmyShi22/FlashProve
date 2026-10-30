-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPub.lean.
The tests on the planes' matrix (Fo.planeMatAB, Fo.planeMatHB,
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneNums.lean) say yes at every record that Verify.publicOf returns.

The tests ask three things of a plan: that the lookup's shape is made of the calls (Fo.madeB); that
the planes' matrix has as many rows as a block of its tables; that it has at least as many columns
as the planes have. The first is Fo.Pub.public_made_A and Fo.Pub.public_made_H
(OnBytes/Tie/Pv/Lookup/Ends/FoMadePublic.lean) with Fo.test_of_made
(OnBytes/Tie/Pv/Lookup/Ends/FoMadeTestB.lean). The other two hold by how the plans are made:
Attention.matrices lays the matrix bA with 2 ^ lmb rows and S.kbA columns, and Attention.shapeHid
sets S.kbA to what Forest.planeCols returns; Head.matsH lays bH with 2 ^ lmbH rows and L.kb columns.

States:
  seamShape_mats, seamPlan_mats, planA_mats: the list of matrices in the attention plan is
    Attention.matrices, each matrix of another owner marked.
  matrices_bA: number NAs + 2 of that list has 2 ^ lmb rows and S.kbA columns.
  shapeHid_kbA: S.kbA is the number of columns of the planes at the shape and the configuration's
    lmb.
  planA_planeMat: Fo.planeMatAB says yes at every plan that Attention.plan returns.
  public_planeMatAB: so it does at every attention plan of a record that Verify.publicOf returns.
  planH2_kb: Head.planH2 returns only where the layout's L.kb is the number of columns of the
    planes.
  matsH_bH: number NHf + 2 of Head.matsH has 2 ^ lmbH rows and L.kb columns.
  public_planeMatHB: Fo.planeMatHB says yes at the head's plan of such a record.
Under: in each the one equation of the routine that returns (and, in public_planeMatAB, that the
plan is a member of X.A). Limits: attention and the head alone: nothing on the layers. One
direction: from a routine that returns.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneNums
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanH
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeTestB
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PlaneMat
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (cases e; done)
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

/-- A matrix of another owner, marked. -/
def markQ (M : TMat) : TMat := if M.kind == 1 then { M with foreign := some 0, ttOff := 0 } else M

theorem seamShape_mats {g : Settings} {m : Array TMat} {tau col0F ktO aO : ℕ}
    {s : Attention.Seam} (e : Attention.Seam.shape g m tau col0F ktO aO = .ok s) :
    s.tl.mats = m.map markQ := by
  unfold Attention.Seam.shape at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨tl, h0, e⟩ := bindE_ok e
  cases e
  exact (shape_mats _ _ _ _ _ _ _ h0).1

theorem seamPlan_mats {s r : Attention.Seam} {nU3 hb hbLine : ℕ}
    (e : s.plan nU3 hb hbLine = .ok r) : r.tl.mats = s.tl.mats := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, h0, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨Tp, _, e⟩ := bindE_ok e
  cases e
  exact (addTrees_keeps _ _ _ _ _ _ _ _ h0).1

/-- The list of matrices in the attention plan. -/
theorem planA_mats (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    P.mats = (Attention.matrices P.S i).map markQ := by
  unfold Attention.plan at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, hS, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, h0, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, h1, e⟩ := bindE_ok e
  cases e
  show seam.tl.mats = _
  rw [seamPlan_mats h1, seamShape_mats h0]

/-- The planes' matrix in the list. -/
theorem matrices_bA (S : Attention.Shape) (i : Attention.In) :
    (((Attention.matrices S i).map markQ).getD (S.cf.NAs + 2) {}).m = 2 ^ S.cf.lmb ∧
      (((Attention.matrices S i).map markQ).getD (S.cf.NAs + 2) {}).k = S.kbA := by
  have e : ((Attention.matrices S i).map markQ)[S.cf.NAs + 2]? =
      some (Attention.ownMatrix i "bA" (2 ^ S.cf.lmb) S.kbA (S.cf.NAs + 2) i.wpbA) := by
    unfold Attention.matrices
    simp [markQ, Attention.ownMatrix]
  rw [Array.getD_eq_getD_getElem?, e]
  exact ⟨rfl, rfl⟩

/-- The number of columns of the planes' matrix. -/
theorem shapeHid_kbA {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (e : Attention.shapeHid lid cf = .ok (S, fs)) : S.kbA = planeCols fs cf.lmb := by
  unfold Attention.shapeHid at e
  obtain ⟨A, _, e⟩ := bindE_ok e
  obtain ⟨h, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨kbA, hk, e⟩ := bindE_ok e
  dsimp only at e
  obtain ⟨counted, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  unfold Forest.planeCols at hk
  split at hk
  · cases hk
  · exact (Except.ok.inj hk).symm

/-- The test says yes at every plan that Attention.plan returns. -/
theorem planA_planeMat (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : planeMatAB P = true := by
  obtain ⟨hS, _⟩ := Pub.planA_shapeHid settings i cf P e
  have hcf : P.S.cf = cf := (Pub2.shapeOf_shapeHid hS).2
  obtain ⟨m1, m2⟩ := matrices_bA P.S i
  have hm := planA_mats settings i cf P e
  simp only [planeMatAB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨test_of_made (Pub.planA_made settings i cf P e), ?_⟩, ?_⟩
  · rw [hm, m1]
    exact Nat.div_self (Nat.pos_of_ne_zero (by positivity))
  · rw [hm, m2, shapeHid_kbA hS, hcf]

/-- **The test says yes at every attention plan of a record that publicOf returns.** -/
theorem public_planeMatAB {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (P : Attention.Plan)
    (hg : X.A[g]? = some P) : planeMatAB P = true := by
  obtain ⟨sc, lines, cf, a0, _, _, _, hp, ha, hm, _⟩ := Fo.Pub.public_A h g P hg
  have h0 := planA_planeMat _ _ _ a0 hp
  have eS : P.S = a0.S := by rw [ha]
  have eF : P.fs = a0.fs := by rw [ha]
  have eL : P.lid = a0.lid := by rw [ha]; rfl
  have eM : P.mats = a0.mats := hm
  unfold planeMatAB at h0 ⊢
  rw [eS, eF, eL, eM]
  exact h0

/-! ### the head -/

/-- The head's plan is made only where the layout's number of columns is the planes'. -/
theorem planH2_kb {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : ℕ} {hp : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : L.kb = planeCols L.fs h.lmbH := by
  unfold Head.planH2 at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨n, hk, e⟩ := bindE_ok e
  obtain ⟨_, hn, _⟩ := bindE_ok e
  have hb : (n == L.kb) = true := by
    cases hq : (n == L.kb) with
    | true => rfl
    | false =>
      rw [hq] at hn
      cases hn
  have e1 : n = L.kb := beq_iff_eq.mp hb
  unfold Forest.planeCols at hk
  split at hk
  · cases hk
  · exact e1.symm.trans (Except.ok.inj hk).symm

/-- The planes' matrix in the head's list. -/
theorem matsH_bH (h : Head.Shape) (L : Head.HL) (b : Head.Border) (gid sid : ℕ) :
    ((Head.matsH h L b gid sid).getD (h.NHf + 1 + 1) {}).m = 2 ^ h.lmbH ∧
      ((Head.matsH h L b gid sid).getD (h.NHf + 1 + 1) {}).k = L.kb := by
  have e : (Head.matsH h L b gid sid)[h.NHf + 1 + 1]? =
      some { name := "bH", m := 2 ^ h.lmbH, k := L.kb, aId := gid * 256 + (h.NHf + 1 + 1) } := by
    unfold Head.matsH
    simp
    have key : ∀ (A : List (String × ℕ × ℕ)) (a b c : String × ℕ × ℕ) (n : ℕ) (_ : A.length = n)
        (hlt : n + 1 + 1 < (A ++ [a, b, c]).length), (A ++ [a, b, c])[n + 1 + 1] = c := by
      intro A a b c n hn hlt
      subst hn
      rw [List.getElem_eq_iff, List.getElem?_append_right (by omega)]
      have h2 : A.length + 1 + 1 - A.length = 2 := by omega
      rw [h2]
      rfl
    rw [key _ _ _ _ h.NHf (by simp) _]
    exact ⟨rfl, rfl, rfl⟩
  rw [Array.getD_eq_getD_getElem?, e]
  exact ⟨rfl, rfl⟩

/-- **The test says yes at the head's plan of a record that publicOf returns.** -/
theorem public_planeMatHB {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    planeMatHB X.hS X.HLy X.H.tl.mats = true := by
  obtain ⟨H0, hp, _⟩ := Pub.public_H h
  obtain ⟨stream, _, hm, _⟩ := Pub.public_mats h
  obtain ⟨m1, m2⟩ := matsH_bH X.hS X.HLy (Verify.borderOf X.layers.y) (1 + X.layers.y.NGr)
    stream.aId
  simp only [planeMatHB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨test_of_made (Pub.public_made_H h), ?_⟩, ?_⟩
  · rw [hm, m1]
    exact Nat.div_self (Nat.pos_of_ne_zero (by positivity))
  · rw [hm, m2, planH2_kb hp]

end Fo.PlaneMat
