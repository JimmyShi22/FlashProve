-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicAMats.lean.
The attention plans of a record that Verify.publicOf returns: their list of matrices, their
configuration and their shape, tied to the functions that make them.

Fo.Pub.public_A (OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean) says from which calls a member of X.A
comes. This file draws what a user of Attention.matrices, Attention.shapeHid and the configuration's
numbers needs of it.

States:
  public_A_mats: the plan's list of matrices is Attention.matrices at the plan's shape and at the
    written record of what the plan gets besides (Attention.inOf …), each matrix of another owner
    marked (Fo.PlaneMat.markQ, which keeps rows and columns).
  matrices_size: Attention.matrices has NAs + 4 members.
  public_A_box: so that list has NAs + 4 members, and each has at most Fo.Pub2.boxR rows and
    Fo.Pub2.boxC columns of the plan's own list (OnBytes/Tie/Pv/Lookup/Ends/FoBox.lean). markQ_mk:
    the mark keeps rows and columns.
  public_A_shapeHid: Attention.shapeHid at the settings' cap on a tree's depth and at the plan's own
    configuration returns the plan's shape and its record of the lookup.
  public_A_cf (by fill_nums): three numbers of the configuration are the parameter file's: NAs, S,
    rx.
  config_NAs, public_A_NAs: NAs is not 0: Attention.config refuses it.
Under: in each statement on a plan: Verify.publicOf's equation and that the plan is a member of X.A;
nothing else.
Limits. That S is 12 and rx is 8 does not follow: they are lines of the parameter file.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub
import OnBytes.Tie.Pv.Lookup.Ends.FoBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PubA
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo Fo.PlaneMat Fo.Pub2

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **The plan's list of matrices.** -/
theorem public_A_mats (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    a.seam.tl.mats = (Attention.matrices a.S (Attention.inOf X.P.settings X.layers.y (Pub.midQ
        X.layers.y g) g)).map markQ := by
  obtain ⟨_, _, cf, a0, _, _, _, hp, ha, hm, _⟩ := Pub.public_A h g a hg
  have eS : a.S = a0.S := by rw [ha]
  rw [hm, eS]
  exact planA_mats _ _ _ a0 hp

theorem matrices_size (S : Attention.Shape) (i : Attention.In) :
    (Attention.matrices S i).size = S.cf.NAs + 4 := by
  unfold Attention.matrices
  simp

theorem markQ_mk (M : TMat) : (markQ M).m = M.m ∧ (markQ M).k = M.k := by
  unfold markQ
  split <;> exact ⟨rfl, rfl⟩

/-- **The list's size, and its members inside the box of the plan's own list.** -/
theorem public_A_box (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    (Attention.matrices a.S (Attention.inOf X.P.settings X.layers.y (Pub.midQ X.layers.y g) g)).size
        = a.S.cf.NAs + 4 ∧
      ∀ M ∈ Attention.matrices a.S (Attention.inOf X.P.settings X.layers.y (Pub.midQ X.layers.y g)
          g),
        M.m ≤ boxR a.seam.tl.mats ∧ M.k ≤ boxC a.seam.tl.mats := by
  refine ⟨matrices_size _ _, fun M hM => ?_⟩
  have hq : markQ M ∈ a.seam.tl.mats.toList := by
    rw [public_A_mats h g a hg, Array.toList_map]
    exact List.mem_map_of_mem (Array.mem_toList_iff.mpr hM)
  obtain ⟨e1, e2⟩ := markQ_mk M
  exact ⟨e1 ▸ le_boxR hq, e2 ▸ le_boxC hq⟩

/-- **The shape's equation at the plan's own configuration.** -/
theorem public_A_shapeHid (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ)
    (a : Attention.Plan) (hg : X.A[g]? = some a) :
    Attention.shapeHid X.P.settings.lidb a.S.cf = .ok (a.S, a.fs) := by
  obtain ⟨_, _, cf, a0, _, _, _, hp, ha, _, _⟩ := Pub.public_A h g a hg
  have eS : a.S = a0.S := by rw [ha]
  have eF : a.fs = a0.fs := by rw [ha]
  obtain ⟨hS, _⟩ := Pub.planA_shapeHid _ _ cf a0 hp
  rw [eS, eF, (Pub2.shapeOf_shapeHid hS).2]
  exact hS

theorem fill_nums {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {lines : List Attention.Line}
    {g : ℕ} {cf : Attention.Cfg} (e : Attention.fill P y s lines g = .ok cf) :
    cf.NAs = P.h.NAs ∧ cf.S = P.h.Sx ∧ cf.rx = P.h.rx := by
  unfold Attention.fill at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj e
  exact ⟨rfl, rfl, rfl⟩

/-- **Three numbers of the configuration are the parameter file's.** -/
theorem public_A_cf (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    a.S.cf.NAs = X.P.h.NAs ∧ a.S.cf.S = X.P.h.Sx ∧ a.S.cf.rx = X.P.h.rx := by
  obtain ⟨_, _, cf, a0, _, _, hf, hp, ha, _, _⟩ := Pub.public_A h g a hg
  have eS : a.S = a0.S := by rw [ha]
  obtain ⟨hS, _⟩ := Pub.planA_shapeHid _ _ cf a0 hp
  rw [eS, (Pub2.shapeOf_shapeHid hS).2]
  exact fill_nums hf

theorem config_NAs {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : ℕ → ℕ}
    {c : Attention.Config} (h : Attention.config P y s mq = .ok c) : 0 < P.h.NAs := by
  unfold Attention.config at h
  obtain ⟨lines, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, hr, _⟩ := bindE_ok h
  by_contra hn
  have h0 : P.h.NAs = 0 := by omega
  simp [refuseIf, h0] at hr

/-- **The number of parts of the matrix `as` is not 0.** -/
theorem public_A_NAs (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : 0 < a.S.cf.NAs := by
  rw [(public_A_cf h g a hg).1]
  obtain ⟨_, _, _, _, _, sc, A0, seen, _, k3, _, k7⟩ := Pub.publicOf_cut pol KL layout X h
  rcases k3 with ⟨_, c, k9, _⟩ | ⟨_, rfl⟩
  · exact config_NAs k9
  · rw [k7] at hg
    simp at hg

end

end Fo.PubA
