-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PansStepsT.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the batched sumcheck's panels: the steps of
the verifier's second walk over the segments (panelT, OnBytes/Model/LayerPanels.lean), segment by
segment: EACH RETURNS, and how it moves the summary of the list (Sm, PansSum.lean): a run of panels
with the selector for each of G, U, D (one panel for each layer with routed experts); one panel
each for N1, N2, QK, XR, DD and MR; nothing for eight others. Statements and proofs. General in the
sizes.

  `foldlM_cons_some`, `sm_run`   a step of a walk in Option; a run of like steps.
  `ewh_some`, `ewOf_some`       the weights of a segment that some call holds.
  `panelT_‹segment›_skip`       eight segments append nothing.
  `step_tri`, `step_norm`, `step_QK`, `step_XR`, `step_sel`   one segment's step.
  `walkT_call`                  the walk over one call's segments is the walk over its names.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A
LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, WITH ROUTED EXPERTS. Public data alone:
numbers, and whether a form IS THERE; nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.PansWalkA
import Johnson.Road.FormsKeysXR
import Johnson.Road.FormsKeysCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Panels PanelEnv panelT panelsT tri)
open OnBytes.Desc.First.K4.Total (amapM_all)
open Inst.Model.FFSeg (fams)

/-- A step of a walk in Option. -/
theorem foldlM_cons_some {α σ : Type} {f : σ → α → Option σ} {a : α} {l : List α} {s s1 : σ}
    (h : f s a = some s1) : (a :: l).foldlM f s = l.foldlM f s1 := by
  rw [List.foldlM_cons, h]
  rfl

/-- A run of like steps: each appends X places and one weight claim and leaves the walk's state. -/
theorem sm_run {y : Lay} {F : Panels → ℕ → Option Panels} {X N : ℕ}
    (hF : ∀ s pl nv wD lm, lm < N → Sm y s pl nv wD →
      ∃ s', F s lm = some s' ∧ Sm y s' (pl + X) (nv + 1) wD) :
    ∀ n, n ≤ N → ∀ s pl nv wD, Sm y s pl nv wD →
      ∃ s', (List.range n).foldlM F s = some s' ∧ Sm y s' (pl + n * X) (nv + n) wD
  | 0, _, s, pl, nv, wD, H => ⟨s, rfl, by rw [Nat.zero_mul, Nat.add_zero, Nat.add_zero]; exact H⟩
  | n + 1, hn, s, pl, nv, wD, H => by
    obtain ⟨s1, h1, H1⟩ := sm_run hF n (Nat.le_of_succ_le hn) s pl nv wD H
    obtain ⟨s2, h2, H2⟩ := hF s1 _ _ _ n (Nat.lt_of_succ_le hn) H1
    refine ⟨s2, ?_, ?_⟩
    · rw [List.range_succ, List.foldlM_append, h1]
      show ([n].foldlM F s1) = some s2
      rw [foldlM_cons_some h2]
      rfl
    · rw [Nat.succ_mul, ← Nat.add_assoc, ← Nat.add_assoc]
      exact H2

/-- The blocks' weights of a segment that some call holds are there. -/
theorem ewh_some {v : Env} {n : String} (hs : HasSeg v.y n) : ∃ wh, v.ewh n = some wh := by
  obtain ⟨q, cd, s, h⟩ := callOf_some hs
  exact ⟨_, by unfold Env.ewh; rw [h]; rfl⟩

/-- The entries' weights of a segment that some call holds are there. -/
theorem ewOf_some {v : Env} {n : String} (hs : HasSeg v.y n) : ∃ ew, v.ewOf n = some ew := by
  obtain ⟨q, cd, s, h⟩ := callOf_some hs
  exact ⟨_, by unfold Env.ewOf; rw [h]; rfl⟩

variable {p : PanelEnv}

/-- The segment N1H brings no panel in the second walk: the list stays as it is. -/
theorem panelT_N1H_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "N1H" s = some s := by
  have e : panelT p ec el "N1H" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment N2H brings no panel in the second walk: the list stays as it is. -/
theorem panelT_N2H_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "N2H" s = some s := by
  have e : panelT p ec el "N2H" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment O brings no panel in the second walk: the list stays as it is. -/
theorem panelT_O_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "O" s = some s := by
  have e : panelT p ec el "O" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment V brings no panel in the second walk: the list stays as it is. -/
theorem panelT_V_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "V" s = some s := by
  have e : panelT p ec el "V" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment QKH brings no panel in the second walk: the list stays as it is. -/
theorem panelT_QKH_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "QKH" s = some s := by
  have e : panelT p ec el "QKH" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment LR brings no panel in the second walk: the list stays as it is. -/
theorem panelT_LR_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "LR" s = some s := by
  have e : panelT p ec el "LR" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment LT brings no panel in the second walk: the list stays as it is. -/
theorem panelT_LT_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "LT" s = some s := by
  have e : panelT p ec el "LT" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- The segment CG brings no panel in the second walk: the list stays as it is. -/
theorem panelT_CG_skip (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "CG" s = some s := by
  have e : panelT p ec el "CG" s = (if !p.v.y.h.p3 then pure s else pure s) := rfl
  rw [e]
  split_ifs <;> rfl

/-- **A run of panels with the selector**, for one of the segments G, U, D. nk: the panel's columns.
hk: the down product's columns have lfe bits. -/
theorem step_tri (h3 : p.v.y.h.p3 = true) (R : PanRd p.v) (hk : ceilLog2 p.v.y.h.fe = p.v.y.lfe)
    (ec : E) (el : Array E) {sn : String} (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") {s : Panels}
    {pl nv wD : ℕ} (H : Sm p.v.y s pl nv wD) :
    ∃ s', panelT p ec el sn s = some s' ∧
      Sm p.v.y s' (pl + p.v.y.LamM * 2 ^ (ceilLog2 (max p.v.y.h.NE 1) +
        ceilLog2 (if sn = "D" then p.v.y.h.fe else p.v.y.h.d))) (nv + p.v.y.LamM) wD := by
  rw [panelT_routed p ec el sn s h3 hs]
  refine sm_run (N := p.v.y.LamM) (fun s pl nv wD lm hlm H => ?_) _ (Nat.le_refl _) s pl nv wD H
  have hxx : ∃ xx, (Array.range p.v.y.h.d).mapM
      (fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) = some xx := by
    apply some_of
    rw [amapM_all, List.all_eq_true]
    intro k2 hk2
    have hk2' : k2 < p.v.y.h.d := by simpa using hk2
    exact shA_some (R.xr_rt lm hlm) hk2'
  obtain ⟨xx, hxx⟩ := hxx
  rcases hs with rfl | rfl | rfl
  · have e : triStep p ec el "G" s lm = some (tri p.v.y ec 1 p.v.y.h.d
        ((Array.range p.v.y.h.NE).map fun e =>
          p.shownT.getD (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE) xx none
        (mulE (el.getD (2 * lm + 1) zeroE) (Model.Layer.kTM p.v.sc (p.v.lay (2 * lm + 1)) 1))
        s) := by
      unfold triStep
      dsimp only
      rw [hxx]
      rfl
    exact ⟨_, e, sm_tri H ec 1 p.v.y.h.d _ xx none _ (fun h => by cases h)⟩
  · have e : triStep p ec el "U" s lm = some (tri p.v.y ec 1 p.v.y.h.d
        ((Array.range p.v.y.h.NE).map fun e =>
          p.shownT.getD (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE) xx none
        (mulE (el.getD (2 * lm + 1) zeroE) (Model.Layer.kTM p.v.sc (p.v.lay (2 * lm + 1)) 2))
        s) := by
      unfold triStep
      dsimp only
      rw [hxx]
      rfl
    exact ⟨_, e, sm_tri H ec 1 p.v.y.h.d _ xx none _ (fun h => by cases h)⟩
  · exact ⟨_, rfl, sm_tri H ec 1 p.v.y.h.fe _ #[] (some (1 + lm)) _ (fun _ => hk)⟩

/-- **The panel of a norm's segment.** -/
theorem step_norm (hNW : p.v.y.NW = 2) (R : PanRd p.v) (ec : E) (el : Array E) {sn : String}
    (hs : sn = "N1" ∨ sn = "N2") (hseg : HasSeg p.v.y sn) {s : Panels} {pl nv wD : ℕ}
    (H : Sm p.v.y s pl nv wD) :
    ∃ s', panelT p ec el sn s = some s' ∧
      Sm p.v.y s' (pl + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 1)) nv wD := by
  obtain ⟨wh, hwh⟩ := ewh_some hseg
  rcases hs with rfl | rfl
  · rw [panelT_N1_eq, hwh]
    exact ⟨_, rfl, sm_forms H ec 1 false 1 _ _ _ (fun _ _ _ _ => rfl) fun i hi _ _ =>
      SxsA_at (R.strY (2 * i + 0) (by
        have hi' : i < p.v.y.Lam := hi
        rw [hNW]
        omega)) wh⟩
  · rw [panelT_N2_eq, hwh]
    exact ⟨_, rfl, sm_forms H ec 1 false 1 _ _ _ (fun _ _ _ _ => rfl) fun i hi _ _ =>
      SxsA_at (R.strY (2 * i + 1) (by
        have hi' : i < p.v.y.Lam := hi
        rw [hNW]
        omega)) wh⟩

/-- **The panel of the segment QK.** -/
theorem step_QK (R : PanRd p.v) (ec : E) (el : Array E) {s : Panels} {pl nv wD : ℕ}
    (H : Sm p.v.y s pl nv wD) :
    ∃ s', panelT p ec el "QK" s = some s' ∧
      Sm p.v.y s' (pl + 2 ^ (ceilLog2 p.v.y.Lam + ceilLog2 p.v.y.h.d)) (nv + p.v.y.Lam) wD := by
  rw [panelT_QK_eq]
  exact ⟨_, rfl, sm_weight H ec 1 false p.v.y.h.d _ _ fun i hi yv hyv =>
    shA_some (R.a_rt i hi) hyv⟩

/-- **The panel of the segment XR.** -/
theorem step_XR (h3 : p.v.y.h.p3 = true) (R : PanRd p.v) (ec : E) (el : Array E)
    (hseg : HasSeg p.v.y "XR") {s : Panels} {pl nv wD : ℕ} (H : Sm p.v.y s pl nv wD) :
    ∃ s', panelT p ec el "XR" s = some s' ∧
      Sm p.v.y s' (pl + 2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 1)) nv wD := by
  obtain ⟨ew, hew⟩ := ewOf_some hseg
  rw [panelT_XR_eq, h3, hew]
  exact ⟨_, rfl, sm_forms H ec 1 true 1 _ _ _ (fun _ _ _ _ => rfl) fun i hi _ _ =>
    shSum_some (R.m_rt (2 * i + 1) (R.odd i hi)) (Nat.le_refl _)⟩

/-- **The panel of one of the segments DD, MR.** -/
theorem step_sel (h3 : p.v.y.h.p3 = true) (R : PanRd p.v) (ec : E) (el : Array E) {sn : String}
    (hs : sn = "DD" ∨ sn = "MR") (hseg : HasSeg p.v.y sn) {s : Panels} {pl nv wD : ℕ}
    (H : Sm p.v.y s pl nv wD) :
    ∃ s', panelT p ec el sn s = some s' ∧
      Sm p.v.y s' (pl + 2 ^ (ceilLog2 p.v.y.LamM + ceilLog2 p.v.y.h.NE)) nv wD := by
  obtain ⟨ew, hew⟩ := ewOf_some hseg
  have hg : ∀ i, i < p.v.y.LamM → ∀ yv, yv < p.v.y.h.NE →
      (p.v.shA "lr" "rt" ((2 * i + 1) / 2) yv).isSome = true := fun i hi yv hyv =>
    shA_some (R.lr_rt ((2 * i + 1) / 2) (by omega)) hyv
  rcases hs with rfl | rfl
  · rw [panelT_DD_eq, h3, hew]
    exact ⟨_, rfl, sm_forms H ec 1 true p.v.y.h.NE _ _ _ (fun _ _ _ _ => rfl) hg⟩
  · rw [panelT_MR_eq, h3, hew]
    exact ⟨_, rfl, sm_forms H ec 1 true p.v.y.h.NE _ _ _ (fun _ _ _ _ => rfl) hg⟩

/-- The walk over one call's segments is the walk over the line's names. -/
theorem walkT_call (hN : LinesAre p.v.y) (q : Fin 8) (ec : E) (el : Array E) (s : Panels) :
    (p.v.y.calls.getD q.val default).segs.foldlM (fun s g => panelT p ec el g.name s) s =
      ((fams q).map segName).foldlM (fun s n => panelT p ec el n s) s := by
  rw [← line_at hN q, List.foldlM_map]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.foldlM_cons_some
#print axioms OnBytes.Road.K4.C.sm_run
#print axioms OnBytes.Road.K4.C.ewh_some
#print axioms OnBytes.Road.K4.C.ewOf_some
#print axioms OnBytes.Road.K4.C.panelT_N1H_skip
#print axioms OnBytes.Road.K4.C.panelT_N2H_skip
#print axioms OnBytes.Road.K4.C.panelT_O_skip
#print axioms OnBytes.Road.K4.C.panelT_V_skip
#print axioms OnBytes.Road.K4.C.panelT_QKH_skip
#print axioms OnBytes.Road.K4.C.panelT_LR_skip
#print axioms OnBytes.Road.K4.C.panelT_LT_skip
#print axioms OnBytes.Road.K4.C.panelT_CG_skip
#print axioms OnBytes.Road.K4.C.step_tri
#print axioms OnBytes.Road.K4.C.step_norm
#print axioms OnBytes.Road.K4.C.step_QK
#print axioms OnBytes.Road.K4.C.step_XR
#print axioms OnBytes.Road.K4.C.step_sel
#print axioms OnBytes.Road.K4.C.walkT_call
