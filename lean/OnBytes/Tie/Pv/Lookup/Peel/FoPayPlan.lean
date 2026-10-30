-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPayPlan.lean.
The bounds on the rows of the planes' matrix, 5 ≤ lm ≤ kT + 5, from the success of the three kinds'
own layouts and plans.

Each of the three kinds of sub-proof calls Forest.planeCols at its own lm and its own lookup's
record where it lays out its public numbers. So where that routine returns, the two bounds hold
(Fo.Pay.planeCols_bounds).

Main names:
  `layoutLook_lm`: Layer.layoutLook y = .ok y' gives 5 ≤ y.h.lmb and y.h.lmb ≤ y'.fo.kT + 5.
  `shapeHid_lm`: Attention.shapeHid lid cf = .ok (S, fs) gives 5 ≤ cf.lmb and cf.lmb ≤ fs.kT + 5.
  `planH2_lm`: Head.planH2 g h L b O NGr lkW = .ok hp gives 5 ≤ h.lmbH and h.lmbH ≤ L.fs.kT + 5.
They serve where lm must be known before a run. The premises h5 and hlm of Fo.hcTie,
Fo.Peel.look_yesT and Fo.lookPeelFlatT stand at the record of the run;
Does not say: that the record with which a run calls Forest.pad is y'.fo, fs or L.fs; that the lm
which the run reads (y'.h.lmb, S.cf.lmb) is y.h.lmb, cf.lmb.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPayCaller
import OnBytes.Tie.Pv.Lookup.Ends.BatRows

set_option autoImplicit false

namespace Fo.Pay
open OnBytes OnBytes.Model
open Fo.BatRows (bindE_ok)

theorem layoutLook_lm {y y' : Layer.Lay} (e : Layer.layoutLook y = .ok y') :
    5 ≤ y.h.lmb ∧ y.h.lmb ≤ y'.fo.kT + 5 := by
  unfold Layer.layoutLook at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨fo, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨kbm, hk, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨pub, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact planeCols_bounds hk

theorem shapeHid_lm {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (e : Attention.shapeHid lid cf = .ok (S, fs)) : 5 ≤ cf.lmb ∧ cf.lmb ≤ fs.kT + 5 := by
  unfold Attention.shapeHid at e
  obtain ⟨A, _, e⟩ := bindE_ok e
  obtain ⟨h, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨kbA, hk, e⟩ := bindE_ok e
  dsimp only at e
  obtain ⟨counted, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact planeCols_bounds hk

theorem planH2_lm {g : Settings} {h : Head.Shape} {L : Head.HL} {b : Head.Border}
    {O : Head.Owner} {NGr lkW : ℕ} {hp : Head.HPlanH2}
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : 5 ≤ h.lmbH ∧ h.lmbH ≤ L.fs.kT + 5 := by
  unfold Head.planH2 at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨n, hk, -⟩ := bindE_ok e
  exact planeCols_bounds hk

end Fo.Pay
