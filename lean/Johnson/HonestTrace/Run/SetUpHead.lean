-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpHead.lean

The head's layout under another lawful final normalisation. Theorems alone; no definition.

Main theorems (on OnBytes/Model/HeadLayout.lean):
* "headLayout_norm": where "Head.layout h t" returns L, it returns the same L at the shape h with
  MF, KF, epsF set to other values. Asked: 24 ≤ MF ≤ 47, MF ≤ KF + 14, 17 ≤ KF ≤ 32 and
  1 ≤ epsF < 2^59.
* "callSizes_norm", "policy_norm", "h9_norm": three steps of "Head.layout" at the shape so set;
  "h9_norm" is stated at "Head.cellBound" alone.
* "cell_is": "Head.cellBound" is 262144, by "decide".

Limits. Conditional: no shape at which "Head.layout" returns is shown here. The file has one
"local macro", "step": a tactic alone; its text is that of a macro that is local to
Johnson/LPFPol/PublicAtPolicy.lean.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.LPFPol.PublicAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok needed_yes needed_inv)

/-- One step that is the same term, up to unfolding, in the hypothesis k and in the goal (LPFPol's own macro, which is local there). -/
local macro "step " k:ident : tactic =>
  `(tactic| (obtain ⟨a, ha, $k:ident⟩ := exc_bind $k
             refine (bind_ok ha).trans ?_
             clear ha
             try dsimp only at $k:ident
             try dsimp only))

theorem callSizes_norm (h : Head.Shape) (MF KF epsF : Nat) :
    ∀ cs : List CallD, Head.callSizes { h with MF := MF, KF := KF, epsF := epsF } cs = Head.callSizes h cs
  | [] => rfl
  | c :: cs => by
    unfold Head.callSizes
    rw [callSizes_norm h MF KF epsF cs]
    rfl

theorem policy_norm (h : Head.Shape) {MF KF epsF : Nat} {u : Unit} (k : Head.policy h = .ok u)
    (hM : 24 ≤ MF ∧ MF ≤ 47 ∧ MF ≤ KF + 14) (hK : 17 ≤ KF ∧ KF ≤ 32) (he : 1 ≤ epsF ∧ epsF < 2 ^ 59) :
    Head.policy { h with MF := MF, KF := KF, epsF := epsF } = .ok u := by
  unfold Head.policy at k ⊢
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes ?_)).trans ?_
  · show (!(decide (MF < 24) || decide (MF > 47) || decide (KF + 14 < MF))) = true
    have e1 : decide (MF < 24) = false := decide_eq_false (by omega)
    have e2 : decide (MF > 47) = false := decide_eq_false (by omega)
    have e3 : decide (KF + 14 < MF) = false := decide_eq_false (by omega)
    rw [e1, e2, e3]
    rfl
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes ?_)).trans ?_
  · show (!(decide (KF < 17) || decide (KF > 32) || decide (epsF < 1) || decide (epsF ≥ 2 ^ 59))) = true
    have e1 : decide (KF < 17) = false := decide_eq_false (by omega)
    have e2 : decide (KF > 32) = false := decide_eq_false (by omega)
    have e3 : decide (epsF < 1) = false := decide_eq_false (by omega)
    have e4 : decide (epsF ≥ 2 ^ 59) = false := decide_eq_false (by omega)
    rw [e1, e2, e3, e4]
    rfl
  step k
  step k
  step k
  exact k

theorem cell_is : Head.cellBound = 262144 := by decide

theorem h9_norm (h : Head.Shape) (L : Head.HL) {MF KF epsF : Nat} {u : Unit}
    (k : Head.h9 h L Head.cellBound = .ok u)
    (hM : 24 ≤ MF ∧ MF ≤ 47 ∧ MF ≤ KF + 14) (hK : 17 ≤ KF ∧ KF ≤ 32) :
    Head.h9 { h with MF := MF, KF := KF, epsF := epsF } L Head.cellBound = .ok u := by
  have a1 : 2 ^ MF ≤ 2 ^ 47 := Nat.pow_le_pow_right (by decide) hM.2.1
  have a2 : 2 ^ KF ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hK.2
  have a3 : 2 ^ (KF - 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have a4 : ∀ b : Bool, 2 ^ (if b = true then 38 else 29) ≤ 2 ^ 38 := by
    intro b
    cases b <;> decide
  have a5 := a4 (h.XL == 5)
  unfold Head.h9 at k ⊢
  dsimp only at k ⊢
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes (decide_eq_true ?_))).trans ?_
  · omega
  obtain ⟨_, _, k⟩ := exc_bind k
  refine (bind_ok (a := ()) (needed_yes (decide_eq_true ?_))).trans ?_
  · rw [cell_is]
    omega
  step k
  step k
  step k
  step k
  step k
  step k
  step k
  step k
  step k
  step k
  exact k

theorem headLayout_norm {h : Head.Shape} {t : Array OnBytes.F} {L : Head.HL} (k : Head.layout h t = .ok L)
    {MF KF epsF : Nat} (hM : 24 ≤ MF ∧ MF ≤ 47 ∧ MF ≤ KF + 14) (hK : 17 ≤ KF ∧ KF ≤ 32)
    (he : 1 ≤ epsF ∧ epsF < 2 ^ 59) :
    Head.layout { h with MF := MF, KF := KF, epsF := epsF } t = .ok L := by
  unfold Head.layout at k ⊢
  obtain ⟨_, a0, k⟩ := exc_bind k
  refine (bind_ok a0).trans ?_
  obtain ⟨_, a1, k⟩ := exc_bind k
  refine (bind_ok (policy_norm h a1 hM hK he)).trans ?_
  try dsimp only at k
  try dsimp only
  step k -- numbers
  step k -- callsOf
  step k -- the table's size
  obtain ⟨_, a6, k⟩ := exc_bind k
  refine (bind_ok ((callSizes_norm h MF KF epsF _).trans a6)).trans ?_
  try dsimp only at k
  try dsimp only
  step k -- Forest.shape
  step k -- the forest's depth
  step k -- planeCols
  step k -- the lines iotaH
  step k -- pubOf
  step k -- pubAsk
  step k -- the absent calls
  obtain ⟨_, a14, k⟩ := exc_bind k
  refine (bind_ok (h9_norm h _ a14 hM hK)).trans ?_
  exact k

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.headLayout_norm
