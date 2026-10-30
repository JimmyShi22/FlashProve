-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/PadProved.lean: the flat function `lkPad` (OnBytes/K/Kc/FlatHear.lean) returns what the
program's routine `Model.Forest.pad` (OnBytes/Model/Look.lean) returns, in every run on a view in
which that succeeds; and with it the law of the head's whole receiving side without a hypothesis.

The proofs follow the routines' texts line by line, by the rules of OnBytes/K/Kc/Kit.lean and
OnBytes/K/Kc/HearProved.lean.

Main theorems: `lawPad`, `lawHear`. Beneath: `sim_roundsIn`, `sim_lkDraws`, `sim_lkTieStep`,
`sim_lkTie`, `sim_lkLevel`.

Not claimed. One direction alone, as in OnBytes/K/Kc/Laws.lean. Nothing on the dry run. Nothing on
soundness. The program does not import this file.
-/
import OnBytes.K.Kc.HearProved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM Aff Psc Tsc Level RoundForm)

theorem sim_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Sim (Model.roundsIn form p zs) (Fl.roundsIn form p zs) := by
  unfold Model.roundsIn Fl.roundsIn
  refine Sim.foldlM _ _ (fun s z => ?_) _ _
  refine Sim.bind (sim_roundIn _ _ _ _) fun x => ?_
  obtain ⟨r, q⟩ := x
  exact Sim.pure _

/-! ## The lookup -/

theorem sim_lkDraws (h : Model.Forest.Shape) : Sim (Model.Forest.draws h) (lkDraws h) := by
  unfold Model.Forest.draws lkDraws
  refine Sim.ite (Sim.bind (sim_answer _) fun theta => ?_) (Sim.bind (Sim.pure _) fun theta => ?_)
  · refine Sim.bind (sim_answer _) fun alpha => ?_
    exact Sim.pure _
  · refine Sim.bind (sim_answer _) fun alpha => ?_
    exact Sim.pure _

theorem sim_lkTieStep (a : E) (s : Model.Forest.TieStep) (j : Nat) :
    Sim (Model.Forest.tieStep a s j) (lkTieStep a s j) := by
  unfold Model.Forest.tieStep lkTieStep
  refine Sim.bind (sim_pscBegin _) fun p => ?_
  refine Sim.bind (sim_pscEnds p 3 _) fun x => ?_
  obtain ⟨first, p1⟩ := x
  refine Sim.bind (sim_shown _) fun vP => ?_
  refine Sim.bind (sim_shown _) fun vG => ?_
  refine Sim.ite (Sim.bind (sim_shown _) fun z => Sim.bind (Sim.pure _) fun summand => ?_)
    (Sim.bind (Sim.pure _) fun summand => ?_)
  · refine Sim.bind (sim_pscRow p1 _ _) fun x => ?_
    obtain ⟨row, p2⟩ := x
    exact Sim.pure _
  · refine Sim.bind (sim_pscRow p1 _ _) fun x => ?_
    obtain ⟨row, p2⟩ := x
    exact Sim.pure _

theorem sim_lkTie (a : E) : Sim (Model.Forest.tie a) (lkTie a) := by
  unfold Model.Forest.tie lkTie
  refine Sim.bind (Sim.foldlM _ _ (fun s j => sim_lkTieStep a s j) _ _) fun s => ?_
  refine Sim.bind (sim_point _ _) fun y => ?_
  exact Sim.pure _

theorem sim_lkLevel (s : Model.Forest.Descent) (mu : Nat) (order : List Nat) :
    Sim (Model.Forest.level s mu order) (lkLevel s mu order) := by
  unfold Model.Forest.level lkLevel
  refine Sim.bind (sim_levelIn _ _ _ _) fun o => ?_
  generalize o.handDown = x
  obtain ⟨rho, form⟩ := x
  exact Sim.pure _

/-- **The lookup's messages.** -/
theorem lawPad : LawPad := by
  intro calls pub lid
  unfold Model.Forest.pad lkPad
  refine Sim.bind (Sim.need _) fun h0 => ?_
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind sim_slot fun slot0 => ?_
  refine Sim.bind (sim_owe _) fun o1 => ?_
  refine Sim.bind (sim_owe _) fun o2 => ?_
  refine Sim.bind (sim_owe _) fun o3 => ?_
  refine Sim.bind (sim_lkDraws _) fun x => ?_
  obtain ⟨theta, alpha, a⟩ := x
  refine Sim.bind (sim_lkTie a) fun t => ?_
  refine Sim.bind (Sim.foldlM _ _ (fun s mu => sim_lkLevel s mu _) _ _) fun keys => ?_
  refine Sim.bind (Sim.foldlM _ _ (fun s l => sim_lkLevel s _ _) _ _) fun table => ?_
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (sim_pscBegin _) fun leaves => ?_
  refine Sim.bind (sim_roundsIn _ _ _) fun x => ?_
  obtain ⟨zb0, leaves1⟩ := x
  refine Sim.bind (sim_point _ _) fun y => ?_
  refine Sim.bind (sim_pscBegin _) fun bits => ?_
  refine Sim.bind (sim_roundsIn _ _ _) fun x => ?_
  obtain ⟨zb1, bits1⟩ := x
  refine Sim.bind (sim_pscEnds _ 2 1) fun x => ?_
  obtain ⟨sBit, bits2⟩ := x
  refine Sim.bind (sim_shown _) fun vBit => ?_
  refine Sim.bind (sim_pscRow _ _ _) fun x => ?_
  obtain ⟨bitsRow, bits3⟩ := x
  refine Sim.bind sim_slot fun s1 => ?_
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  refine Sim.bind (Sim.mustAs _ _) fun _ => ?_
  exact Sim.pure _

/-- **The whole receiving side of the head's check.** -/
theorem lawHear : LawHear := lawHear_of lawPad

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.lawPad
#print axioms OnBytes.K.Kc.lawHear
