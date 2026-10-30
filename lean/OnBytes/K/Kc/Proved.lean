-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/Proved.lean: the five statements of OnBytes/K/Kc/Laws.lean, proved: each flat function
of OnBytes/K/Kc/Flat.lean returns what the program's routine returns, in every run on a view in
which that routine succeeds.

The proofs follow the routines' texts line by line, by the rules of OnBytes/K/Kc/Kit.lean: first the
small routines of a sub-proof (OnBytes/Model/Hide.lean), then those of the masked sumcheck
(OnBytes/Model/Psc.lean, OnBytes/Model/Tsc.lean), then the head's five
(OnBytes/Model/HeadHeard.lean).

Main theorems: `lawPoint`, `lawSquares`, `lawProducts`, `lawStream`, `lawLogits`. Beneath them, for
whoever needs the same of another sub-proof's routines: `sim_claimsIn`, `sim_pscBegin`,
`sim_pscRound`, `sim_roundIn`, `sim_pscEnds`, `sim_pscRow`, `sim_levelIn`, `sim_tscRounds`,
`sim_tscIn`.

Not claimed. No more than the five statements say, with the limits that the head of
OnBytes/K/Kc/Laws.lean names: one direction alone; nothing on the dry run; nothing on soundness. The
program does not import this file.
-/
import OnBytes.K.Kc.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

open OnBytes.Model (Fork SubM Aff Psc Tsc Level RoundForm)

/-! ## The small routines -/

theorem sim_read (n : Nat) : Sim (SubM.read n) (Fl.read n) := Sim.lift (simB_trRead n)

theorem sim_readSum : Sim SubM.readSum Fl.readSum := Sim.lift simB_recvE

theorem sim_answer (r : Model.RoundName) : Sim (SubM.answer r) (Fl.answer r) :=
  Sim.lift (simB_trAnswer r)

theorem sim_point (r : Model.RoundName) (n : Nat) : Sim (SubM.point r n) (Fl.point r n) :=
  Sim.lift (simB_trPoint r n)

theorem sim_batch (rows : Nat) : Sim (SubM.batch rows) (Fl.batch rows) :=
  Sim.lift (simB_trBatch rows)

theorem sim_empty (r : Model.RoundName) : Sim (SubM.empty r) (Fl.empty r) :=
  Sim.lift (simB_trEmpty r)

theorem sim_takeSlots (n : Nat) : Sim (SubM.takeSlots n) (Fl.takeSlots n) := Sim.take _

theorem sim_shown (j : Nat) : Sim (SubM.shown j) (Fl.shown j) := Sim.ask _

theorem sim_publicPart (a : Aff) : Sim (SubM.publicPart a) (Fl.publicPart a) := Sim.ask _

theorem sim_claimsIn (n : Nat) : Sim (SubM.claimsIn n) (Fl.claimsIn n) := by
  unfold SubM.claimsIn Fl.claimsIn
  refine Sim.bind (sim_read n) fun v => ?_
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (sim_takeSlots n) fun j => ?_
  refine Sim.bind (Sim.change _) fun _ => ?_
  exact Sim.pure j

/-! ## The masked sumcheck -/

theorem sim_pscBeginAt (target : E) : Sim (Model.pscBeginAt target) (Fl.pscBeginAt target) := by
  unfold Model.pscBeginAt Fl.pscBeginAt
  refine Sim.bind (sim_takeSlots 1) fun first => ?_
  refine Sim.bind sim_readSum fun mu => ?_
  refine Sim.bind (sim_answer _) fun eps => ?_
  exact Sim.pure _

theorem sim_pscBegin (C : Aff) : Sim (Model.pscBegin C) (Fl.pscBegin C) := by
  unfold Model.pscBegin Fl.pscBegin
  refine Sim.bind (sim_publicPart C) fun t => ?_
  refine Sim.bind (sim_pscBeginAt t) fun p => ?_
  exact Sim.pure _

theorem sim_pscRound (p : Psc) (w : OnBytes.Psc.Weight) {draw : Blk E}
    {g : Tape → Option (E × Tape)} (hdraw : SimB draw g) :
    Sim (Model.pscRound p w draw) (Fl.pscRound p w g) := by
  unfold Model.pscRound Fl.pscRound
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (sim_read _) fun sent => ?_
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (Sim.lift hdraw) fun r => ?_
  refine Sim.bind (sim_takeSlots _) fun _ => ?_
  exact Sim.pure _

theorem sim_roundIn (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    Sim (Model.roundIn form p z degree) (Fl.roundIn form p z degree) := by
  unfold Model.roundIn Fl.roundIn
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (Sim.need _) fun w => ?_
  exact sim_pscRound p w (simB_trAnswer .pscRound)

theorem sim_pscEnds (p : Psc) (degreeInY n : Nat) :
    Sim (Model.pscEnds p degreeInY n) (Fl.pscEnds p degreeInY n) := by
  unfold Model.pscEnds Fl.pscEnds
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (sim_pscRound p _ (simB_trAnswerNotZero .pscY)) fun x => ?_
  obtain ⟨beta, p'⟩ := x
  refine Sim.bind (sim_read n) fun v => ?_
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (sim_empty _) fun _ => ?_
  refine Sim.bind (sim_takeSlots n) fun e => ?_
  refine Sim.bind (Sim.change _) fun _ => ?_
  exact Sim.pure _

theorem sim_pscRow (p : Psc) (S0 : E) (kept : Aff) :
    Sim (Model.pscRow p S0 kept) (Fl.pscRow p S0 kept) := by
  unfold Model.pscRow Fl.pscRow
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (Sim.change _) fun _ => ?_
  exact Sim.pure _

theorem sim_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    Sim (Model.levelRounds mu rho order r p) (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Model.levelRounds Fl.levelRounds
    exact Sim.pure _
  | v :: order, r, p => by
    unfold Model.levelRounds Fl.levelRounds
    refine Sim.bind (Sim.must _) fun _ => ?_
    refine Sim.bind (sim_roundIn _ _ _ _) fun x => ?_
    obtain ⟨y, p'⟩ := x
    exact sim_levelRounds mu rho order _ p'

theorem sim_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Sim (Model.levelIn mu rho C order) (Fl.levelIn mu rho C order) := by
  unfold Model.levelIn Fl.levelIn
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (sim_pscBegin C) fun p => ?_
  refine Sim.bind (sim_levelRounds mu rho order _ p) fun x => ?_
  obtain ⟨r, p1⟩ := x
  refine Sim.bind (sim_pscEnds p1 2 2) fun x => ?_
  obtain ⟨sL, p2⟩ := x
  refine Sim.bind (sim_answer _) fun tau => ?_
  refine Sim.bind (sim_shown _) fun a => ?_
  refine Sim.bind (sim_shown _) fun b => ?_
  refine Sim.bind (sim_pscRow p2 _ _) fun x => ?_
  obtain ⟨row, p3⟩ := x
  exact Sim.pure _

theorem sim_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc),
    Sim (Model.tscLoop zs r p) (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Model.tscLoop Fl.tscLoop
    exact Sim.pure _
  | z :: zs, r, p => by
    unfold Model.tscLoop Fl.tscLoop
    refine Sim.bind (sim_roundIn _ _ _ _) fun x => ?_
    obtain ⟨y, p'⟩ := x
    exact sim_tscLoop zs _ p'

theorem sim_tscRounds (P : Array E) (lt : Nat) :
    Sim (Model.tscRounds P lt) (Fl.tscRounds P lt) := by
  unfold Model.tscRounds Fl.tscRounds
  refine Sim.bind (Sim.must _) fun _ => ?_
  refine Sim.bind (sim_claimsIn 1) fun sCl => ?_
  refine Sim.bind (sim_pscBegin _) fun p => ?_
  refine Sim.bind (sim_tscLoop _ _ p) fun x => ?_
  obtain ⟨r, p'⟩ := x
  exact Sim.pure _

theorem sim_tscIn (P : Array E) (lt shown degreeInY : Nat) :
    Sim (Model.tscIn P lt shown degreeInY) (Fl.tscIn P lt shown degreeInY) := by
  unfold Model.tscIn Fl.tscIn
  refine Sim.bind (sim_tscRounds P lt) fun o => ?_
  refine Sim.bind (sim_pscEnds o.p degreeInY shown) fun x => ?_
  obtain ⟨sEnd, p⟩ := x
  exact Sim.pure _

/-! ## The head's five -/

theorem sim_shownRun (first n : Nat) :
    Sim (Model.Head.shownRun first n) (Fl.shownRun first n) := by
  unfold Model.Head.shownRun Fl.shownRun
  refine Sim.foldlM _ _ (fun a j => ?_) _ _
  refine Sim.bind (sim_shown _) fun y => ?_
  exact Sim.pure _

theorem sim_channelRounds : ∀ (n : Nat) (r : Array E) (p : Psc),
    Sim (Model.Head.channelRounds n r p) (Fl.channelRounds n r p)
  | 0, r, p => by
    unfold Model.Head.channelRounds Fl.channelRounds
    exact Sim.pure _
  | n + 1, r, p => by
    unfold Model.Head.channelRounds Fl.channelRounds
    refine Sim.bind (sim_roundIn _ _ _ _) fun x => ?_
    obtain ⟨y, p'⟩ := x
    exact sim_channelRounds n _ p'

/-- **The norm's point.** -/
theorem lawPoint : LawPoint := fun lt => sim_point .zero lt

/-- **The sums of limb products with their product layer.** -/
theorem lawSquares : LawSquares := by
  intro h PV
  unfold Model.Head.hearSquares flatSquares
  refine Sim.bind (sim_claimsIn _) fun sW => ?_
  refine Sim.bind (sim_batch _) fun gp => ?_
  refine Sim.bind (sim_levelIn _ _ _ _) fun wpl => ?_
  exact Sim.pure _

/-- **The row products with their token sumcheck.** -/
theorem lawProducts : LawProducts := by
  intro h PV
  unfold Model.Head.hearProducts flatProducts
  refine Sim.bind (sim_claimsIn _) fun sPv => ?_
  refine Sim.bind (sim_batch _) fun omV => ?_
  refine Sim.bind (sim_tscIn _ _ _ _) fun tV => ?_
  refine Sim.bind (sim_shownRun _ _) fun sh => ?_
  refine Sim.bind (sim_pscRow _ _ _) fun x => ?_
  obtain ⟨row, p⟩ := x
  exact Sim.pure _

/-- **The stream times the reciprocal.** -/
theorem lawStream : LawStream := by
  intro h zt
  unfold Model.Head.hearStream flatStream
  refine Sim.bind (sim_tscIn _ _ _ _) fun tN => ?_
  refine Sim.bind (sim_shown _) fun a => ?_
  refine Sim.bind (sim_shown _) fun b => ?_
  refine Sim.bind (sim_pscRow _ _ _) fun x => ?_
  obtain ⟨row, p⟩ := x
  exact Sim.pure _

/-- **The activations times the head's weights.** -/
theorem lawLogits : LawLogits := by
  intro h lam zt
  unfold Model.Head.hearLogits flatLogits
  refine Sim.bind (sim_tscRounds _ _) fun tH => ?_
  refine Sim.bind (sim_channelRounds _ _ _) fun x => ?_
  obtain ⟨r, p⟩ := x
  refine Sim.bind (sim_pscEnds p 2 2) fun x => ?_
  obtain ⟨sEnd, p1⟩ := x
  refine Sim.bind (sim_shown _) fun a => ?_
  refine Sim.bind (sim_shown _) fun b => ?_
  refine Sim.bind (sim_pscRow _ _ _) fun x => ?_
  obtain ⟨row, p2⟩ := x
  exact Sim.pure _

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.lawPoint
#print axioms OnBytes.K.Kc.lawSquares
#print axioms OnBytes.K.Kc.lawProducts
#print axioms OnBytes.K.Kc.lawStream
#print axioms OnBytes.K.Kc.lawLogits
