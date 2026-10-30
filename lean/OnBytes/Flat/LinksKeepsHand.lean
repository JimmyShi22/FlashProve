-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksKeepsHand.lean: the blocks and routines below the model's links for which "leaves
the two flags of a run as they are" is shown by hand.

The walk of OnBytes/Flat/LinksKeepsTool.lean goes through a routine's text. It does not go through a
block that is written as a function of the context, nor through a routine that calls itself. This
file has a theorem for each of these that the links of a proof's first chain reach, under the name
by which the walk finds it: `OnBytes.Flat.KeepsOf` ++ the routine's name.

 1. Blocks written as functions of the context (OnBytes/Iop/Ground.lean), and the three routines by
    which a sub-proof's check reads or changes its own state (OnBytes/Model/Hide.lean).
 2. Routines that call themselves: by induction, the step by the walk.
 3. Between them, by the walk alone: the routines that those of point 2 call.

Not claimed: anything on what a routine decides. For proofs only; no module of the program imports
this file.


-/
import OnBytes.Flat.LinksKeepsTool
import OnBytes.Model.VerifyLinks

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- Closes `Blk.Keeps b` for a block that is unfolded to a function of the context: by cases. -/
local macro "by_cases_of_the_text " h:ident : tactic => `(tactic| (
  repeat' (split at $h:ident)
  all_goals first
    | (cases $h:ident; exact ⟨rfl, rfl⟩)
    | (cases $h:ident; done)))

/-! ## Blocks written as functions of the context -/

theorem KeepsOf.OnBytes.Blk.lastEntry : Over.K Blk.lastEntry := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.lastEntry at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.check (name : String) (b : Bool) : Over.K (Blk.check name b) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.check at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.testOnView (f : Unit → Bool) (name : String) :
    Over.K (Blk.testOnView f name) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.testOnView at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.checkOnView (name : String) (f : Unit → Bool) :
    Over.K (Blk.checkOnView name f) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.checkOnView at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.requireRows (rows : Nat) : Over.K (Blk.requireRows rows) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.requireRows at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.handOver : Over.K Blk.handOver := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

theorem KeepsOf.OnBytes.Blk.takeColumns (t : Tree) (xs : Array Nat) :
    Over.K (Blk.takeColumns t xs) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.takeColumns at h
  dsimp only at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.readStored (t : Fmt.Stored) (pos : Positions) :
    Over.K (Blk.readStored t pos) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.readStored at h
  dsimp only at h
  by_cases_of_the_text h

theorem KeepsOf.OnBytes.Blk.named {α : Type} (name : String) (b : Blk α) (hb : Over.K b) :
    Over.K (Blk.named name b) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.named at h
  split at h
  · cases h
  · next x hx =>
    cases h
    exact hb c a c' hx

theorem KeepsOf.OnBytes.Blk.inPlace {α : Type} (place : String) (b : Blk α) (hb : Over.K b) :
    Over.K (Blk.inPlace place b) := by
  intro c a c' h
  unfold _root_.OnBytes.Blk.inPlace at h
  split at h
  · cases h
  · next x hx =>
    cases h
    exact hb c a c' hx

/-! ## A sub-proof's check reads or changes its own state -/

theorem KeepsOf.OnBytes.Model.SubM.ask {α : Type} (f : Fork → Option α) :
    Over.K (SubM.ask f) := by
  intro F c x c' h
  unfold _root_.OnBytes.Model.SubM.ask at h
  cases hf : f F with
  | none =>
    rw [hf] at h
    cases h
  | some a =>
    rw [hf] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem KeepsOf.OnBytes.Model.SubM.change (f : Fork → Option Fork) :
    Over.K (SubM.change f) := by
  intro F c x c' h
  unfold _root_.OnBytes.Model.SubM.change at h
  cases hf : f F with
  | none =>
    rw [hf] at h
    cases h
  | some a =>
    rw [hf] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem KeepsOf.OnBytes.Model.SubM.take {α : Type} (f : Fork → Option (α × Fork)) :
    Over.K (SubM.take f) := by
  intro F c x c' h
  unfold _root_.OnBytes.Model.SubM.take at h
  cases hf : f F with
  | none =>
    rw [hf] at h
    cases h
  | some a =>
    rw [hf] at h
    cases h
    exact ⟨rfl, rfl⟩

/-! ## Routines that call themselves -/

theorem KeepsOf.OnBytes.Blk.recvEsInto (n : Nat) (acc : Array E) :
    Over.K (Blk.recvEsInto n acc) := by
  induction n generalizing acc with
  | zero => unfold _root_.OnBytes.Blk.recvEsInto; keeps
  | succ n ih => unfold _root_.OnBytes.Blk.recvEsInto; keeps

theorem KeepsOf.OnBytes.Blk.takeMasksInto (o n : Nat) (acc : Array Nat) :
    Over.K (Blk.takeMasksInto o n acc) := by
  induction n generalizing acc with
  | zero => unfold _root_.OnBytes.Blk.takeMasksInto; keeps
  | succ n ih => unfold _root_.OnBytes.Blk.takeMasksInto; keeps

theorem KeepsOf.OnBytes.Blk.openTreesInto (B : TreeBook) (pos : Positions) (ts : List Nat)
    (acc : Array (Nat × Array Nat × Array (Array F))) :
    Over.K (Blk.openTreesInto B pos ts acc) := by
  induction ts generalizing acc with
  | nil => unfold _root_.OnBytes.Blk.openTreesInto; keeps
  | cons t ts ih => unfold _root_.OnBytes.Blk.openTreesInto; keeps

theorem KeepsOf.OnBytes.foldRounds (n : Nat) (claim : E) : Over.K (foldRounds n claim) := by
  induction n generalizing claim with
  | zero => unfold _root_.OnBytes.foldRounds; keeps
  | succ n ih => unfold _root_.OnBytes.foldRounds; keeps

theorem KeepsOf.OnBytes.Model.trReadLoop (n : Nat) (a : Array E) :
    Over.K (trReadLoop n a) := by
  induction n generalizing a with
  | zero => unfold _root_.OnBytes.Model.trReadLoop; keeps
  | succ n ih => unfold _root_.OnBytes.Model.trReadLoop; keeps

/-! ### `OnBytes.Model.roundIn`, and what its text reaches -/

theorem KeepsOf.OnBytes.Model.SubM.get {α : Type} (x : Option α) :
    Over.K (OnBytes.Model.SubM.get x) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.must (b : Bool) :
    Over.K (OnBytes.Model.SubM.must b) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.takeSlots (n : Nat) :
    Over.K (OnBytes.Model.SubM.takeSlots n) := by
  keeps

theorem KeepsOf.OnBytes.Model.closeAs (name : String) (kind : Fmt.Kind)
    (elems notZero entries : Nat) :
    Over.K (OnBytes.Model.closeAs name kind elems notZero entries) := by
  keeps

theorem KeepsOf.OnBytes.Model.oneOf (d : Fmt.Drawn) :
    Over.K (OnBytes.Model.oneOf d) := by
  keeps

theorem KeepsOf.OnBytes.Model.refuse {α : Type} (name : String) :
    Over.K (OnBytes.Model.refuse (α := α) name) := by
  keeps

theorem KeepsOf.OnBytes.Model.trRead (n : Nat) :
    Over.K (OnBytes.Model.trRead n) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.read (n : Nat) :
    Over.K (OnBytes.Model.SubM.read n) := by
  keeps

theorem KeepsOf.OnBytes.Model.mustAs (name : String) (b : Bool) :
    Over.K (OnBytes.Model.mustAs name b) := by
  keeps

theorem KeepsOf.OnBytes.Model.noBatching (r : OnBytes.Model.RoundName) :
    Over.K (OnBytes.Model.noBatching r) := by
  keeps

theorem KeepsOf.OnBytes.Model.pscRound (p : OnBytes.Model.Psc) (w : OnBytes.Psc.Weight)
    (draw : OnBytes.Blk OnBytes.E) (h : Over.K draw) :
    Over.K (OnBytes.Model.pscRound p w draw) := by
  keeps

theorem KeepsOf.OnBytes.Model.trAnswer (r : OnBytes.Model.RoundName) :
    Over.K (OnBytes.Model.trAnswer r) := by
  keeps

theorem KeepsOf.OnBytes.Model.roundDraw :
    Over.K OnBytes.Model.roundDraw := by
  keeps

theorem KeepsOf.OnBytes.Model.roundIn (form : OnBytes.Model.RoundForm)
    (p : OnBytes.Model.Psc) (z : OnBytes.E := OnBytes.zeroE) (degree : Nat := 0) :
    Over.K (OnBytes.Model.roundIn form p z degree) := by
  keeps

theorem KeepsOf.OnBytes.Model.levelRounds (mu : Nat) (rho : Array E) (order : List Nat)
    (r : Array E) (p : Psc) : Over.K (levelRounds mu rho order r p) := by
  induction order generalizing r p with
  | nil => unfold _root_.OnBytes.Model.levelRounds; keeps
  | cons v order ih => unfold _root_.OnBytes.Model.levelRounds; keeps

theorem KeepsOf.OnBytes.Model.tscLoop (zs : List E) (r : Array E) (p : Psc) :
    Over.K (tscLoop zs r p) := by
  induction zs generalizing r p with
  | nil => unfold _root_.OnBytes.Model.tscLoop; keeps
  | cons z zs ih => unfold _root_.OnBytes.Model.tscLoop; keeps

theorem KeepsOf.OnBytes.Model.wsForkRounds (n : Nat) (rm : Array E) (p : Psc) :
    Over.K (wsForkRounds n rm p) := by
  induction n generalizing rm p with
  | zero => unfold _root_.OnBytes.Model.wsForkRounds; keeps
  | succ n ih => unfold _root_.OnBytes.Model.wsForkRounds; keeps

theorem KeepsOf.OnBytes.Model.Head.channelRounds (n : Nat) (r : Array E) (p : Psc) :
    Over.K (Head.channelRounds n r p) := by
  induction n generalizing r p with
  | zero => unfold _root_.OnBytes.Model.Head.channelRounds; keeps
  | succ n ih => unfold _root_.OnBytes.Model.Head.channelRounds; keeps

theorem KeepsOf.OnBytes.recvVectors (ns : List Nat) : Over.K (recvVectors ns) := by
  induction ns with
  | nil => unfold _root_.OnBytes.recvVectors; keeps
  | cons n ns ih => unfold _root_.OnBytes.recvVectors; keeps

theorem KeepsOf.OnBytes.Attention.sc3Rounds (n : Nat) (p : Psc) (r : Array E) :
    Over.K (Attention.sc3Rounds n p r) := by
  induction n generalizing p r with
  | zero => unfold _root_.OnBytes.Attention.sc3Rounds; keeps
  | succ n ih => unfold _root_.OnBytes.Attention.sc3Rounds; keeps

theorem KeepsOf.OnBytes.Attention.sc3Shown (o : Attention.Sc3) (W : Array E) (n b : Nat) (s : E) :
    Over.K (Attention.sc3Shown o W n b s) := by
  induction n generalizing b s with
  | zero => unfold _root_.OnBytes.Attention.sc3Shown; keeps
  | succ n ih => unfold _root_.OnBytes.Attention.sc3Shown; keeps

theorem KeepsOf.OnBytes.Attention.scdRounds (ds : List Nat) (p : Psc) (r : Array E) :
    Over.K (Attention.scdRounds ds p r) := by
  induction ds generalizing p r with
  | nil => unfold _root_.OnBytes.Attention.scdRounds; keeps
  | cons d ds ih => unfold _root_.OnBytes.Attention.scdRounds; keeps

/-! ### `OnBytes.Attention.planeUnit`, and what its text reaches -/

theorem KeepsOf.OnBytes.Model.SubM.claimsIn (n : Nat) :
    Over.K (OnBytes.Model.SubM.claimsIn n) := by
  keeps

theorem KeepsOf.OnBytes.Attention.planeUnit (S : OnBytes.Attention.Shape)
    (zk : Array (Array OnBytes.E)) (u : Nat × OnBytes.Attention.ACall × OnBytes.Attention.Seg) :
    Over.K (OnBytes.Attention.planeUnit S zk u) := by
  keeps

/-! ### `OnBytes.Attention.scoreUnit`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.recvE : Over.K OnBytes.Blk.recvE := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.answer (r : OnBytes.Model.RoundName) :
    Over.K (OnBytes.Model.SubM.answer r) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.publicPart (a : OnBytes.Model.Aff) :
    Over.K (OnBytes.Model.SubM.publicPart a) := by
  keeps

theorem KeepsOf.OnBytes.Model.pscRow (p : OnBytes.Model.Psc) (S0 : OnBytes.E)
    (kept : OnBytes.Model.Aff := { }) : Over.K (OnBytes.Model.pscRow p S0 kept) := by
  keeps

theorem KeepsOf.OnBytes.Model.trAnswerNotZero (r : OnBytes.Model.RoundName) :
    Over.K (OnBytes.Model.trAnswerNotZero r) := by
  keeps

theorem KeepsOf.OnBytes.Model.trEmpty (r : OnBytes.Model.RoundName) :
    Over.K (OnBytes.Model.trEmpty r) := by
  keeps

theorem KeepsOf.OnBytes.Model.trSum : Over.K OnBytes.Model.trSum := by
  keeps

theorem KeepsOf.OnBytes.Attention.sc3Row (o : OnBytes.Attention.Sc3)
    (W : Array OnBytes.E) : Over.K (OnBytes.Attention.sc3Row o W) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.empty (r : OnBytes.Model.RoundName) :
    Over.K (OnBytes.Model.SubM.empty r) := by
  keeps

theorem KeepsOf.OnBytes.Model.SubM.readSum :
    Over.K OnBytes.Model.SubM.readSum := by
  keeps

theorem KeepsOf.OnBytes.Model.pscBeginAt (target : OnBytes.E) :
    Over.K (OnBytes.Model.pscBeginAt target) := by
  keeps

theorem KeepsOf.OnBytes.Model.pscEnds (p : OnBytes.Model.Psc) (degreeInY n : Nat) :
    Over.K (OnBytes.Model.pscEnds p degreeInY n) := by
  keeps

theorem KeepsOf.OnBytes.Model.pscBegin (C : OnBytes.Model.Aff) :
    Over.K (OnBytes.Model.pscBegin C) := by
  keeps

theorem KeepsOf.OnBytes.Attention.sc3In (nv nb : Nat) (start : OnBytes.Model.Aff) :
    Over.K (OnBytes.Attention.sc3In nv nb start) := by
  keeps

theorem KeepsOf.OnBytes.Attention.scoreUnit (S : OnBytes.Attention.Shape)
    (zk : Array (Array OnBytes.E)) (claim : Nat)
    (u : Nat × OnBytes.Attention.ACall × OnBytes.Attention.Seg) :
    Over.K (OnBytes.Attention.scoreUnit S zk claim u) := by
  keeps

theorem KeepsOf.OnBytes.Attention.planeUnits (S : Attention.Shape) (zk : Array (Array E))
    (us : List (Nat × Attention.ACall × Attention.Seg)) (planes : Array Attention.PlaneClaim) :
    Over.K (Attention.planeUnits S zk us planes) := by
  induction us generalizing planes with
  | nil => unfold _root_.OnBytes.Attention.planeUnits; keeps
  | cons u us ih => unfold _root_.OnBytes.Attention.planeUnits; keeps

theorem KeepsOf.OnBytes.Attention.scoreUnits (S : Attention.Shape) (zk : Array (Array E))
    (us : List (Nat × Attention.ACall × Attention.Seg)) (planes : Array Attention.PlaneClaim)
    (stored : Array Attention.Score) : Over.K (Attention.scoreUnits S zk us planes stored) := by
  induction us generalizing planes stored with
  | nil => unfold _root_.OnBytes.Attention.scoreUnits; keeps
  | cons u us ih => unfold _root_.OnBytes.Attention.scoreUnits; keeps

/-! ### `OnBytes.baseVerify`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.closeOne (name : String)
    (kind : Fmt.Kind := Fmt.Kind.elems) (nz : Nat := 0) :
    Over.K (OnBytes.Blk.closeOne name kind nz) := by
  keeps

theorem KeepsOf.OnBytes.Blk.closePositions (name : String) (logN : Nat) :
    Over.K (OnBytes.Blk.closePositions name logN) := by
  keeps

theorem KeepsOf.OnBytes.Blk.openTrees (B : OnBytes.TreeBook) (pos : OnBytes.Positions)
    (ts : List Nat) : Over.K (OnBytes.Blk.openTrees B pos ts) := by
  keeps

theorem KeepsOf.OnBytes.Blk.readOpened (ids : Array Nat) (pos : OnBytes.Positions) :
    Over.K (OnBytes.Blk.readOpened ids pos) := by
  keeps

theorem KeepsOf.OnBytes.Blk.spendAsMask (o : Nat) :
    Over.K (OnBytes.Blk.spendAsMask o) := by
  keeps

theorem KeepsOf.OnBytes.baseVerify (R : OnBytes.SingleRows) (mask : Option Nat)
    (leafClass : Nat) : Over.K (OnBytes.baseVerify R mask leafClass) := by
  keeps

/-! ### `OnBytes.foldVerify`, and what its text reaches -/

theorem KeepsOf.OnBytes.foldEpsilon (s : OnBytes.FoldStart) :
    Over.K (OnBytes.foldEpsilon s) := by
  keeps

theorem KeepsOf.OnBytes.foldRoundsVerify (F : OnBytes.FoldShape)
    (row : OnBytes.GroupRow) (start : OnBytes.FoldStart) :
    Over.K (OnBytes.foldRoundsVerify F row start) := by
  keeps

theorem KeepsOf.OnBytes.foldStartVerify (F : OnBytes.FoldShape) (mask : Option Nat) :
    Over.K (OnBytes.foldStartVerify F mask) := by
  keeps

theorem KeepsOf.OnBytes.foldVerify (F : OnBytes.FoldShape) (row : OnBytes.GroupRow)
    (mask : Option Nat) : Over.K (OnBytes.foldVerify F row mask) := by
  keeps

/-! ### `OnBytes.csVerify`, and what its text reaches -/

theorem KeepsOf.OnBytes.Blk.closeLedger (o : Nat) :
    Over.K (OnBytes.Blk.closeLedger o) := by
  keeps

theorem KeepsOf.OnBytes.Blk.layout (g : Nat) :
    Over.K (OnBytes.Blk.layout g) := by
  keeps

theorem KeepsOf.OnBytes.singleRowsRead (s : OnBytes.SingleRows)
    (pos : OnBytes.Positions) : Over.K (OnBytes.singleRowsRead s pos) := by
  keeps

theorem KeepsOf.OnBytes.switchAdmit (old : OnBytes.SingleRows)
    (T : OnBytes.SwitchTarget) (to : Nat) (out : OnBytes.Switched) (y : Array OnBytes.E) :
    Over.K (OnBytes.switchAdmit old T to out y) := by
  keeps

theorem KeepsOf.OnBytes.switchVerify (old : OnBytes.SingleRows)
    (T : OnBytes.SwitchTarget) (to : Nat) (others : Array OnBytes.OracleNotice) (withTheta : Bool) :
    Over.K (OnBytes.switchVerify old T to others withTheta) := by
  keeps

theorem KeepsOf.OnBytes.Blk.beginRun (g : Nat) :
    Over.K (OnBytes.Blk.beginRun g) := by
  keeps

theorem KeepsOf.OnBytes.csVerify (old : OnBytes.SingleRows) (T : OnBytes.SwitchTarget)
    (to : Nat) (others : Array OnBytes.OracleNotice) :
    Over.K (OnBytes.csVerify old T to others) := by
  keeps

theorem KeepsOf.OnBytes.ioppStagesVerify (answers : Nat) (ride : Bool) (cur : Params.IoppStage)
    (rest : List Params.IoppStage) (row : GroupRow) (L : GroupLayout) (mask : Option Nat) :
    Over.K (ioppStagesVerify answers ride cur rest row L mask) := by
  induction rest generalizing cur row L mask with
  | nil => unfold _root_.OnBytes.ioppStagesVerify; keeps
  | cons next rest ih => unfold _root_.OnBytes.ioppStagesVerify; keeps

end OnBytes.Flat
