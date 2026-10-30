-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsTails.lean: behind a link's routine, on a view, no message is open.

Definitions, statements and proofs. Each of the three kinds of link ends in doorH
(OnBytes/Model/Trees.lean), whose last call on the channel is ChainCheck.close; behind that call no
message is open (OnBytes/Tie/Pv/Keeps/KeepsOpen.lean); what follows it leaves the channel as it was.
To say so of a long routine only its tail has to be looked at.
Main names:
  `EndsClean x`: wherever the routine x succeeds on a view, it leaves a context in which no message
    is open.
  `LeavesCh x`: wherever x succeeds, it leaves the channel as it was.
  `EndsClean.behind`: x, then f: if x keeps (KeepsM) and every f a is `EndsClean`, so is the whole.
  `EndsClean.andThen`: x, then f: if x is `EndsClean` and every f a is `LeavesCh`, so is the whole.
  `LeavesCh.pure`, `LeavesCh.bind`, `LeavesCh.lift`, `LeavesCh.up`, `LeavesCh.sub`, and the laws for
    the calls on a layer's own state and on a sub-proof's state.
  `doorH_ends`: doorH is `EndsClean`.
Tactics of this file.
  tail_walk: proves `EndsClean` of a routine: it goes along the routine's text from the front, past
    every call that keeps, to a call that is known to be `EndsClean`, and shows of what follows that
    it leaves the channel.
  leaves_ch: proves `LeavesCh` of a routine that is made of such calls.
Limits: one direction: from a success. Nothing on a dry run.
-/
import OnBytes.Tie.Pv.Keeps.KeepsOpen
import OnBytes.Tie.Pv.Keeps.KeepsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Cut

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

section Laws

variable {m : Type → Type} [Monad m] [HasRuns m] {α β σ : Type}

/-- Wherever the routine succeeds on a view, no message is open behind it. -/
def EndsClean (x : m α) : Prop :=
  ∀ s a s', Runs x s a s' → View s → (HasRuns.ctx s').ch.cur = none

/-- Wherever the routine succeeds, it leaves the channel as it was. -/
def LeavesCh (x : m α) : Prop := ∀ s a s', Runs x s a s' → (HasRuns.ctx s').ch = (HasRuns.ctx s).ch

theorem EndsClean.behind [HasKeeps m] [RunsKeep m] {x : m α} (k : KeepsM x) {f : α → m β}
    (hf : ∀ a, EndsClean (f a)) : EndsClean (x >>= f) := fun s b s' h d => by
  obtain ⟨a, s1, _, d1, h2⟩ := step h d
  exact hf a s1 b s' h2 d1

theorem EndsClean.andThen {x : m α} (hx : EndsClean x) {f : α → m β} (hf : ∀ a, LeavesCh (f a)) :
    EndsClean (x >>= f) := fun s b s' h d => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  rw [hf a s1 b s' h2]
  exact hx s a s1 h1 d

theorem EndsClean.fails (x : m α) [Fails x] : EndsClean x := fun _ _ _ h _ => Fails.elim h

theorem LeavesCh.fails (x : m α) [Fails x] : LeavesCh x := fun _ _ _ h => Fails.elim h

theorem LeavesCh.pure (a : α) : LeavesCh (pure a : m α) := fun s b s' h => by
  rw [(HasRuns.runs_pure h).2]

theorem LeavesCh.bind {x : m α} (hx : LeavesCh x) {f : α → m β} (hf : ∀ a, LeavesCh (f a)) :
    LeavesCh (x >>= f) := fun s b s' h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  rw [hf a s1 b s' h2, hx s a s1 h1]

theorem LeavesCh.lift {x : m α} (hx : LeavesCh x) : LeavesCh (StateT.lift x : StateT σ m α) :=
  fun s a s' h => hx s.2 a s'.2 (runs_lift h).1

theorem LeavesCh.up {n : Type → Type} [MonadLiftT n m] {x : n α}
    (hx : LeavesCh (monadLift x : m α)) : LeavesCh (monadLift x : StateT σ m α) :=
  fun s a s' h => hx s.2 a s'.2 (runs_up h).1

theorem LeavesCh.get : LeavesCh (get : StateT σ m σ) := fun s a s' h => by rw [(runs_get h).2]

theorem LeavesCh.modify (f : σ → σ) : LeavesCh (modify f : StateT σ m PUnit) := fun s a s' h => by
  rw [runs_modify h]
  rfl

end Laws

/-- A block that leaves the channel, in the words of OnBytes/Tie/Pv/Keeps/KeepsOpen.lean. -/
theorem LeavesCh.same {α : Type} (b : Blk α) [k : Open.SameCh b] : LeavesCh b :=
  fun c a c' h => k.out c a c' h

theorem LeavesCh.sub {α : Type} {x : SubM α} (hx : LeavesCh x) : LeavesCh (LinkM.sub x) :=
  fun s a s' h => hx s.2 a s'.2 (runs_sub h).1

theorem LeavesCh.ask {α : Type} (f : Fork → Option α) : LeavesCh (SubM.ask f) := fun s a s' h => by
  rw [(runs_ask h).2]

theorem LeavesCh.change (f : Fork → Option Fork) : LeavesCh (SubM.change f) := fun s a s' h => by
  show s'.2.ch = s.2.ch
  rw [(runs_change h).2]

theorem LeavesCh.mustAs (n : String) (b : Bool) : LeavesCh (Model.mustAs n b) := fun c u c' h => by
  rw [(runs_mustAs h).2]

theorem LeavesCh.allTaken : LeavesCh SubM.allTaken := LeavesCh.ask _

theorem LeavesCh.subMust (b : Bool) : LeavesCh (SubM.must b) :=
  LeavesCh.lift (LeavesCh.same (Blk.must b))

theorem LeavesCh.fork : LeavesCh LinkM.fork := LeavesCh.sub (LeavesCh.ask _)

theorem LeavesCh.linkMust (b : Bool) : LeavesCh (LinkM.must b) := LeavesCh.sub (LeavesCh.subMust b)

/-- A call of the chain that closes the link. -/
theorem call_close_ends (eq : ReqEquation) : EndsClean (LinkM.call fun c => c.close eq) :=
  fun s u s' h d => by
    obtain ⟨_, chk, h1, _, _⟩ := call_L h
    exact (Open.chainClose_clean d h1).2

/-- doorH leaves no message open. -/
theorem doorH_ends (laid : Nat) : EndsClean (doorH laid) := by
  unfold doorH
  repeat' first
    | exact EndsClean.andThen (call_close_ends _) fun _ => LeavesCh.modify _
    | refine EndsClean.behind (by keepsM) fun _ => ?_

theorem EndsClean.map {m : Type → Type} [Monad m] [LawfulMonad m] [HasRuns m] {α β : Type}
    (g : α → β) {x : m α} (hx : EndsClean x) : EndsClean (g <$> x) := by
  rw [← bind_pure_comp]
  exact hx.andThen fun _ => LeavesCh.pure _

/-! ## The tactics -/

/-- Proves LeavesCh of a routine that is made of calls which leave the channel. -/
macro "leaves_ch" : tactic =>
  `(tactic| repeat' first
      | exact LeavesCh.pure _
      | exact LeavesCh.get
      | exact LeavesCh.modify _
      | exact LeavesCh.ask _
      | exact LeavesCh.change _
      | exact LeavesCh.mustAs _ _
      | exact LeavesCh.allTaken
      | exact LeavesCh.subMust _
      | exact LeavesCh.fork
      | exact LeavesCh.linkMust _
      | exact LeavesCh.same _
      | exact LeavesCh.fails _
      | refine LeavesCh.bind ?_ fun _ => ?_
      | refine LeavesCh.sub ?_
      | refine LeavesCh.lift ?_
      | refine LeavesCh.up ?_
      | split
      | dsimp only)

/-- Proves EndsClean of a routine: along its text from the front, past every call that keeps, to the
call of which e says EndsClean; what follows that call leaves the channel. -/
macro "tail_walk " e:term : tactic =>
  `(tactic| repeat' first
      | with_reducible exact $e
      | with_reducible exact EndsClean.fails _
      | ((with_reducible refine EndsClean.andThen $e fun _ => ?_); leaves_ch; done)
      | refine EndsClean.behind (by keepsM) fun _ => ?_
      | split
      | dsimp only)

/-! ## The three kinds of link -/

theorem finish_ends (tl : HTailF2) (nU : Array Nat) : EndsClean (Attention.Seam.finish tl nU) := by
  unfold Attention.Seam.finish
  tail_walk (doorH_ends _)

theorem countsHeld_leaves (P : Attention.Plan) (tl : HTailF2) :
    LeavesCh (Attention.countsHeld P tl) := by
  unfold Attention.countsHeld SubM.claims SubM.allTaken
  leaves_ch

theorem attention_ends (P : Attention.Plan) : EndsClean (Attention.run P) := by
  unfold Attention.run
  repeat' first
    | with_reducible exact EndsClean.fails _
    | with_reducible
        exact EndsClean.andThen (finish_ends _ _) fun _ => LeavesCh.up (countsHeld_leaves _ _)
    | refine EndsClean.behind (by keepsM) fun _ => ?_
    | split

theorem layer_ends (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) :
    EndsClean (Layer.runForkHidG2 P hp g) := by
  unfold Layer.runForkHidG2
  tail_walk (doorH_ends _)

theorem head_ends (h : Head.Shape) (L : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) :
    EndsClean (Head.runForkHidH2 h L b hp O cov wsLay) := by
  unfold Head.runForkHidH2
  tail_walk (doorH_ends _)

end OnBytes.Tie.Pv.Keeps.Cut

#print axioms OnBytes.Tie.Pv.Keeps.Cut.doorH_ends
#print axioms OnBytes.Tie.Pv.Keeps.Cut.attention_ends
#print axioms OnBytes.Tie.Pv.Keeps.Cut.layer_ends
#print axioms OnBytes.Tie.Pv.Keeps.Cut.head_ends
