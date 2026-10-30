-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean.
The three words on the channel's two marks, for a sub-proof's routines and for a link's routines.

A routine of a sub-proof (`SubM`) is a block for each state of the sub-proof, and a routine of a
link (`LinkM`) is a routine of a sub-proof for each state of the link. So the words of
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean
are said of them state by state.

 * `CalmS x`, `DryS x`, `ShutS x`: for every state F of the sub-proof the block `x F` is calm, stays
   on the view, leaves no message open. `CalmL`, `DryL`, `ShutL`: the same for every state of the
   link and of the sub-proof.
 * The rules: pure, bind, the lifts from one level to the next, a loop over a list, reading and
   setting the link's state; "stays on the view, then leaves no message open" and "leaves no message
   open, then calm".
 * The routines that act on the sub-proof's state alone (`SubM.ask`, `SubM.take`, `SubM.change`) are
   calm.
 * `shutL_call`: a call of the chain (`LinkM.call`) by a block that leaves no message open leaves
   none open. `shutL_rootInH`: in a run on a view, behind a later commitment (`rootInH`) that
   returns no message is open.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShutLink
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α β σ : Type}

def CalmS (x : SubM α) : Prop := ∀ F, Calm (x F)
def DryS (x : SubM α) : Prop := ∀ F, Dry (x F)
def ShutS (x : SubM α) : Prop := ∀ F, Shut (x F)
def CalmL (x : LinkM α) : Prop := ∀ L, CalmS (x L)
def DryL (x : LinkM α) : Prop := ∀ L, DryS (x L)
def ShutL (x : LinkM α) : Prop := ∀ L, ShutS (x L)

theorem CalmS.dry {x : SubM α} (h : CalmS x) : DryS x := fun F => (h F).dry
theorem ShutS.dry {x : SubM α} (h : ShutS x) : DryS x := fun F => (h F).dry
theorem CalmL.dry {x : LinkM α} (h : CalmL x) : DryL x := fun L => (h L).dry
theorem ShutL.dry {x : LinkM α} (h : ShutL x) : DryL x := fun L => (h L).dry

/-! ### a sub-proof's routines -/

theorem CalmS.pure (a : α) : CalmS (Pure.pure a : SubM α) := fun F => Calm.pure (a, F)

theorem CalmS.bind {x : SubM α} {f : α → SubM β} (hx : CalmS x) (hf : ∀ a, CalmS (f a)) :
    CalmS (x >>= f) := fun F =>
  Calm.bind (x := x F) (f := fun p => f p.1 p.2) (hx F) fun p => hf p.1 p.2

theorem DryS.bind {x : SubM α} {f : α → SubM β} (hx : DryS x) (hf : ∀ a, DryS (f a)) :
    DryS (x >>= f) := fun F =>
  Dry.bind (x := x F) (f := fun p => f p.1 p.2) (hx F) fun p => hf p.1 p.2

theorem ShutS.after {x : SubM α} {f : α → SubM β} (hx : DryS x) (hf : ∀ a, ShutS (f a)) :
    ShutS (x >>= f) := fun F =>
  Shut.after (x := x F) (f := fun p => f p.1 p.2) (hx F) fun p => hf p.1 p.2

theorem ShutS.before {x : SubM α} {f : α → SubM β} (hx : ShutS x) (hf : ∀ a, CalmS (f a)) :
    ShutS (x >>= f) := fun F =>
  Shut.before (x := x F) (f := fun p => f p.1 p.2) (hx F) fun p => hf p.1 p.2

theorem CalmS.lift {b : Blk α} (h : Calm b) : CalmS (StateT.lift b : SubM α) := fun F =>
  Calm.bind (f := fun a => Pure.pure (a, F)) h fun _ => Calm.pure _
theorem DryS.lift {b : Blk α} (h : Dry b) : DryS (StateT.lift b : SubM α) := fun F =>
  Dry.bind (f := fun a => Pure.pure (a, F)) h fun _ => Dry.pure _
theorem ShutS.lift {b : Blk α} (h : Shut b) : ShutS (StateT.lift b : SubM α) := fun F =>
  Shut.before (f := fun a => Pure.pure (a, F)) h fun _ => Calm.pure _

theorem CalmS.ask (f : Fork → Option α) : CalmS (SubM.ask f) := fun F => ⟨fun c a c' h => by
  obtain ⟨_, _, e⟩ := (ask_ok f F c (a, c')).1 h
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  exact ⟨rfl, rfl⟩⟩
theorem CalmS.take (f : Fork → Option (α × Fork)) : CalmS (SubM.take f) :=
  fun F => ⟨fun c a c' h => by
    obtain ⟨_, _, e⟩ := (take_ok f F c (a, c')).1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    exact ⟨rfl, rfl⟩⟩
theorem CalmS.change (f : Fork → Option Fork) : CalmS (SubM.change f) :=
  fun F => ⟨fun c a c' h => by
    obtain ⟨_, _, e⟩ := (change_ok f F c (a, c')).1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    exact ⟨rfl, rfl⟩⟩

/-! ### a link's routines -/

theorem CalmL.pure (a : α) : CalmL (Pure.pure a : LinkM α) := fun L => CalmS.pure (a, L)

theorem CalmL.bind {x : LinkM α} {f : α → LinkM β} (hx : CalmL x) (hf : ∀ a, CalmL (f a)) :
    CalmL (x >>= f) := fun L =>
  CalmS.bind (x := x L) (f := fun p => f p.1 p.2) (hx L) fun p => hf p.1 p.2

theorem ShutL.after {x : LinkM α} {f : α → LinkM β} (hx : DryL x) (hf : ∀ a, ShutL (f a)) :
    ShutL (x >>= f) := fun L =>
  ShutS.after (x := x L) (f := fun p => f p.1 p.2) (hx L) fun p => hf p.1 p.2

theorem ShutL.before {x : LinkM α} {f : α → LinkM β} (hx : ShutL x) (hf : ∀ a, CalmL (f a)) :
    ShutL (x >>= f) := fun L =>
  ShutS.before (x := x L) (f := fun p => f p.1 p.2) (hx L) fun p => hf p.1 p.2

theorem CalmL.sub {x : SubM α} (h : CalmS x) : CalmL (LinkM.sub x) := fun L =>
  CalmS.bind (f := fun a => Pure.pure (a, L)) h fun _ => CalmS.pure _
theorem ShutL.sub {x : SubM α} (h : ShutS x) : ShutL (LinkM.sub x) := fun L =>
  ShutS.before (f := fun a => Pure.pure (a, L)) h fun _ => CalmS.pure _
theorem CalmL.lift {x : SubM α} (h : CalmS x) : CalmL (StateT.lift x : LinkM α) := fun L =>
  CalmS.bind (f := fun a => Pure.pure (a, L)) h fun _ => CalmS.pure _
theorem ShutL.lift {x : SubM α} (h : ShutS x) : ShutL (StateT.lift x : LinkM α) := fun L =>
  ShutS.before (f := fun a => Pure.pure (a, L)) h fun _ => CalmS.pure _

theorem CalmL.get : CalmL (MonadState.get : LinkM LinkCtx) := fun L => CalmS.pure (L, L)
theorem CalmL.modify (f : LinkCtx → LinkCtx) : CalmL (_root_.modify f : LinkM PUnit) :=
  fun L => CalmS.pure (α := PUnit × LinkCtx) (PUnit.unit, f L)

theorem CalmL.loop (f : β → σ → LinkM (ForInStep σ)) (hf : ∀ a s, CalmL (f a s)) :
    ∀ (l : List β) (s : σ), CalmL (forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact CalmL.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine CalmL.bind (hf a s) fun r => ?_
    cases r with
    | done t => exact CalmL.pure t
    | yield t => exact CalmL.loop f hf l t

end

/-! ### the link's own routines -/

theorem calm_mustAs (name : String) (b : Bool) : Calm (mustAs name b) := by
  unfold mustAs refuse; calm
theorem calm_testAs (name : String) (b : Bool) : Calm (testAs name b) := by
  unfold testAs refuse; calm

theorem calmL_mustAs (name : String) (b : Bool) : CalmL (LinkM.mustAs name b) :=
  CalmL.sub (CalmS.lift (calm_mustAs name b))
theorem calmL_must (b : Bool) : CalmL (LinkM.must b) := CalmL.sub (CalmS.lift (calm_must b _))
theorem calmL_fork : CalmL LinkM.fork := CalmL.sub (CalmS.ask _)

/-- A call of the chain that leaves no message open. -/
theorem shutL_call (f : ChainCheck → Blk ChainCheck) (hf : ∀ k, Shut (f k)) :
    ShutL (LinkM.call f) := by
  intro L
  show ShutS (SubM.must (L.link == L.check.link) >>= fun _ =>
    (liftM (f L.check) : SubM ChainCheck) >>= fun check =>
      Pure.pure ((), { L with check := check }))
  exact ShutS.after (CalmS.lift (calm_must _ _)).dry fun _ =>
    ShutS.before (ShutS.lift (hf L.check)) fun _ => CalmS.pure _

/-- Behind a later commitment no message is open. -/
theorem shutL_rootInH (trees : List Nat) : ShutL (rootInH trees) := by
  unfold rootInH
  refine ShutL.after CalmL.get.dry fun L => ShutL.after (calmL_mustAs _ _).dry fun _ =>
    ShutL.before (shutL_call _ shut_checkLater) fun _ => CalmL.bind (CalmL.modify _) fun _ =>
    CalmL.bind (CalmL.loop _ (fun t _ => ?_) _ _) fun _ => calmL_mustAs _ _
  exact CalmL.bind calmL_fork fun F => CalmL.bind (calmL_mustAs _ _) fun _ =>
    CalmL.bind (CalmL.sub (CalmS.change _)) fun _ => CalmL.pure _

end Fo
