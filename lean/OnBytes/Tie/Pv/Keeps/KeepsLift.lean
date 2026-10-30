-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsLift.lean: the class Keeps of OnBytes/Tie/Pv/Keeps/KeepsKit.lean, carried
through StateT: to the routines of a sub-proof (SubM = StateT Fork Blk) and of a link (LinkM =
StateT LinkCtx SubM).

How the rules are cut. HasKeeps m is a property K of the routines of a monad m of which two things
are known: pure has it, and bind carries it. Every further rule (map, if, the loops, mapM) is drawn
from these two alone, once, for every such monad. Blk has Keeps as its K. If m has a K, StateT σ m
has one: the routine, run from every state, has m's. Only the calls that are written as functions of
a state are shown by hand.

 1. HasKeeps, its two instances, the class KeepsM.
 2. the rules.
 3. lifts; the calls on a layer's own state (get, set, modify, modifyGet).
 4. the same rules with their hypotheses as goals, for the tactic.
 5. the tactic keepsM.

For a twin that compares two runs: only HasKeeps and its two instances speak of what K is. A twin
has a K of two routines and a relation on values; its pure and bind take the place of K_pure and
K_bind, and the rules of section 2 are drawn from them by the same inductions.

Tactics of this file.
  keepsM: as keeps, for a routine over blocks (KeepsM): it also enters a loop, a map or a lift by
    its rule where the body wants cases, and takes a routine that is run from a state without the
    state.
-/
import OnBytes.Tie.Pv.Keeps.KeepsKit

namespace OnBytes.L5

open OnBytes

/-- A property of a monad's routines that pure has and bind carries. -/
class HasKeeps (m : Type → Type) [Monad m] where
  K : {α : Type} → m α → Prop
  K_pure : ∀ {α : Type} (a : α), K (pure a : m α)
  K_bind : ∀ {α β : Type} (x : m α) (f : α → m β), K x → (∀ a, K (f a)) → K (x >>= f)

/-- For a block: Keeps. -/
instance hasKeeps_blk : HasKeeps Blk where
  K := fun b => Keeps b
  K_pure := fun a => keeps_pure a
  K_bind := fun _ _ hx hf => Keeps.bind hx hf

/-- For a routine with a state of its own: from every state it has the property below. -/
instance hasKeeps_stateT {σ : Type} {m : Type → Type} [Monad m] [HasKeeps m] :
    HasKeeps (StateT σ m) where
  K := fun x => ∀ s, HasKeeps.K (x s)
  K_pure := fun a s => HasKeeps.K_pure (a, s)
  K_bind := fun x _ hx hf s => HasKeeps.K_bind (x s) _ (hx s) fun ⟨a, s'⟩ => hf a s'

/-- The routine has its monad's property. A class, so that Lean finds the fact on each step. -/
class KeepsM {m : Type → Type} [Monad m] [HasKeeps m] {α : Type} (x : m α) : Prop where
  out : HasKeeps.K x

section Rules

variable {m : Type → Type} [Monad m] [HasKeeps m] {α β γ σ : Type}

/-- A block that Keeps. -/
instance keepsM_of_keeps (b : Blk α) [h : Keeps b] : KeepsM b := ⟨h⟩

/-- Back. -/
theorem KeepsM.keeps (b : Blk α) [h : KeepsM b] : Keeps b := h.out

/-- A routine with a state, by its runs. -/
theorem KeepsM.fn {x : StateT σ m α} (h : ∀ s, KeepsM (x s)) : KeepsM x := ⟨fun s => (h s).out⟩

/-- A routine over blocks that is written as a function of its state and of the context. -/
theorem KeepsM.prim {x : StateT σ Blk α}
    (h : ∀ s c y c', x s c = .ok (y, c') → Kept c c') : KeepsM x :=
  KeepsM.fn fun s => @keepsM_of_keeps _ (x s) ⟨h s⟩

/-- A run of a routine with a state. -/
theorem KeepsM.at {x : StateT σ m α} (h : KeepsM x) (s : σ) : KeepsM (x s) := ⟨h.out s⟩

instance keepsM_run (x : StateT σ m α) [h : KeepsM x] (s : σ) : KeepsM (x.run s) := h.at s

instance keepsM_pure (a : α) : KeepsM (pure a : m α) := ⟨HasKeeps.K_pure a⟩

theorem KeepsM.bind {x : m α} {f : α → m β} (hx : KeepsM x) (hf : ∀ a, KeepsM (f a)) :
    KeepsM (x >>= f) := ⟨HasKeeps.K_bind x f hx.out fun a => (hf a).out⟩

instance keepsM_bind (x : m α) (f : α → m β) [hx : KeepsM x] [hf : ∀ a, KeepsM (f a)] :
    KeepsM (x >>= f) := KeepsM.bind hx hf

instance keepsM_map [LawfulMonad m] (g : α → β) (x : m α) [KeepsM x] : KeepsM (g <$> x) := by
  rw [← bind_pure_comp]; infer_instance

instance keepsM_discard [LawfulMonad m] (x : m α) [KeepsM x] : KeepsM (discard x) := by
  unfold Functor.discard
  rw [map_const]
  exact keepsM_map (Function.const α PUnit.unit) x

instance keepsM_ite (p : Prop) [Decidable p] (a b : m α) [KeepsM a] [KeepsM b] :
    KeepsM (if p then a else b) := by
  split <;> assumption

instance keepsM_dite (p : Prop) [Decidable p] (a : p → m α) (b : ¬p → m α)
    [ha : ∀ h, KeepsM (a h)] [hb : ∀ h, KeepsM (b h)] : KeepsM (dite p a b) := by
  split
  · exact ha _
  · exact hb _

instance keepsM_forIn_list (l : List γ) (init : β) (f : γ → β → m (ForInStep β))
    [hf : ∀ a b, KeepsM (f a b)] : KeepsM (forIn l init f) := by
  induction l generalizing init with
  | nil => rw [List.forIn_nil]; infer_instance
  | cons a l ih =>
    rw [List.forIn_cons]
    refine KeepsM.bind (hf a init) fun r => ?_
    cases r with
    | done b => exact keepsM_pure b
    | yield b => exact ih b

instance keepsM_forIn_array (l : Array γ) (init : β) (f : γ → β → m (ForInStep β))
    [hf : ∀ a b, KeepsM (f a b)] : KeepsM (forIn l init f) := by
  rw [← Array.forIn_toList]; infer_instance

instance keepsM_forIn_range (r : Std.Legacy.Range) (init : β) (f : Nat → β → m (ForInStep β))
    [hf : ∀ a b, KeepsM (f a b)] : KeepsM (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; infer_instance

instance keepsM_foldlM_list (l : List γ) (init : β) (f : β → γ → m β)
    [hf : ∀ b a, KeepsM (f b a)] : KeepsM (l.foldlM f init) := by
  induction l generalizing init with
  | nil => rw [List.foldlM_nil]; infer_instance
  | cons a l ih =>
    rw [List.foldlM_cons]
    exact KeepsM.bind (hf init a) fun r => ih r

instance keepsM_foldlM_array (l : Array γ) (init : β) (f : β → γ → m β)
    [hf : ∀ b a, KeepsM (f b a)] : KeepsM (l.foldlM f init) := by
  rw [← Array.foldlM_toList]; infer_instance

instance keepsM_forM_list (l : List γ) (f : γ → m PUnit) [hf : ∀ a, KeepsM (f a)] :
    KeepsM (l.forM f) := by
  induction l with
  | nil => exact keepsM_pure _
  | cons a l ih => exact KeepsM.bind (hf a) fun _ => ih

instance keepsM_forM_array (l : Array γ) (f : γ → m PUnit) [hf : ∀ a, KeepsM (f a)] :
    KeepsM (l.forM f) := by
  unfold Array.forM; infer_instance

instance keepsM_mapM_array [LawfulMonad m] (l : Array γ) (f : γ → m β)
    [hf : ∀ a, KeepsM (f a)] :
    KeepsM (l.mapM f) := by
  rw [Array.mapM_eq_foldlM]; infer_instance

instance keepsM_mapM_list [LawfulMonad m] (l : List γ) (f : γ → m β) [hf : ∀ a, KeepsM (f a)] :
    KeepsM (l.mapM f) := by
  induction l with
  | nil => rw [List.mapM_nil]; infer_instance
  | cons a l ih => rw [List.mapM_cons]; infer_instance

/-! ## Lifts -/

instance keepsM_lift (x : m α) [hx : KeepsM x] : KeepsM (StateT.lift x : StateT σ m α) :=
  ⟨fun s => HasKeeps.K_bind x _ hx.out fun a => HasKeeps.K_pure (a, s)⟩

/-- A routine lifted to its own monad. -/
instance keepsM_monadLift_self (x : m α) [hx : KeepsM x] : KeepsM (monadLift x : m α) := hx

/-- A lift through one more layer of state. n: any monad that lifts into m. -/
instance keepsM_monadLift_step {n : Type → Type} [MonadLiftT n m] (x : n α)
    [hx : KeepsM (monadLift x : m α)] : KeepsM (monadLift x : StateT σ m α) :=
  keepsM_lift (σ := σ) (monadLift x : m α)

/-- What has no context (a value that may be missing, a value or a failure), lifted into a block. -/
instance keeps_monadLift_except {n : Type → Type} [MonadLiftT n (Except Failure)] (x : n α) :
    Keeps (monadLift x : Blk α) :=
  ⟨fun c y c' h => by
    have h' : ((monadLift x : Except Failure α) >>= fun a => pure (a, c)) = .ok (y, c') := h
    cases e : (monadLift x : Except Failure α) with
    | error f => rw [e] at h'; cases h'
    | ok a => rw [e] at h'; cases h'; exact Kept.refl _⟩

/-- Blk.named and Blk.inPlace of a block that is KeepsM. -/
instance keeps_named' (n : String) (b : Blk α) [h : KeepsM b] : Keeps (Blk.named n b) :=
  @keeps_named _ n b h.out

instance keeps_inPlace' (n : String) (b : Blk α) [h : KeepsM b] : Keeps (Blk.inPlace n b) :=
  @keeps_inPlace _ n b h.out

/-- A block that reads the whole context and leaves it. -/
instance keeps_getThe : Keeps (getThe Ctx : Blk Ctx) :=
  ⟨fun c x c' h => by cases h; exact Kept.refl _⟩

/-! ## The calls on a layer's own state

They are stated for the state of the outermost StateT alone, over a monad that has a K. Blk itself
is StateT Ctx over Except Failure, which has none: so none of the four speaks of the context. -/

instance keepsM_get : KeepsM (get : StateT σ m σ) := ⟨fun s => HasKeeps.K_pure (s, s)⟩

instance keepsM_set (s' : σ) : KeepsM (set s' : StateT σ m PUnit) :=
  ⟨fun _ => HasKeeps.K_pure (PUnit.unit, s')⟩

instance keepsM_modify (f : σ → σ) : KeepsM (modify f : StateT σ m PUnit) :=
  ⟨fun s => HasKeeps.K_pure (PUnit.unit, f s)⟩

instance keepsM_modifyGet (f : σ → α × σ) : KeepsM (modifyGet f : StateT σ m α) :=
  ⟨fun s => HasKeeps.K_pure (f s)⟩

/-! ## The same rules with their hypotheses as goals, for the tactic -/

theorem KeepsM.forInL {l : List γ} {init : β} {f : γ → β → m (ForInStep β)}
    (hf : ∀ a b, KeepsM (f a b)) : KeepsM (forIn l init f) := keepsM_forIn_list l init f

theorem KeepsM.forInA {l : Array γ} {init : β} {f : γ → β → m (ForInStep β)}
    (hf : ∀ a b, KeepsM (f a b)) : KeepsM (forIn l init f) := keepsM_forIn_array l init f

theorem KeepsM.forInR {r : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (hf : ∀ a b, KeepsM (f a b)) : KeepsM (forIn r init f) := keepsM_forIn_range r init f

theorem KeepsM.foldlML {l : List γ} {init : β} {f : β → γ → m β}
    (hf : ∀ b a, KeepsM (f b a)) : KeepsM (l.foldlM f init) := keepsM_foldlM_list l init f

theorem KeepsM.foldlMA {l : Array γ} {init : β} {f : β → γ → m β}
    (hf : ∀ b a, KeepsM (f b a)) : KeepsM (l.foldlM f init) := keepsM_foldlM_array l init f

theorem KeepsM.forML {l : List γ} {f : γ → m PUnit} (hf : ∀ a, KeepsM (f a)) :
    KeepsM (l.forM f) := keepsM_forM_list l f

theorem KeepsM.forMA {l : Array γ} {f : γ → m PUnit} (hf : ∀ a, KeepsM (f a)) :
    KeepsM (l.forM f) := keepsM_forM_array l f

theorem KeepsM.mapML [LawfulMonad m] {l : List γ} {f : γ → m β} (hf : ∀ a, KeepsM (f a)) :
    KeepsM (l.mapM f) := keepsM_mapM_list l f

theorem KeepsM.mapMA [LawfulMonad m] {l : Array γ} {f : γ → m β} (hf : ∀ a, KeepsM (f a)) :
    KeepsM (l.mapM f) := keepsM_mapM_array l f

theorem KeepsM.map [LawfulMonad m] {g : α → β} {x : m α} (hx : KeepsM x) : KeepsM (g <$> x) :=
  keepsM_map g x

theorem KeepsM.discard [LawfulMonad m] {x : m α} (hx : KeepsM x) : KeepsM (discard x) :=
  keepsM_discard x

theorem KeepsM.lift {x : m α} (hx : KeepsM x) : KeepsM (StateT.lift x : StateT σ m α) :=
  keepsM_lift x

theorem KeepsM.liftStep {n : Type → Type} [MonadLiftT n m] {x : n α}
    (hx : KeepsM (monadLift x : m α)) : KeepsM (monadLift x : StateT σ m α) :=
  keepsM_monadLift_step x

theorem KeepsM.run {x : StateT σ m α} (hx : KeepsM x) (s : σ) : KeepsM (x.run s) := hx.at s

end Rules

/-! ## The tactic -/

/-- As keeps, with one step more: a loop, a map or a lift whose body wants cases is entered by its
rule; and a routine that is run from a state is taken without the state. -/
macro "keepsM" : tactic =>
  `(tactic| repeat' first
      | infer_instance
      | intro _
      | apply KeepsM.bind
      | apply KeepsM.forInL
      | apply KeepsM.forInA
      | apply KeepsM.forInR
      | apply KeepsM.foldlML
      | apply KeepsM.foldlMA
      | apply KeepsM.forML
      | apply KeepsM.forMA
      | apply KeepsM.mapML
      | apply KeepsM.mapMA
      | apply KeepsM.map
      | apply KeepsM.discard
      | apply KeepsM.lift
      | apply KeepsM.liftStep
      | apply KeepsM.run
      | split
      | dsimp only
      | apply KeepsM.at)

#print axioms hasKeeps_blk
#print axioms hasKeeps_stateT
#print axioms keepsM_map
#print axioms keepsM_forIn_list
#print axioms keepsM_forIn_array
#print axioms keepsM_forIn_range
#print axioms keepsM_foldlM_list
#print axioms keepsM_foldlM_array
#print axioms keepsM_forM_list
#print axioms keepsM_forM_array
#print axioms keepsM_mapM_array
#print axioms keepsM_mapM_list
#print axioms keepsM_lift
#print axioms keepsM_monadLift_self
#print axioms keepsM_monadLift_step
#print axioms keeps_monadLift_except
#print axioms keeps_named'
#print axioms keeps_inPlace'
#print axioms keeps_getThe
#print axioms keepsM_discard
#print axioms keepsM_get
#print axioms keepsM_set
#print axioms keepsM_modify
#print axioms keepsM_modifyGet

end OnBytes.L5
