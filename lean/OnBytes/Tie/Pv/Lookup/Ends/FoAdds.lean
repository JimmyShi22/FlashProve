-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAdds.lean.
How many claims a routine of a sub-proof adds.

AddsR x n post: every run of x that returns, from a state with one coefficient for each slot,
returns a value that meets post and adds some n claims (Fo.Added). Adds x n: the same without a word
on the value. The file has the rules by which the number passes through the ways in which routines
are put together, and the steps on the state.

States:
  AddsR, Adds; AddsR.pure, .bind, .mono, .cast, .getO (behind SubM.get the value is known), .qbind';
    Adds.pure, .bind, .cast, .lift, .monadLift, .ask, .get, .getO, .must, .ite, .lin (one claim),
    .paid, .foldlM, .arrayFoldlM, .forM, .arrayForM, .forIn (a loop whose body always goes on);
    sum_const.
  Quiet x: x adds no claim; Quiet.pure, .bind, .ite, .foldlM, .arrayFoldlM; the tactic quiet.
Limit: "adds some n claims" pins the NUMBER of claims and no claim: the list is found behind the
state, and a form may carry any element of the field as a coefficient, powers of the state's theta
among them, so one member of such a list can swallow another. Which claims stand where is said with
lists that are terms, or that are fixed before the state (OnBytes/Tie/Pv/Lookup/Ends/FoFixed.lean).
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a run returns, or which claims are added.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAdded
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- Every run that returns, returns a value that meets post and adds some n claims. -/
def AddsR {α : Type} (x : SubM α) (n : ℕ) (post : α → Prop) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') →
    F.LS.size = F.ns → post a ∧ ∃ l : List Cl, l.length = n ∧ Added F G l

/-- Every run that returns adds some n claims. -/
def Adds {α : Type} (x : SubM α) (n : ℕ) : Prop := AddsR x n fun _ => True

section
variable {α β σ : Type}

theorem AddsR.pure {post : α → Prop} (a : α) (h : post a) : AddsR (Pure.pure a : SubM α) 0 post :=
    by
  intro F c b G c' hr hs
  have e := (pure_ok _ _ _ _).1 hr
  have e1 : b = a := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
  have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
  rw [e1, e2]
  exact ⟨h, [], rfl, Added.refl hs⟩

theorem AddsR.bind {x : SubM α} {f : α → SubM β} {n m : ℕ} {p : α → Prop} {post : β → Prop}
    (hx : AddsR x n p) (hf : ∀ a, p a → AddsR (f a) m post) : AddsR (x >>= f) (n + m) post := by
  intro F c b G c' hr hs
  obtain ⟨a, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 hr
  obtain ⟨pa, l1, e1, a1⟩ := hx _ _ _ _ _ h1 hs
  obtain ⟨pb, l2, e2, a2⟩ := hf a pa _ _ _ _ _ h2 a1.sized
  exact ⟨pb, l1 ++ l2, by rw [List.length_append, e1, e2], a1.trans a2⟩

theorem AddsR.mono {x : SubM α} {n : ℕ} {p q : α → Prop} (h : AddsR x n p) (hpq : ∀ a, p a → q a) :
    AddsR x n q := fun F c a G c' hr hs =>
  ⟨hpq a (h F c a G c' hr hs).1, (h F c a G c' hr hs).2⟩

theorem AddsR.cast {x : SubM α} {n m : ℕ} {p : α → Prop} (h : AddsR x n p) (e : n = m) :
    AddsR x m p := e ▸ h

theorem Adds.cast {x : SubM α} {n m : ℕ} (h : Adds x n) (e : n = m) : Adds x m := e ▸ h

theorem Adds.pure (a : α) : Adds (Pure.pure a : SubM α) 0 := AddsR.pure a trivial

theorem Adds.bind {x : SubM α} {f : α → SubM β} {n m : ℕ} (hx : Adds x n)
    (hf : ∀ a, Adds (f a) m) : Adds (x >>= f) (n + m) := AddsR.bind hx fun a _ => hf a

theorem Adds.lift (b : Blk α) : Adds (StateT.lift b : SubM α) 0 := by
  intro F c a G c' hr hs
  obtain ⟨a', c1, _, e⟩ := (lift_ok _ _ _ _).1 hr
  have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
  rw [e2]
  exact ⟨trivial, [], rfl, Added.refl hs⟩

theorem Adds.monadLift (b : Blk α) : Adds (MonadLiftT.monadLift b : SubM α) 0 := Adds.lift b

theorem Adds.ask (f : Fork → Option α) : Adds (SubM.ask f) 0 := by
  intro F c a G c' hr hs
  obtain ⟨a', _, e⟩ := (ask_ok _ _ _ _).1 hr
  have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
  rw [e2]
  exact ⟨trivial, [], rfl, Added.refl hs⟩

theorem Adds.get : Adds (MonadState.get : SubM Fork) 0 := by
  intro F c a G c' hr hs
  have e : ((F, F), c) = ((a, G), c') := Except.ok.inj hr
  have e2 : F = G := congrArg (fun x : (Fork × Fork) × Ctx => x.1.2) e
  rw [← e2]
  exact ⟨trivial, [], rfl, Added.refl hs⟩

theorem AddsR.getO (x : Option α) : AddsR (SubM.get x) 0 fun a => x = some a := by
  intro F c a G c' hr hs
  obtain ⟨a', h1, e⟩ := (get_ok _ _ _ _).1 hr
  have e1 : a = a' := congrArg (fun x : (α × Fork) × Ctx => x.1.1) e
  have e2 : G = F := congrArg (fun x : (α × Fork) × Ctx => x.1.2) e
  rw [e1, e2]
  exact ⟨h1, [], rfl, Added.refl hs⟩

theorem Adds.getO (x : Option α) : Adds (SubM.get x) 0 := (AddsR.getO x).mono fun _ _ => trivial

theorem Adds.must (b : Bool) : Adds (SubM.must b) 0 := by
  intro F c a G c' hr hs
  obtain ⟨_, e⟩ := (must_ok _ _ _ _).1 hr
  have e2 : G = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
  rw [e2]
  exact ⟨trivial, [], rfl, Added.refl hs⟩

theorem Adds.ite {p : Prop} [Decidable p] {x y : SubM α} {n m : ℕ} (hx : Adds x n)
    (hy : Adds y m) : Adds (if p then x else y) (if p then n else m) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos hp]
    exact hx
  · rw [if_neg hp, if_neg hp]
    exact hy

theorem Adds.lin (f : Aff) : Adds (SubM.lin f) 1 := by
  intro F c a G c' hr hs
  obtain ⟨h1, _⟩ := (SubM.lin_run f F G c c').1 hr
  exact ⟨trivial, [(f, #[])], rfl, added_lin hs h1⟩

theorem Adds.paid (i : ℕ) : Adds (SubM.paid i) 0 := by
  intro F c a G c' hr hs
  unfold SubM.paid at hr
  obtain ⟨G', h1, e⟩ := (change_ok _ _ _ _).1 hr
  have e2 : G = G' := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e
  rw [e2, ← Option.some.inj h1]
  exact ⟨trivial, [], rfl, added_paid hs i⟩

/-! ### loops -/

theorem Adds.foldlM {f : σ → α → SubM σ} {k : α → ℕ} (hf : ∀ s a, Adds (f s a) (k a)) :
    ∀ (l : List α) (s : σ), Adds (l.foldlM f s) (l.map k).sum
  | [], s => Adds.pure s
  | a :: l, s => by
    rw [List.foldlM_cons, List.map_cons, List.sum_cons]
    exact (hf s a).bind fun s' => Adds.foldlM hf l s'

theorem Adds.arrayFoldlM {f : σ → α → SubM σ} {k : α → ℕ} (hf : ∀ s a, Adds (f s a) (k a))
    (l : Array α) (s : σ) : Adds (l.foldlM f s) (l.toList.map k).sum := by
  rw [← Array.foldlM_toList]
  exact Adds.foldlM hf _ s

theorem Adds.forM {f : α → SubM PUnit} {k : α → ℕ} (hf : ∀ a, Adds (f a) (k a)) :
    ∀ l : List α, Adds (l.forM f) (l.map k).sum
  | [] => Adds.pure _
  | a :: l => by
    show Adds (f a >>= fun _ => l.forM f) _
    rw [List.map_cons, List.sum_cons]
    exact (hf a).bind fun _ => Adds.forM hf l

theorem Adds.arrayForM {f : α → SubM PUnit} {k : α → ℕ} (hf : ∀ a, Adds (f a) (k a))
    (l : Array α) : Adds (l.forM f) (l.toList.map k).sum := by
  unfold Array.forM
  exact Adds.arrayFoldlM (fun _ a => hf a) l _

/-- A loop whose body always goes on. -/
theorem Adds.forIn {f : α → σ → SubM (ForInStep σ)} {k : α → ℕ}
    (hf : ∀ a s, AddsR (f a s) (k a) fun r => ∃ b, r = .yield b) :
    ∀ (l : List α) (s : σ), Adds (ForIn.forIn l s f) (l.map k).sum
  | [], s => by
    rw [List.forIn_nil]
    exact Adds.pure s
  | a :: l, s => by
    rw [List.forIn_cons, List.map_cons, List.sum_cons]
    refine AddsR.bind (hf a s) fun r hr => ?_
    obtain ⟨b, rfl⟩ := hr
    exact Adds.forIn hf l b

/-! ### routines that add no claim -/

/-- The routine adds no claim. -/
def Quiet (x : SubM α) : Prop := Adds x 0

theorem Quiet.pure (a : α) : Quiet (Pure.pure a : SubM α) := Adds.pure a

theorem Quiet.bind {x : SubM α} {f : α → SubM β} (hx : Quiet x) (hf : ∀ a, Quiet (f a)) :
    Quiet (x >>= f) := Adds.bind hx hf

theorem Quiet.lift (b : Blk α) : Quiet (StateT.lift b : SubM α) := Adds.lift b
theorem Quiet.monadLift (b : Blk α) : Quiet (MonadLiftT.monadLift b : SubM α) := Adds.lift b
theorem Quiet.liftM (b : Blk α) : Quiet (liftM b : SubM α) := Adds.lift b
theorem Quiet.ask (f : Fork → Option α) : Quiet (SubM.ask f) := Adds.ask f
theorem Quiet.get : Quiet (MonadState.get : SubM Fork) := Adds.get
theorem Quiet.getO (x : Option α) : Quiet (SubM.get x) := Adds.getO x
theorem Quiet.must (b : Bool) : Quiet (SubM.must b) := Adds.must b
theorem Quiet.paid (i : ℕ) : Quiet (SubM.paid i) := Adds.paid i

theorem Quiet.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Quiet x) (hy : Quiet y) :
    Quiet (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Quiet.foldlM {f : σ → α → SubM σ} (hf : ∀ s a, Quiet (f s a)) :
    ∀ (l : List α) (s : σ), Quiet (l.foldlM f s)
  | [], s => Quiet.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Quiet.foldlM hf l s'

theorem Quiet.arrayFoldlM {f : σ → α → SubM σ} (hf : ∀ s a, Quiet (f s a)) (l : Array α) (s : σ) :
    Quiet (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Quiet.foldlM hf _ s

theorem AddsR.qbind' {x : SubM α} {f : α → SubM β} {n : ℕ} {post : β → Prop} (hx : Quiet x)
    (hf : ∀ a, AddsR (f a) n post) : AddsR (x >>= f) n post :=
  (AddsR.bind hx fun a _ => hf a).cast (Nat.zero_add n)

theorem sum_const (l : List α) (k : ℕ) : (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons]
    ring

end

/-- One step of the tactic quiet. -/
macro "quiet_step" : tactic => `(tactic| first
  | exact Quiet.pure _ | exact Quiet.lift _ | exact Quiet.monadLift _ | exact Quiet.liftM _
  | exact Quiet.ask _ | exact Quiet.get | exact Quiet.getO _ | exact Quiet.must _
  | exact Quiet.paid _
  | assumption
  | (apply_assumption)
  | refine Quiet.bind ?_ (fun _ => ?_)
  | refine Quiet.foldlM (fun _ _ => ?_) _ _
  | refine Quiet.arrayFoldlM (fun _ _ => ?_) _ _
  | refine Quiet.ite ?_ ?_
  | split
  | dsimp only)

/-- Proves Quiet x by the rules, for a routine whose definition has been opened. -/
macro "quiet" : tactic => `(tactic| repeat' quiet_step)

end Fo
