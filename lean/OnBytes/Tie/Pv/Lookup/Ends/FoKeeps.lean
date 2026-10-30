-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeeps.lean.
Routines of a sub-proof that keep what lies under the filled slots.

`Keeps x`: whenever the routine x, run from a state F whose slots' arrays have their sizes, returns
and leaves the state G, then G is a later state than F (`Later`,
OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean: the slot counter has not fallen, the number of slots is
the same, and every slot that is filled in F stays filled and keeps what was shown and its factor)
and G's arrays have their sizes. It says nothing of a run in which x refuses: a routine that never
returns has the property idly. The file has the rules by which the property passes through the ways
in which routines are put together (pure, bind, a lifted routine of the channel, a branch, a loop)
and proves it of the steps that are lifted from the channel, of those that only read the state, of
SubM.takeSlots and of the filling of a run of slots. SubM.hide and the steps that add claims are in
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean. No statement is made of SubM.slots: it sets up the
slots anew, so it does not keep what lay under them (by reading; no theorem).

The tactic `keeps`, which proves Keeps of a routine by these rules, is not in this file but in
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsSteps.lean.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Tie.Pv.Psc.PscFork
import OnBytes.Model.Look

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The routine keeps what lies under the filled slots, and the arrays' sizes. -/
def Keeps {α : Type} (x : SubM α) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') → Sized F →
    Later F G ∧ Sized G

section
variable {α β : Type}

theorem Keeps.pure (a : α) : Keeps (Pure.pure a : SubM α) := by
  intro F c b G c' h hS
  rw [pure_ok] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using h
  exact ⟨Later.refl _, hS⟩

theorem Keeps.bind {x : SubM α} {f : α → SubM β} (hx : Keeps x) (hf : ∀ a, Keeps (f a)) :
    Keeps (x >>= f) := by
  intro F c b G c' h hS
  rw [bind_ok] at h
  obtain ⟨a, F1, c1, h1, h2⟩ := h
  obtain ⟨l1, s1⟩ := hx _ _ _ _ _ h1 hS
  obtain ⟨l2, s2⟩ := hf a _ _ _ _ _ h2 s1
  exact ⟨l1.trans l2, s2⟩

theorem Keeps.lift (b : Blk α) : Keeps (StateT.lift b : SubM α) := by
  intro F c a G c' h hS
  rw [lift_ok] at h
  obtain ⟨a', c1, -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨Later.refl _, hS⟩

theorem Keeps.ask (f : Fork → Option α) : Keeps (SubM.ask f) := by
  intro F c a G c' h hS
  rw [ask_ok] at h
  obtain ⟨a', -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨Later.refl _, hS⟩

theorem Keeps.change {f : Fork → Option Fork}
    (hf : ∀ F G, f F = some G → Sized F → Later F G ∧ Sized G) : Keeps (SubM.change f) := by
  intro F c a G c' h hS
  rw [change_ok] at h
  obtain ⟨G', hG, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf _ _ hG hS

theorem Keeps.take {f : Fork → Option (α × Fork)}
    (hf : ∀ F y, f F = some y → Sized F → Later F y.2 ∧ Sized y.2) : Keeps (SubM.take f) := by
  intro F c a G c' h hS
  rw [take_ok] at h
  obtain ⟨y, hy, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf _ _ hy hS

theorem Keeps.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Keeps x) (hy : Keeps y) :
    Keeps (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Keeps.map {x : SubM α} (f : α → β) (hx : Keeps x) : Keeps (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => Keeps.pure _

theorem Keeps.monadLift (b : Blk α) : Keeps (MonadLiftT.monadLift b : SubM α) := Keeps.lift b

theorem Keeps.liftM (b : Blk α) : Keeps (liftM b : SubM α) := Keeps.lift b

theorem Keeps.get : Keeps (MonadState.get : SubM Fork) := by
  intro F c a G c' h hS
  have e : ((F, F), c) = ((a, G), c') := Except.ok.inj h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨Later.refl _, hS⟩

/-! ### loops -/

theorem Keeps.foldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Keeps (f s a)) :
    ∀ (l : List α) (s : σ), Keeps (l.foldlM f s)
  | [], s => Keeps.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Keeps.foldlM hf l s'

theorem Keeps.arrayFoldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Keeps (f s a))
    (l : Array α) (s : σ) : Keeps (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Keeps.foldlM hf _ s

theorem Keeps.forIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Keeps (f a s)) :
    ∀ (l : List α) (s : σ), Keeps (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Keeps.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact Keeps.pure b
    | yield b => exact Keeps.forIn hf l b

theorem Keeps.arrayForIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Keeps (f a s))
    (l : Array α) (s : σ) : Keeps (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Keeps.forIn hf _ s

theorem Keeps.forM {f : α → SubM PUnit} (hf : ∀ a, Keeps (f a)) :
    ∀ l : List α, Keeps (l.forM f)
  | [] => Keeps.pure _
  | a :: l => by
    show Keeps (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => Keeps.forM hf l

theorem Keeps.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Keeps (f a)) (l : Array α) :
    Keeps (l.forM f) := by
  unfold Array.forM
  exact Keeps.arrayFoldlM (fun _ a => hf a) l _

theorem Keeps.mapM {f : α → SubM β} (hf : ∀ a, Keeps (f a)) : ∀ l : List α, Keeps (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact Keeps.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (Keeps.mapM hf l).bind fun _ => Keeps.pure _

theorem Keeps.arrayMapM {f : α → SubM β} (hf : ∀ a, Keeps (f a)) (l : Array α) :
    Keeps (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (Keeps.mapM hf _).map _

end

/-! ### the steps on the state -/

/-- A step that turns neither the slots' arrays nor their numbers. -/
theorem later_of_same {F G : Fork} (h1 : G.next = F.next) (h2 : G.ns = F.ns) (h3 : G.vp = F.vp)
    (h4 : G.mf = F.mf) (h5 : G.gotF = F.gotF) (hS : Sized F) : Later F G ∧ Sized G := by
  refine ⟨⟨le_of_eq h1.symm, h2, fun j hj => ?_⟩, ?_⟩
  · unfold Filled at *
    rw [h3, h4, h5]
    exact ⟨hj, rfl, rfl⟩
  · unfold Sized at *
    rw [h2, h3, h4, h5]
    exact hS

theorem Keeps.must (b : Bool) : Keeps (SubM.must b) := Keeps.lift _
theorem Keeps.test (b : Bool) : Keeps (SubM.test b) := Keeps.lift _
theorem Keeps.getO {α : Type} (x : Option α) : Keeps (SubM.get x) := Keeps.lift _
theorem Keeps.read (n : ℕ) : Keeps (SubM.read n) := Keeps.lift _
theorem Keeps.readSum : Keeps SubM.readSum := Keeps.lift _
theorem Keeps.answer (r : RoundName) : Keeps (SubM.answer r) := Keeps.lift _
theorem Keeps.answerNotZero (r : RoundName) : Keeps (SubM.answerNotZero r) := Keeps.lift _
theorem Keeps.point (r : RoundName) (n : ℕ) : Keeps (SubM.point r n) := Keeps.lift _
theorem Keeps.batch (n : ℕ) : Keeps (SubM.batch n) := Keeps.lift _
theorem Keeps.batchOpen : Keeps SubM.batchOpen := Keeps.lift _
theorem Keeps.batchRows (n : ℕ) : Keeps (SubM.batchRows n) := Keeps.lift _
theorem Keeps.empty (r : RoundName) : Keeps (SubM.empty r) := Keeps.lift _
theorem Keeps.trits (a b : ℕ) : Keeps (SubM.trits a b) := Keeps.lift _
theorem Keeps.slot : Keeps SubM.slot := Keeps.ask _
theorem Keeps.shown (j : ℕ) : Keeps (SubM.shown j) := Keeps.ask _
theorem Keeps.publicPart (a : Aff) : Keeps (SubM.publicPart a) := Keeps.ask _
theorem Keeps.claims : Keeps SubM.claims := Keeps.ask _
theorem Keeps.allTaken : Keeps SubM.allTaken := Keeps.ask _
theorem Keeps.settle (n : ℕ) : Keeps (SubM.settle n) := Keeps.ask _

theorem Keeps.takeSlots (n : ℕ) : Keeps (SubM.takeSlots n) :=
  Keeps.take fun F y h hS => by
    obtain rfl := Option.some.inj h
    exact ⟨took_later F n, took_sized n hS⟩

theorem Keeps.hideRun (j : ℕ) (v : Array E) (f : E) : Keeps (SubM.change (·.hideRun j v f)) :=
  Keeps.change fun _ _ h hS => ⟨hideRun_later hS h, (hideRun_ok _ _ _ _ _ hS h).2.1⟩

end Fo
