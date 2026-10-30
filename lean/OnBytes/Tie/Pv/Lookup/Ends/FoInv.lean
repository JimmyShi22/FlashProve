-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInv.lean.
Routines of a sub-proof that keep a property of the sub-proof's state.

`Inv I x`: whenever the routine x, run from a state that has the property I, returns, the state that
it leaves has the property I. The file has the rules by which this passes through the ways in which
routines are put together (pure, bind, a lifted routine of the channel, a branch, a loop).
`Book F G`: G differs from F at most in the books on the claims (their number, the batching
element and its marks, the list of owed claims, the door's mark).
`Prim I`: the property I is kept by each step on the state that the routines use: taking slots,
filling slots, adding a form or runs to the one equation, marking an array as committed, giving the
virtual rows their weights, writing in one virtual row, and every step that turns the books alone.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoForm
import OnBytes.Tie.Pv.Psc.PscFork
import OnBytes.Model.Look
import OnBytes.Model.Trees
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The routine keeps the property I of the state. -/
def Inv {α : Type} (I : Fork → Prop) (x : SubM α) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : α) (G : Fork) (c' : Ctx), x F c = .ok ((a, G), c') → I F → I G

section
variable {α β : Type} {I : Fork → Prop}

theorem Inv.pure (a : α) : Inv I (Pure.pure a : SubM α) := by
  intro F c b G c' h hS
  rw [pure_ok] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using h
  exact hS

theorem Inv.bind {x : SubM α} {f : α → SubM β} (hx : Inv I x) (hf : ∀ a, Inv I (f a)) :
    Inv I (x >>= f) := by
  intro F c b G c' h hS
  rw [bind_ok] at h
  obtain ⟨a, F1, c1, h1, h2⟩ := h
  exact hf a _ _ _ _ _ h2 (hx _ _ _ _ _ h1 hS)

theorem Inv.lift (b : Blk α) : Inv I (StateT.lift b : SubM α) := by
  intro F c a G c' h hS
  rw [lift_ok] at h
  obtain ⟨a', c1, -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hS

theorem Inv.ask (f : Fork → Option α) : Inv I (SubM.ask f) := by
  intro F c a G c' h hS
  rw [ask_ok] at h
  obtain ⟨a', -, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hS

theorem Inv.change {f : Fork → Option Fork}
    (hf : ∀ F G, f F = some G → I F → I G) : Inv I (SubM.change f) := by
  intro F c a G c' h hS
  rw [change_ok] at h
  obtain ⟨G', hG, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf _ _ hG hS

theorem Inv.take {f : Fork → Option (α × Fork)}
    (hf : ∀ F y, f F = some y → I F → I y.2) : Inv I (SubM.take f) := by
  intro F c a G c' h hS
  rw [take_ok] at h
  obtain ⟨y, hy, e⟩ := h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hf _ _ hy hS

theorem Inv.ite {p : Prop} [Decidable p] {x y : SubM α} (hx : Inv I x) (hy : Inv I y) :
    Inv I (if p then x else y) := by
  split
  · exact hx
  · exact hy

theorem Inv.map {x : SubM α} (f : α → β) (hx : Inv I x) : Inv I (f <$> x) := by
  rw [← bind_pure_comp]
  exact hx.bind fun _ => Inv.pure _

theorem Inv.monadLift (b : Blk α) : Inv I (MonadLiftT.monadLift b : SubM α) := Inv.lift b

theorem Inv.liftM (b : Blk α) : Inv I (liftM b : SubM α) := Inv.lift b

theorem Inv.get : Inv I (MonadState.get : SubM Fork) := by
  intro F c a G c' h hS
  have e : ((F, F), c) = ((a, G), c') := Except.ok.inj h
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  exact hS

/-! ### loops -/

theorem Inv.foldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Inv I (f s a)) :
    ∀ (l : List α) (s : σ), Inv I (l.foldlM f s)
  | [], s => Inv.pure s
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact (hf s a).bind fun s' => Inv.foldlM hf l s'

theorem Inv.arrayFoldlM {σ : Type} {f : σ → α → SubM σ} (hf : ∀ s a, Inv I (f s a))
    (l : Array α) (s : σ) : Inv I (l.foldlM f s) := by
  rw [← Array.foldlM_toList]
  exact Inv.foldlM hf _ s

theorem Inv.forIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Inv I (f a s)) :
    ∀ (l : List α) (s : σ), Inv I (ForIn.forIn l s f)
  | [], s => by
    rw [List.forIn_nil]
    exact Inv.pure s
  | a :: l, s => by
    rw [List.forIn_cons]
    refine (hf a s).bind fun r => ?_
    cases r with
    | done b => exact Inv.pure b
    | yield b => exact Inv.forIn hf l b

theorem Inv.arrayForIn {σ : Type} {f : α → σ → SubM (ForInStep σ)} (hf : ∀ a s, Inv I (f a s))
    (l : Array α) (s : σ) : Inv I (ForIn.forIn l s f) := by
  rw [← Array.forIn_toList]
  exact Inv.forIn hf _ s

theorem Inv.forM {f : α → SubM PUnit} (hf : ∀ a, Inv I (f a)) :
    ∀ l : List α, Inv I (l.forM f)
  | [] => Inv.pure _
  | a :: l => by
    show Inv I (f a >>= fun _ => l.forM f)
    exact (hf a).bind fun _ => Inv.forM hf l

theorem Inv.arrayForM {f : α → SubM PUnit} (hf : ∀ a, Inv I (f a)) (l : Array α) :
    Inv I (l.forM f) := by
  unfold Array.forM
  exact Inv.arrayFoldlM (fun _ a => hf a) l _

theorem Inv.mapM {f : α → SubM β} (hf : ∀ a, Inv I (f a)) : ∀ l : List α, Inv I (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact Inv.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun _ => (Inv.mapM hf l).bind fun _ => Inv.pure _

theorem Inv.arrayMapM {f : α → SubM β} (hf : ∀ a, Inv I (f a)) (l : Array α) :
    Inv I (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (Inv.mapM hf _).map _

end


/-! ### the steps on the state -/

/-- The two states differ at most in the books on the claims. -/
def Book (F G : Fork) : Prop :=
  G.trees = F.trees ∧ G.ns = F.ns ∧ G.next = F.next ∧ G.vp = F.vp ∧ G.mf = F.mf ∧ G.LS = F.LS ∧
    G.gotF = F.gotF ∧ G.c0 = F.c0

/-- The steps on the state keep the property. -/
class Prim (I : Fork → Prop) : Prop where
  took : ∀ (F : Fork) (n : ℕ), I F → I (took F n)
  hideRun : ∀ (F G : Fork) (j : ℕ) (v : Array E) (f : E), F.hideRun j v f = some G → I F → I G
  push : ∀ (F G : Fork) (w : E) (a : Aff), F.push w a = some G → I F → I G
  pushRuns : ∀ (F G : Fork) (k : E) (runs : Array Run2), F.pushRuns k runs = some G → I F → I G
  rootTaken : ∀ (F : Fork) (t w : ℕ), I F → I (F.rootTaken t w)
  fill : ∀ (F : Fork) (T : Tail2), I F → I (t2FillL F T)
  onRow : ∀ (F : Fork) (t r : ℕ) (f : HRow → HRow), I F → I (HTailF2.onRow F t r f)
  book : ∀ F G : Fork, Book F G → I F → I G

section
variable {I : Fork → Prop}

theorem Inv.must (b : Bool) : Inv I (SubM.must b) := Inv.lift _
theorem Inv.test (b : Bool) : Inv I (SubM.test b) := Inv.lift _
theorem Inv.getO {α : Type} (x : Option α) : Inv I (SubM.get x) := Inv.lift _
theorem Inv.read (n : ℕ) : Inv I (SubM.read n) := Inv.lift _
theorem Inv.readSum : Inv I SubM.readSum := Inv.lift _
theorem Inv.answer (r : RoundName) : Inv I (SubM.answer r) := Inv.lift _
theorem Inv.answerNotZero (r : RoundName) : Inv I (SubM.answerNotZero r) := Inv.lift _
theorem Inv.point (r : RoundName) (n : ℕ) : Inv I (SubM.point r n) := Inv.lift _
theorem Inv.batch (n : ℕ) : Inv I (SubM.batch n) := Inv.lift _
theorem Inv.batchOpen : Inv I SubM.batchOpen := Inv.lift _
theorem Inv.batchRows (n : ℕ) : Inv I (SubM.batchRows n) := Inv.lift _
theorem Inv.empty (r : RoundName) : Inv I (SubM.empty r) := Inv.lift _
theorem Inv.trits (a b : ℕ) : Inv I (SubM.trits a b) := Inv.lift _
theorem Inv.slot : Inv I SubM.slot := Inv.ask _
theorem Inv.shown (j : ℕ) : Inv I (SubM.shown j) := Inv.ask _
theorem Inv.publicPart (a : Aff) : Inv I (SubM.publicPart a) := Inv.ask _
theorem Inv.claims : Inv I SubM.claims := Inv.ask _
theorem Inv.allTaken : Inv I SubM.allTaken := Inv.ask _
theorem Inv.settle (n : ℕ) : Inv I (SubM.settle n) := Inv.ask _


variable [Prim I]

theorem Inv.takeSlots (n : ℕ) : Inv I (SubM.takeSlots n) :=
  Inv.take fun F y h hS => by
    obtain rfl := Option.some.inj h
    exact Prim.took F n hS

theorem Inv.hideRun (j : ℕ) (v : Array E) (f : E) : Inv I (SubM.change (·.hideRun j v f)) :=
  Inv.change fun _ _ h hS => Prim.hideRun _ _ _ _ _ h hS

end
end Fo
