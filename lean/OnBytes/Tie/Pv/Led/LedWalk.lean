-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedWalk.lean: rules by which "this routine adds just this list of claims" passes
through the text of a routine of the shipped Lean verifier.

A sub-proof's check adds its claims one by one, by Fork.lin or by t2Lin. The state keeps the
coefficients of one equation and no list of the forms. Adds F l G (LedAdds.lean) says that G comes
from F by adding the forms of l, with steps between that add nothing. This file has that relation
for routines.

Main names.
  Adds.trans: one walk behind another adds the two lists in a row. adds_lins: Fork.lins walks.
  appL a b: two lists that may be missing, in a row.
  Walks r P ol: whenever the routine r returns, with a value a and from a state F to a state G, the
    value has the property P, the list ol is there, say l, and Adds F l G.
  The rules: walks_pure, walks_keep (a routine that adds nothing), walks_still (a routine that
    leaves the state as it was), walks_lift (a call on the channel), walks_get (a value that must be
    there), walks_lin, walks_t2Lin, walks_bind, walks_after, walks_before, walks_get_bind,
    walks_lift_bind, walks_mono, walks_forIn (a loop over a list, with any step), walks_yield.
  hideRun_keeps: filling a run of slots adds nothing (Keeps, LedAdds.lean).
  walks_adds: a run of such a routine, as a walk.

What this file does not claim. No routine of a sub-proof is treated here. Nothing where a routine
does not return.


-/
import OnBytes.Tie.Pv.Psc.PscRun
import OnBytes.Tie.Pv.Led.LedCoef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

/-! ## Walks in a row -/

theorem Adds.trans {F G H : Model.Fork} {l l' : List Model.Aff} (a : Adds F l G)
    (b : Adds G l' H) : Adds F (l ++ l') H := by
  induction b with
  | nil => simpa using a
  | keep _ k ih => exact Adds.keep ih k
  | lin _ h ih =>
    rw [← List.append_assoc]
    exact Adds.lin ih h
  | runs _ h1 h2 h3 ih =>
    rw [← List.append_assoc]
    exact Adds.runs ih h1 h2 h3

theorem adds_lins : ∀ (l : List Model.Aff) (F G : Model.Fork), F.lins l = some G → Adds F l G
  | [], F, G, h => by
    have e : F = G := by simpa [Model.Fork.lins] using h
    subst e
    exact Adds.nil F
  | f :: l, F, G, h => by
    unfold Model.Fork.lins at h
    rw [List.foldlM_cons] at h
    cases hq : F.lin f with
    | none => simp [hq] at h
    | some F1 =>
      have h2 : F1.lins l = some G := by simpa [Model.Fork.lins, hq] using h
      exact Adds.trans (Adds.lin (Adds.nil F) hq) (adds_lins l F1 G h2)

/-- Two lists that may be missing, in a row. -/
def appL (a b : Option (List Model.Aff)) : Option (List Model.Aff) :=
  a.bind fun x => b.map (x ++ ·)

theorem appL_some_some (x y : List Model.Aff) : appL (some x) (some y) = some (x ++ y) := rfl

/-! ## Routines -/

/-- Whenever the routine returns, its value has the property P, the list is there, and the new state
comes from the old one by adding just that list. -/
def Walks {α : Type} (r : Model.SubM α) (P : α → Prop) (ol : Option (List Model.Aff)) : Prop :=
  ∀ (F G : Model.Fork) (c c' : Ctx) (a : α), r F c = .ok ((a, G), c') →
    P a ∧ ∃ l, ol = some l ∧ Adds F l G

/-- A run of such a routine, as a walk. -/
theorem walks_adds {α : Type} {r : Model.SubM α} {P : α → Prop} {ol : Option (List Model.Aff)}
    (w : Walks r P ol) {F G : Model.Fork} {c c' : Ctx} {a : α}
    (h : r F c = .ok ((a, G), c')) : P a ∧ ∃ l, ol = some l ∧ Adds F l G := w F G c c' a h

theorem walks_mono {α : Type} {r : Model.SubM α} {P Q : α → Prop}
    {ol : Option (List Model.Aff)} (w : Walks r P ol) (h : ∀ a, P a → Q a) : Walks r Q ol :=
  fun F G c c' a hr => ⟨h a (w F G c c' a hr).1, (w F G c c' a hr).2⟩

/-- A routine that adds nothing. -/
theorem walks_keep {α : Type} {r : Model.SubM α} {P : α → Prop}
    (h : ∀ (F G : Model.Fork) (c c' : Ctx) (a : α), r F c = .ok ((a, G), c') → Keeps F G ∧ P a) :
    Walks r P (some []) := fun F G c c' a hr =>
  ⟨(h F G c c' a hr).2, [], rfl, Adds.keep (Adds.nil F) (h F G c c' a hr).1⟩

/-- A routine that leaves the state as it was. -/
theorem walks_still {α : Type} {r : Model.SubM α} {P : α → Prop}
    (h : ∀ (F G : Model.Fork) (c c' : Ctx) (a : α), r F c = .ok ((a, G), c') → G = F ∧ P a) :
    Walks r P (some []) :=
  walks_keep fun F G c c' a hr => by
    obtain ⟨rfl, p⟩ := h F G c c' a hr
    exact ⟨Keeps.refl _, p⟩

theorem walks_pure {α : Type} (a : α) {P : α → Prop} (h : P a) :
    Walks (pure a : Model.SubM α) P (some []) :=
  walks_still fun F G c c' x hr => by
    have e := (PscRun.pure_ok a F c _).1 hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, _⟩ := e
    exact ⟨rfl, h⟩

/-- A call on the channel: a test, a note, a message, a draw. -/
theorem walks_lift {α : Type} (b : Blk α) :
    Walks (StateT.lift b : Model.SubM α) (fun _ => True) (some []) :=
  walks_still fun F G c c' x hr => by
    obtain ⟨a, c1, _, e⟩ := (PscRun.lift_ok b F c _).1 hr
    simp only [Prod.mk.injEq] at e
    exact ⟨e.1.2, trivial⟩

/-- A value that must be there. -/
theorem walks_get {α : Type} (x : Option α) :
    Walks (Model.SubM.get x) (fun a => x = some a) (some []) :=
  walks_still fun F G c c' a hr => by
    obtain ⟨a', h1, e⟩ := (PscRun.get_ok x F c _).1 hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨⟨rfl, rfl⟩, _⟩ := e
    exact ⟨rfl, h1⟩

/-- One claim by a form. -/
theorem walks_lin (f : Model.Aff) : Walks (Model.SubM.lin f) (fun _ => True) (some [f]) :=
  fun F G c c' _ hr =>
    ⟨trivial, [f], rfl, Adds.lin (Adds.nil F) ((Model.SubM.lin_run f F G c c').1 hr).1⟩

/-- One claim by a form and runs of entries. -/
theorem walks_t2Lin (a : Model.Aff) (rs : Array Model.Run2) :
    Walks (Model.t2Lin a rs) (fun _ => True) (some [claimForm a rs]) := by
  intro F G c c' _ h
  unfold Model.t2Lin at h
  obtain ⟨k, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨_, F2, c2, h3, h4⟩ := (PscRun.bind_ok _ _ _ _ _).1 h2
  obtain ⟨y, e1, e1'⟩ := (PscRun.take_ok _ _ _ _).1 h1
  obtain ⟨G2, e2, e2'⟩ := (PscRun.change_ok _ _ _ _).1 h3
  obtain ⟨G3, e3, e3'⟩ := (PscRun.change_ok _ _ _ _).1 h4
  simp only [Prod.mk.injEq] at e1' e2' e3'
  obtain ⟨rfl, rfl⟩ := e1'
  obtain ⟨⟨_, rfl⟩, rfl⟩ := e2'
  obtain ⟨⟨_, rfl⟩, _⟩ := e3'
  exact ⟨trivial, _, rfl, Adds.runs (Adds.nil F) e1 e2 e3⟩

/-- One routine behind another, where the second's list does not hang on the first's value. -/
theorem walks_bind {α β : Type} {r : Model.SubM α} {k : α → Model.SubM β} {Q : α → Prop}
    {P : β → Prop} {a b : Option (List Model.Aff)} (hr : Walks r Q a)
    (hk : ∀ x, Q x → Walks (k x) P b) : Walks (r >>= k) P (appL a b) := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨q, la, rfl, wa⟩ := hr F F1 c c1 x h1
  obtain ⟨p, lb, rfl, wb⟩ := hk x q F1 G c1 c' y h2
  exact ⟨p, la ++ lb, rfl, wa.trans wb⟩

/-- A routine that adds nothing, and then one that may read its value. -/
theorem walks_after {α β : Type} {r : Model.SubM α} {k : α → Model.SubM β} {Q : α → Prop}
    {P : β → Prop} {b : Option (List Model.Aff)} (hr : Walks r Q (some []))
    (hk : ∀ x, Q x → Walks (k x) P b) : Walks (r >>= k) P b := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨q, la, e, wa⟩ := hr F F1 c c1 x h1
  obtain rfl : [] = la := Option.some.inj e
  obtain ⟨p, lb, e2, wb⟩ := hk x q F1 G c1 c' y h2
  exact ⟨p, lb, e2, by simpa using wa.trans wb⟩

/-- A routine, and then one that adds nothing. -/
theorem walks_before {α β : Type} {r : Model.SubM α} {k : α → Model.SubM β} {Q : α → Prop}
    {P : β → Prop} {a : Option (List Model.Aff)} (hr : Walks r Q a)
    (hk : ∀ x, Q x → Walks (k x) P (some [])) : Walks (r >>= k) P a := by
  intro F G c c' y h
  obtain ⟨x, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨q, la, e, wa⟩ := hr F F1 c c1 x h1
  obtain ⟨p, lb, e2, wb⟩ := hk x q F1 G c1 c' y h2
  obtain rfl : [] = lb := Option.some.inj e2
  exact ⟨p, la, e, by simpa using wa.trans wb⟩

/-- A value that must be there, and then a routine whose list may read it. -/
theorem walks_get_bind {α β : Type} (x : Option α) {k : α → Model.SubM β} {P : β → Prop}
    {l : α → Option (List Model.Aff)} (hk : ∀ a, Walks (k a) P (l a)) :
    Walks (Model.SubM.get x >>= k) P (x.bind l) := by
  intro F G c c' y h
  obtain ⟨a, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
  obtain ⟨a', e0, e⟩ := (PscRun.get_ok x F c _).1 h1
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  rw [e0]
  exact hk a F1 G c1 c' y h2

/-- A call on the channel, and then a routine. -/
theorem walks_lift_bind {α β : Type} (b : Blk α) {k : α → Model.SubM β} {P : β → Prop}
    {l : Option (List Model.Aff)} (hk : ∀ a, Walks (k a) P l) :
    Walks ((StateT.lift b : Model.SubM α) >>= k) P l :=
  walks_after (walks_lift b) fun a _ => hk a

/-- The end of a loop's step. -/
theorem walks_yield :
    Walks (pure (ForInStep.yield PUnit.unit) : Model.SubM (ForInStep PUnit))
      (fun s => s = ForInStep.yield PUnit.unit) (some []) :=
  walks_pure _ rfl

/-- A loop over a list, with any step: if each run of the step goes on and adds the list of its
member, the loop adds the lists of all members, in a row. -/
theorem walks_forIn {α : Type} (f : α → PUnit → Model.SubM (ForInStep PUnit))
    (l : α → Option (List Model.Aff))
    (hf : ∀ a, Walks (f a PUnit.unit) (fun s => s = ForInStep.yield PUnit.unit) (l a)) :
    ∀ xs : List α, Walks (forIn xs PUnit.unit f) (fun _ => True) ((xs.mapM l).map List.flatten)
  | [] => by
    rw [List.forIn_nil]
    exact walks_pure _ trivial
  | x :: xs => by
    rw [List.forIn_cons]
    intro F G c c' u h
    obtain ⟨s, F1, c1, h1, h2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
    obtain ⟨rfl, lx, ex, wx⟩ := hf x F F1 c c1 s h1
    obtain ⟨_, lr, er, wr⟩ := walks_forIn f l hf xs F1 G c1 c' u h2
    refine ⟨trivial, lx ++ lr, ?_, wx.trans wr⟩
    cases hm : xs.mapM l with
    | none => simp [hm] at er
    | some L =>
      have e2 : L.flatten = lr := by simpa [hm] using er
      simp [List.mapM_cons, ex, hm, e2]

/-- Filling a run of slots adds nothing. -/
theorem hideRun_keeps {F G : Model.Fork} {first : Nat} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : Keeps F G := by
  have steps : ∀ (l : List E) (s x : Nat × Model.Fork),
      l.foldlM (Model.Fork.hideStep factor) s = some x → Keeps s.2 x.2 := by
    intro l
    induction l with
    | nil =>
      intro s x hx
      have e : s = x := by simpa using hx
      subst e
      exact Keeps.refl _
    | cons y l ih =>
      rintro ⟨j, G0⟩ x hx
      rw [List.foldlM_cons] at hx
      cases hh : G0.hide j y factor with
      | none => simp [Model.Fork.hideStep, hh] at hx
      | some H =>
        have h2 : l.foldlM (Model.Fork.hideStep factor) (j + 1, H) = some x := by
          simpa [Model.Fork.hideStep, hh] using hx
        exact (hide_keeps hh).trans (ih _ x h2)
  unfold Model.Fork.hideRun at h
  split at h
  · rename_i x hx
    rw [← Array.foldlM_toList] at hx
    obtain rfl := Option.some.inj h
    exact steps v.toList (first, F) x hx
  · simp at h

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.Adds.trans
#print axioms OnBytes.Road.Rows.walks_t2Lin
#print axioms OnBytes.Road.Rows.walks_bind
#print axioms OnBytes.Road.Rows.walks_forIn
#print axioms OnBytes.Road.Rows.hideRun_keeps
