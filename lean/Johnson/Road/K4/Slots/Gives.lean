-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/Gives.lean: "WHEREVER THE OPTIONAL VALUE IS THERE, IT HAS Φ", with its rules;
and the readers of the tables in that form. A definition, statements and proofs. A tool for walking
texts that are written with `do` over `Option`.

  `Gives x Φ`: wherever x is there, it has Φ. Rules: `Gives.pure`, `Gives.some`, `Gives.none`,
    `Gives.bind`, `Gives.skip`, `Gives.map`, `Gives.ite`; at forms: `Gives.bindA`, `Gives.bindP`,
    `Gives.mapP`.
  `gives_U3at`, `gives_sumForms`, `gives_longA`, `gives_xbA`, `gives_shA`, `gives_shIn`, `gives_SA`,
    `gives_SxsA`, `gives_SBA`, `gives_shSum`: what a reader returns names no slot (Readers.lean).

Limits. Nothing on which entries are named. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.Readers

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- Wherever the optional value is there, it has Φ. -/
def Gives {α : Type} (x : Option α) (Φ : α → Prop) : Prop := ∀ a, x = some a → Φ a

section Rules
variable {α β : Type} {Φ : α → Prop} {Ψ : β → Prop}

theorem Gives.pure {a : α} (h : Φ a) : Gives (Pure.pure a : Option α) Φ :=
  fun _ e => Option.some.inj e ▸ h

theorem Gives.some {a : α} (h : Φ a) : Gives (Option.some a) Φ :=
  fun _ e => Option.some.inj e ▸ h

theorem Gives.none : Gives (Option.none : Option α) Φ := fun _ e => by cases e

theorem Gives.bind {x : Option α} {f : α → Option β} (hx : Gives x Φ)
    (hf : ∀ a, Φ a → Gives (f a) Ψ) : Gives (x >>= f) Ψ := fun b e => by
  obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp e
  exact hf a (hx a ha) b hb

theorem Gives.skip {x : Option α} {f : α → Option β} (hf : ∀ a, Gives (f a) Ψ) :
    Gives (x >>= f) Ψ := Gives.bind (Φ := fun _ => True) (fun _ _ => trivial) fun a _ => hf a

theorem Gives.map {x : Option α} {f : α → β} (hx : Gives x Φ) (hf : ∀ a, Φ a → Ψ (f a)) :
    Gives (x.map f) Ψ := fun b e => by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp e
  exact hf a (hx a ha)

theorem Gives.ite {c : Prop} [Decidable c] {x y : Option α} (hx : Gives x Φ) (hy : Gives y Φ) :
    Gives (if c then x else y) Φ := by
  split
  · exact hx
  · exact hy

end Rules

variable {v : Env} {S : ℕ → Prop}

/-- The first part of a pair (a form, its weight) names slots with S alone. -/
abbrev P1 (S : ℕ → Prop) : Aff × E → Prop := fun p => SlotsIn S p.1

theorem Gives.bindA {x : Option Aff} {f : Aff → Option Aff} (hx : Gives x (SlotsIn S))
    (hf : ∀ a, SlotsIn S a → Gives (f a) (SlotsIn S)) : Gives (x >>= f) (SlotsIn S) :=
  Gives.bind hx hf

theorem Gives.bindP {x : Option Aff} {f : Aff → Option (Aff × E)} (hx : Gives x (SlotsIn S))
    (hf : ∀ a, SlotsIn S a → Gives (f a) (P1 S)) : Gives (x >>= f) (P1 S) :=
  Gives.bind hx hf

theorem Gives.mapP {x : Option Aff} {f : Aff → Aff × E} (hx : Gives x (SlotsIn S))
    (hf : ∀ a, SlotsIn S a → SlotsIn S (f a).1) : Gives (x.map f) (P1 S) :=
  Gives.map hx hf

/-! ### The readers -/

theorem gives_U3at (t i : ℕ) : Gives (v.U3at t i) (SlotsIn S) := fun _ h => sl_U3at h

theorem gives_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)}
    (hg : ∀ x, Gives (g x) (P1 S)) : Gives (sumForms n g) (SlotsIn S) :=
  fun _ h => sl_sumForms (fun x p hp => hg x p hp) h

theorem gives_longA (t : ℕ) (X : Ten) (i jh : ℕ) : Gives (v.longA t X i jh) (SlotsIn S) :=
  fun _ h => sl_longA h

theorem gives_xbA (t kh : ℕ) : Gives (v.xbA t kh) (SlotsIn S) := fun _ h => sl_xbA h

theorem gives_shA (X P : String) (i j : ℕ) : Gives (v.shA X P i j) (SlotsIn S) :=
  fun _ h => sl_shA h

theorem gives_shIn (found : Option (Ten × ℕ)) (i j : ℕ) : Gives (v.shIn found i j) (SlotsIn S) := by
  unfold Env.shIn
  exact Gives.skip fun x _ h => sl_shortA h

theorem gives_SA (wh : Array E) (X : String) (i : ℕ) (Z : String) :
    Gives (v.SA wh X i Z) (SlotsIn S) := by
  unfold Env.SA
  refine Gives.skip fun x => ?_
  exact gives_sumForms fun xh => Gives.mapP (gives_longA _ _ _ _) fun _ h => h

theorem gives_SxsA (wh : Array E) (Z : String) (sg : ℕ) : Gives (v.SxsA wh Z sg) (SlotsIn S) := by
  unfold Env.SxsA
  refine Gives.skip fun tb => Gives.skip fun txs => ?_
  exact gives_sumForms fun xh =>
    Gives.mapP (Gives.ite (gives_xbA _ _) (gives_longA _ _ _ _)) fun _ h => h

theorem gives_SBA (wh : Array E) (a b : ℕ) (X : String) (i : ℕ) (Z : String) (x0 : ℕ) :
    Gives (v.SBA wh a b X i Z x0) (SlotsIn S) := by
  unfold Env.SBA
  refine Gives.skip fun x => ?_
  exact gives_sumForms fun k => Gives.mapP (gives_longA _ _ _ _) fun _ h => h

theorem gives_shSum (ew : Array E) (n : ℕ) (X P : String) (i : ℕ) :
    Gives (v.shSum ew n X P i) (SlotsIn S) := by
  unfold Env.shSum
  exact gives_sumForms fun x => Gives.mapP (gives_shIn _ _ _) fun _ h => h

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.gives_SxsA
#print axioms OnBytes.Desc.First.K4.Slots.gives_shSum
