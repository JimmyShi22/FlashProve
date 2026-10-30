-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRel.lean: A FRAME FOR TWO RUNS OF ONE TEXT, over the functions on a
ledger and a tape (Fl, OnBytes/K/Kc/Flat.lean). General laws: nothing is evaluated.

Why. To say that the SHAPE of what a long hearing leaves hangs on the shapes in front alone, one can
write the hearing a second time on shapes and keep the two texts in step; or compare two runs of the
one text. This file is the frame for the second way.

  roundSh, TapeAlike   a round without its elements; two tapes of one shape.
  **FlRel R x x'**     at ledgers of one shape (ledSh, Johnson/Desc/First/Shape/Parts.lean) and
                  tapes of one shape: WHERE BOTH RETURN, their values are in R, and the ledgers and
                  the tapes behind have one shape again.
  FlRel.pure, fl_bind, **FlRel.bind**, FlRel.mono, FlRel.ite   the frame is closed under the text's
                  own joints.
  FlRel.must, need, ask, onTape, change, takeSlots   Fl's six base steps.

Limits. THE WEAK FORM: every law stands where BOTH runs return: that one run returns where the other
does is not said. Nothing on what a value is worth. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FormsShape
import OnBytes.K.Kc.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc Tsc Level)
open VerifiableInference.Desc.First.Shape

/-! ## Two tapes of one shape -/

/-- A round without its elements: the three words of its entry; how many elements are still to be
taken; how many are drawn. -/
def roundSh (r : FlatRound) : Option String × Nat × Nat × Nat × Nat :=
  (r.name, r.nz, r.rows, r.sent.length, r.drawn.length)

/-- Two tapes of one shape. -/
def TapeAlike (t t' : Tape) : Prop := t.map roundSh = t'.map roundSh

theorem TapeAlike.refl (t : Tape) : TapeAlike t t := rfl

/-! ## The frame: two runs of one text -/

/-- **Two functions on a ledger and a tape, at ledgers of one shape and tapes of one shape**: where
both return, their values are in R, and the ledgers and the tapes behind have one shape again. -/
def FlRel {α β : Type} (R : α → β → Prop) (x : Fl α) (x' : Fl β) : Prop :=
  ∀ F F' t t' a G u a' G' u', ledSh F = ledSh F' → TapeAlike t t' →
    x F t = some (a, G, u) → x' F' t' = some (a', G', u') →
    R a a' ∧ ledSh G = ledSh G' ∧ TapeAlike u u'

theorem FlRel.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    FlRel R (Pure.pure a : Fl α) (Pure.pure b : Fl β) := by
  intro F F' t t' a₁ G u a₂ G' u' hF ht h1 h2
  have e1 : (a, F, t) = (a₁, G, u) := Option.some.inj h1
  have e2 : (b, F', t') = (a₂, G', u') := Option.some.inj h2
  obtain ⟨rfl, rfl, rfl⟩ : a = a₁ ∧ F = G ∧ t = u :=
    ⟨congrArg (·.1) e1, congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
  obtain ⟨rfl, rfl, rfl⟩ : b = a₂ ∧ F' = G' ∧ t' = u' :=
    ⟨congrArg (·.1) e2, congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  exact ⟨h, hF, ht⟩

/-- What a bind's return is made of. -/
theorem fl_bind {α β : Type} {x : Fl α} {k : α → Fl β} {F : Fork} {t : Tape}
    {r : β × Fork × Tape} (h : (x >>= k) F t = some r) :
    ∃ a G u, x F t = some (a, G, u) ∧ k a G u = some r := by
  have h' : (match x F t with
    | some (a, G, u) => k a G u
    | none => none) = some r := h
  cases hx : x F t with
  | none =>
    rw [hx] at h'
    cases h'
  | some q =>
    obtain ⟨a, G, u⟩ := q
    rw [hx] at h'
    exact ⟨a, G, u, rfl, h'⟩

/-- **The frame is closed under bind.** -/
theorem FlRel.bind {α β γ δ : Type} {S : α → β → Prop} {R : γ → δ → Prop} {x : Fl α} {x' : Fl β}
    {k : α → Fl γ} {k' : β → Fl δ} (hx : FlRel S x x')
    (hk : ∀ a b, S a b → FlRel R (k a) (k' b)) : FlRel R (x >>= k) (x' >>= k') := by
  intro F F' t t' c H w c' H' w' hF ht h1 h2
  obtain ⟨a, G, u, e1, k1⟩ := fl_bind h1
  obtain ⟨b, G', u', e2, k2⟩ := fl_bind h2
  obtain ⟨r1, r2, r3⟩ := hx F F' t t' a G u b G' u' hF ht e1 e2
  exact hk a b r1 G G' u u' c H w c' H' w' r2 r3 k1 k2

theorem FlRel.mono {α β : Type} {R S : α → β → Prop} {x : Fl α} {x' : Fl β} (h : FlRel R x x')
    (hs : ∀ a b, R a b → S a b) : FlRel S x x' := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  obtain ⟨r1, r2, r3⟩ := h F F' t t' a G u a' G' u' hF ht h1 h2
  exact ⟨hs _ _ r1, r2, r3⟩

/-- One test at both sides. -/
theorem FlRel.ite {α β : Type} {R : α → β → Prop} {c : Prop} [Decidable c] {x y : Fl α}
    {x' y' : Fl β} (h1 : FlRel R x x') (h2 : FlRel R y y') :
    FlRel R (if c then x else y) (if c then x' else y') := by
  by_cases h : c
  · simpa only [if_pos h] using h1
  · simpa only [if_neg h] using h2

/-! ## The six base steps -/

theorem FlRel.must (b b' : Bool) : FlRel (fun _ _ => True) (Fl.must b) (Fl.must b') := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  unfold Fl.must at h1 h2
  split at h1
  · split at h2
    · have e1 : ((), F, t) = (a, G, u) := Option.some.inj h1
      have e2 : ((), F', t') = (a', G', u') := Option.some.inj h2
      obtain ⟨rfl, rfl⟩ : F = G ∧ t = u := ⟨congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
      obtain ⟨rfl, rfl⟩ : F' = G' ∧ t' = u' := ⟨congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
      exact ⟨trivial, hF, ht⟩
    · cases h2
  · cases h1

theorem FlRel.need {α β : Type} {R : α → β → Prop} {x : Option α} {x' : Option β}
    (h : ∀ a b, x = some a → x' = some b → R a b) : FlRel R (Fl.need x) (Fl.need x') := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  obtain ⟨a₀, ha, e1⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨b₀, hb, e2⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨rfl, rfl, rfl⟩ : a₀ = a ∧ F = G ∧ t = u :=
    ⟨congrArg (·.1) e1, congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
  obtain ⟨rfl, rfl, rfl⟩ : b₀ = a' ∧ F' = G' ∧ t' = u' :=
    ⟨congrArg (·.1) e2, congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  exact ⟨h _ _ ha hb, hF, ht⟩

/-- A value read off the ledger: nothing is said of it. -/
theorem FlRel.ask {α β : Type} (f : Fork → Option α) (f' : Fork → Option β) :
    FlRel (fun _ _ => True) (Fl.ask f) (Fl.ask f') := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  obtain ⟨a₀, -, e1⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨b₀, -, e2⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨rfl, rfl⟩ : F = G ∧ t = u := ⟨congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
  obtain ⟨rfl, rfl⟩ : F' = G' ∧ t' = u' := ⟨congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  exact ⟨trivial, hF, ht⟩

/-- A step on the tape alone. -/
theorem FlRel.onTape {α β : Type} {R : α → β → Prop} {g : Tape → Option (α × Tape)}
    {g' : Tape → Option (β × Tape)}
    (h : ∀ t t' a u b u', TapeAlike t t' → g t = some (a, u) → g' t' = some (b, u') →
      R a b ∧ TapeAlike u u') : FlRel R (Fl.onTape g) (Fl.onTape g') := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  obtain ⟨x, hx, e1⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨y, hy, e2⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨rfl, rfl, rfl⟩ : x.1 = a ∧ F = G ∧ x.2 = u :=
    ⟨congrArg (·.1) e1, congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
  obtain ⟨rfl, rfl, rfl⟩ : y.1 = a' ∧ F' = G' ∧ y.2 = u' :=
    ⟨congrArg (·.1) e2, congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  obtain ⟨r1, r2⟩ := h t t' x.1 x.2 y.1 y.2 ht hx hy
  exact ⟨r1, hF, r2⟩

/-- A step on the ledger. -/
theorem FlRel.change {f f' : Fork → Option Fork}
    (h : ∀ F F' G G', ledSh F = ledSh F' → f F = some G → f' F' = some G' → ledSh G = ledSh G') :
    FlRel (fun _ _ => True) (Fl.change f) (Fl.change f') := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  obtain ⟨x, hx, e1⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨y, hy, e2⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨rfl, rfl⟩ : x = G ∧ t = u := ⟨congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
  obtain ⟨rfl, rfl⟩ : y = G' ∧ t' = u' := ⟨congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  exact ⟨trivial, h F F' x y hF hx hy, ht⟩

/-- The next n slots are taken: the same first slot. -/
theorem FlRel.takeSlots (n : Nat) : FlRel Eq (Fl.takeSlots n) (Fl.takeSlots n) := by
  intro F F' t t' a G u a' G' u' hF ht h1 h2
  have e1 : (F.next, ({ F with next := F.next + n } : Fork), t) = (a, G, u) := Option.some.inj h1
  have e2 : (F'.next, ({ F' with next := F'.next + n } : Fork), t') = (a', G', u') :=
    Option.some.inj h2
  obtain ⟨rfl, rfl, rfl⟩ : F.next = a ∧ ({ F with next := F.next + n } : Fork) = G ∧ t = u :=
    ⟨congrArg (·.1) e1, congrArg (·.2.1) e1, congrArg (·.2.2) e1⟩
  obtain ⟨rfl, rfl, rfl⟩ :
      F'.next = a' ∧ ({ F' with next := F'.next + n } : Fork) = G' ∧ t' = u' :=
    ⟨congrArg (·.1) e2, congrArg (·.2.1) e2, congrArg (·.2.2) e2⟩
  have hn : F.next = F'.next := congrArg LedSh.next hF
  refine ⟨hn, ?_, ht⟩
  have m : ∀ X : Fork, ledSh { X with next := X.next + n } =
      LedSh.mk (ledSh X).ns (ledSh X).shown (ledSh X).factors (ledSh X).got (ledSh X).owed
        (ledSh X).planClaims (ledSh X).trees ((ledSh X).next + n) (ledSh X).coefs (ledSh X).claims
        (ledSh X).drawn (ledSh X).handed (ledSh X).shut := fun _ => rfl
  rw [m, m, hF]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.TapeAlike.refl
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.pure
#print axioms OnBytes.Desc.First.K4.Rt.fl_bind
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.bind
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.mono
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.ite
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.must
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.need
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.ask
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.onTape
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.change
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.takeSlots
#print axioms OnBytes.Desc.First.K4.Rt.roundSh
#print axioms OnBytes.Desc.First.K4.Rt.TapeAlike
#print axioms OnBytes.Desc.First.K4.Rt.FlRel
