-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Alike.lean: the kind "the code switch" (K2): TOOLS for a law on
refusals: when two runs of one text, at other values, return or refuse ALIKE. Definitions;
statements with their proofs. General: no text of the kind is named but its coins
(`Stretch`, Honest/K2/Part.lean).

  `Alike`           two results are alike under a relation R: both return, and R holds of what they
                    return; or both refuse, in the same words
  `Alike.ok`, `Alike.error`, `Alike.same`, `Alike.mono`   both return · both refuse · a result is
                    alike to itself under a relation that holds of each value and itself · a weaker
                    relation
  `Alike.bind`      THE STEP: alike results, and continuations that are alike at related values
  `Alike.map`       alike results under two functions
  `Alike.ite`       one condition on both sides: alike in each of its two cases
  `Alike.guard`     the like for a refusal under a condition with what follows it, in the form in
                    which Lean has such a line of a `do` block
  `Alike.mapM`, `Alike.mapM_same`   member by member, over two lists of related members; over one
                    list
  `Alike.isSome`    alike results return together
  `Any`             the relation that holds of all values: "return or refuse alike" and no more
  `fAt_alike`, `eAt_alike`   a coin by its number: whether it is there hangs on the count
  `fs_alike`, `es_alike`   so many coins from a number on, off two stretches of one count
  `carried_alike`   the stretch of a number, off two fillings of one list of named counts: alike,
                    and of one count where they return

NEAR, NOT CALLED: the library's `AlikeE`, with `AlikeE.bind` and `AlikeE.refl`
(Johnson/LPFGuard/Seat.lean): THE NEAREST OF KIN: where the two results have one type, `Alike` is
that relation, but for the sides of the equation between two refusals' words; `Alike` leaves the two
types free. `Alike.bind` and `Alike.same` are its two lemmas at that width.

Limits. Tools: nothing here speaks of a closing or a sending. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

variable {α β γ δ : Type}

/-- **Two results are alike.** -/
def Alike (R : α → β → Prop) : Except String α → Except String β → Prop
  | .ok a, .ok b => R a b
  | .error e, .error e' => e = e'
  | _, _ => False

/-- The relation that holds of all values. -/
def Any (_ : α) (_ : β) : Prop := True

theorem Alike.ok {R : α → β → Prop} {a : α} {b : β} (h : R a b) : Alike R (.ok a) (.ok b) := h

theorem Alike.error {R : α → β → Prop} (e : String) : Alike R (.error e) (.error e) := rfl

theorem Alike.same {R : α → α → Prop} (hR : ∀ a, R a a) (x : Except String α) : Alike R x x := by
  cases x with
  | error e => exact rfl
  | ok a => exact hR a

theorem Alike.mono {R Q : α → β → Prop} (hRQ : ∀ a b, R a b → Q a b) {x : Except String α}
    {y : Except String β} (h : Alike R x y) : Alike Q x y := by
  cases x with
  | error e =>
    cases y with
    | error e' => exact h
    | ok b => exact h
  | ok a =>
    cases y with
    | error e' => exact h
    | ok b => exact hRQ a b h

/-- **The step.** -/
theorem Alike.bind {R : α → β → Prop} {Q : γ → δ → Prop} {x : Except String α}
    {y : Except String β} {f : α → Except String γ} {g : β → Except String δ} (h : Alike R x y)
    (hf : ∀ a b, R a b → Alike Q (f a) (g b)) : Alike Q (x.bind f) (y.bind g) := by
  cases x with
  | error e =>
    cases y with
    | error e' => exact h
    | ok b => exact h.elim
  | ok a =>
    cases y with
    | error e' => exact h.elim
    | ok b => exact hf a b h

theorem Alike.map {R : α → β → Prop} {Q : γ → δ → Prop} {x : Except String α}
    {y : Except String β} {f : α → γ} {g : β → δ} (h : Alike R x y)
    (hf : ∀ a b, R a b → Q (f a) (g b)) : Alike Q (x.map f) (y.map g) := by
  cases x with
  | error e =>
    cases y with
    | error e' => exact h
    | ok b => exact h.elim
  | ok a =>
    cases y with
    | error e' => exact h.elim
    | ok b => exact hf a b h

/-- One condition on both sides. -/
theorem Alike.ite {R : α → β → Prop} {c : Prop} [Decidable c] {x₀ x : Except String α}
    {y₀ y : Except String β} (h₀ : Alike R x₀ y₀) (h : Alike R x y) :
    Alike R (if c then x₀ else x) (if c then y₀ else y) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact h₀
  · rw [if_neg hc, if_neg hc]
    exact h

/-- A refusal under one condition on both sides, with what follows. -/
theorem Alike.guard {R : α → β → Prop} {c : Prop} [Decidable c] {e : String}
    {f : PUnit → Except String α} {g : PUnit → Except String β}
    (h : Alike R (f PUnit.unit) (g PUnit.unit)) :
    Alike R (if c then (throw e : Except String PUnit) >>= f else pure PUnit.unit >>= f)
      (if c then (throw e : Except String PUnit) >>= g else pure PUnit.unit >>= g) :=
  Alike.ite (Alike.error e) h

/-- Member by member, over two lists. -/
theorem Alike.mapM {R : γ → δ → Prop} {f : α → Except String γ} {g : β → Except String δ}
    {l : List α} {l' : List β} (h : List.Forall₂ (fun a b => Alike R (f a) (g b)) l l') :
    Alike (List.Forall₂ R) (l.mapM f) (l'.mapM g) := by
  induction h with
  | nil =>
    rw [List.mapM_nil, List.mapM_nil]
    exact List.Forall₂.nil
  | cons h₁ _ ih =>
    rw [List.mapM_cons, List.mapM_cons]
    exact Alike.bind h₁ fun _ _ hab => Alike.bind ih fun _ _ hs => List.Forall₂.cons hab hs

/-- Over one list. -/
theorem Alike.mapM_same {R : γ → δ → Prop} {f : α → Except String γ} {g : α → Except String δ}
    (h : ∀ a, Alike R (f a) (g a)) (l : List α) :
    Alike (List.Forall₂ R) (l.mapM f) (l.mapM g) :=
  Alike.mapM (List.forall₂_same.2 fun a _ => h a)

/-- Alike results return together. -/
theorem Alike.isSome {R : α → β → Prop} {x : Except String α} {y : Except String β}
    (h : Alike R x y) : x.toOption.isSome = y.toOption.isSome := by
  cases x with
  | error e =>
    cases y with
    | error e' => rfl
    | ok b => exact h.elim
  | ok a =>
    cases y with
    | error e' => exact h.elim
    | ok b => rfl

/-! ## Coins -/

theorem fAt_alike {d : Due} (c c' : Cs d) (i : Nat) : Alike Any (c.fAt i) (c'.fAt i) := by
  unfold Cs.fAt
  split
  · exact trivial
  · exact rfl

theorem eAt_alike {d : Due} (c c' : Cs d) (i : Nat) : Alike Any (c.eAt i) (c'.eAt i) := by
  unfold Cs.eAt
  split
  · exact trivial
  · exact rfl

theorem fs_alike {s s' : Stretch} (h : s.due = s'.due) (a n : Nat) :
    Alike Any (s.fs a n) (s'.fs a n) := by
  obtain ⟨d, c⟩ := s
  obtain ⟨d', c'⟩ := s'
  obtain rfl : d = d' := h
  exact Alike.map (Alike.mapM_same (fun i => fAt_alike c c' (a + i)) _) fun _ _ _ => trivial

theorem es_alike {s s' : Stretch} (h : s.due = s'.due) (a n : Nat) :
    Alike Any (s.es a n) (s'.es a n) := by
  obtain ⟨d, c⟩ := s
  obtain ⟨d', c'⟩ := s'
  obtain rfl : d = d' := h
  exact Alike.map (Alike.mapM_same (fun i => eAt_alike c c' (a + i)) _) fun _ _ _ => trivial

/-- The stretch of a number, off two fillings of one list of named counts. -/
theorem carried_alike : ∀ (ds : List (String × Due)) (c c' : CsAll ds) (n : Nat),
    Alike (fun s s' : Stretch => s.due = s'.due) (Stretch.carried ds c n) (Stretch.carried ds c' n)
  | [], _, _, _ => rfl
  | _ :: _, _, _, 0 => rfl
  | _ :: ds, c, c', n + 1 => carried_alike ds c.2 c'.2 n

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.Alike.ok
#print axioms ProofFile.Honest.K2.Law.Alike.error
#print axioms ProofFile.Honest.K2.Law.Alike.same
#print axioms ProofFile.Honest.K2.Law.Alike.mono
#print axioms ProofFile.Honest.K2.Law.Alike.bind
#print axioms ProofFile.Honest.K2.Law.Alike.map
#print axioms ProofFile.Honest.K2.Law.Alike.ite
#print axioms ProofFile.Honest.K2.Law.Alike.guard
#print axioms ProofFile.Honest.K2.Law.Alike.mapM
#print axioms ProofFile.Honest.K2.Law.Alike.mapM_same
#print axioms ProofFile.Honest.K2.Law.Alike.isSome
#print axioms ProofFile.Honest.K2.Law.fAt_alike
#print axioms ProofFile.Honest.K2.Law.eAt_alike
#print axioms ProofFile.Honest.K2.Law.fs_alike
#print axioms ProofFile.Honest.K2.Law.es_alike
#print axioms ProofFile.Honest.K2.Law.carried_alike
#print axioms ProofFile.Honest.K2.Law.Alike
#print axioms ProofFile.Honest.K2.Law.Any
