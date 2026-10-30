-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/RetRules.lean: how "it returns" composes on the monad in which the
smallness test's run of equations is written (EqM, Johnson/Desc/First/TailClaims/Equations.lean).
One definition and general rules; nothing of the protocol is named.

  Ret x front s Q      the routine x, handed the number front, returns from the state s, and its
                       value and the state behind have the property Q.
  Ret.pure | bind | mustAs | testAs | get | ask | claims | emit | paid | change | ite
                       one rule for each way in which a routine is made.
  Ret.forInList | forInArray   a loop, with an invariant on what is left of the list, the loop's own
                       variables and the state.
  Ret.mono             a weaker property.
  Ret.intro            from an equation.
  Ret.also             brings in a law that speaks from a return: what such a law says of every
                       return holds of this one.
  Ret.liftF            a routine on the ledger alone.
The library's own laws on this monad speak from a return (EquationsRuns.lean and the files over it);
these rules go the other way.

Limits. General rules: they show of no routine that it returns. Nothing on soundness, completeness
or hiding.

-/
import Johnson.Desc.First.TailClaims.EquationsRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc

/-- The routine returns from s, and its value and the state behind have the property Q. -/
def Ret {α : Type} (x : EqM α) (front : Nat) (s : St) (Q : α → St → Prop) : Prop :=
  ∃ a s', x front s = .ok (a, s') ∧ Q a s'

variable {α β : Type} {front : Nat} {s : St}

theorem Ret.mono {x : EqM α} {P Q : α → St → Prop} (h : Ret x front s P)
    (hq : ∀ a s', P a s' → Q a s') : Ret x front s Q := by
  obtain ⟨a, s', e, p⟩ := h
  exact ⟨a, s', e, hq a s' p⟩

theorem Ret.pure {Q : α → St → Prop} (a : α) (h : Q a s) : Ret (Pure.pure a : EqM α) front s Q :=
  ⟨a, s, rfl, h⟩

theorem Ret.bind {x : EqM α} {f : α → EqM β} {P : α → St → Prop} {Q : β → St → Prop}
    (hx : Ret x front s P) (hf : ∀ a s₁, P a s₁ → Ret (f a) front s₁ Q) :
    Ret (x >>= f) front s Q := by
  obtain ⟨a, s₁, e, p⟩ := hx
  obtain ⟨b, s₂, e', q⟩ := hf a s₁ p
  exact ⟨b, s₂, (eq_bind_ok _ _ _ _ _).2 ⟨a, s₁, e, e'⟩, q⟩

theorem Ret.mustAs {Q : Unit → St → Prop} (n : String) {b : Bool} (hb : b = true) (h : Q () s) :
    Ret (EqM.mustAs n b) front s Q := by
  subst hb
  exact ⟨(), s, rfl, h⟩

theorem Ret.testAs {Q : Unit → St → Prop} (n : String) {b : Bool} (hb : b = true) (h : Q () s) :
    Ret (EqM.testAs n b) front s Q := Ret.mustAs n hb h

theorem Ret.get {Q : α → St → Prop} (n : String) {o : Option α} {a : α} (ho : o = some a)
    (h : Q a s) : Ret (EqM.get n o) front s Q := by
  subst ho
  exact ⟨a, s, rfl, h⟩

theorem Ret.ask {Q : α → St → Prop} (n : String) {f : Fork → Option α} {a : α}
    (ho : f s.1 = some a) (h : Q a s) : Ret (EqM.ask n f) front s Q := by
  refine ⟨a, s, ?_, h⟩
  unfold EqM.ask EqM.liftF ForkM.ask
  rw [ho]

theorem Ret.claims {Q : Nat → St → Prop} (h : Q (front + s.2.size) s) :
    Ret EqM.claims front s Q := ⟨_, s, rfl, h⟩

theorem Ret.emit {Q : Unit → St → Prop} (c : Claim) (h : Q () (s.1, s.2.push c)) :
    Ret (EqM.emit c) front s Q := ⟨(), _, rfl, h⟩

theorem Ret.paid {Q : Unit → St → Prop} (i : Nat) (h : Q () (s.1.paid i, s.2)) :
    Ret (EqM.paid i) front s Q := ⟨(), _, rfl, h⟩

theorem Ret.change {Q : Unit → St → Prop} (n : String) {f : Fork → Option Fork} {G : Fork}
    (ho : f s.1 = some G) (h : Q () (G, s.2)) : Ret (EqM.change n f) front s Q := by
  refine ⟨(), (G, s.2), ?_, h⟩
  unfold EqM.change EqM.liftF ForkM.change
  rw [ho]

theorem Ret.ite {Q : α → St → Prop} (c : Prop) [Decidable c] {x y : EqM α}
    (hx : c → Ret x front s Q) (hy : ¬ c → Ret y front s Q) :
    Ret (if c then x else y) front s Q := by
  by_cases q : c
  · rw [if_pos q]
    exact hx q
  · rw [if_neg q]
    exact hy q

/-- A loop. I: an invariant on what is left of the list, the loop's own variables and the state. -/
theorem Ret.forInList {f : α → β → EqM (ForInStep β)} (I : List α → β → St → Prop)
    (h : ∀ a rest b s, I (a :: rest) b s →
      Ret (f a b) front s fun r s' => ∃ b', r = .yield b' ∧ I rest b' s') :
    ∀ (l : List α) (b : β) (s : St), I l b s → Ret (forIn l b f) front s (I [])
  | [], b, s, hb => by
    rw [List.forIn_nil]
    exact Ret.pure b hb
  | a :: l, b, s, hb => by
    rw [List.forIn_cons]
    refine Ret.bind (h a l b s hb) ?_
    rintro r s' ⟨b', rfl, hb'⟩
    exact Ret.forInList I h l b' s' hb'

theorem Ret.forInArray {f : α → β → EqM (ForInStep β)} (I : List α → β → St → Prop)
    (h : ∀ a rest b s, I (a :: rest) b s →
      Ret (f a b) front s fun r s' => ∃ b', r = .yield b' ∧ I rest b' s')
    (as : Array α) (b : β) (s : St) (hb : I as.toList b s) : Ret (forIn as b f) front s (I []) := by
  rw [← Array.forIn_toList]
  exact Ret.forInList I h _ b s hb

theorem Ret.intro {x : EqM α} {Q : α → St → Prop} {a : α} {s' : St}
    (e : x front s = .ok (a, s')) (h : Q a s') : Ret x front s Q := ⟨a, s', e, h⟩

/-- What a law says of every return holds of this one. -/
theorem Ret.also {x : EqM α} {P Q : α → St → Prop} (h : Ret x front s Q)
    (hp : ∀ a s', x front s = .ok (a, s') → P a s') :
    Ret x front s fun a s' => Q a s' ∧ P a s' := by
  obtain ⟨a, s', e, q⟩ := h
  exact ⟨a, s', e, q, hp a s' e⟩

theorem Ret.liftF {Q : α → St → Prop} {x : ForkM α} {a : α} {G : Fork}
    (hx : x s.1 = .ok (a, G)) (h : Q a (G, s.2)) : Ret (EqM.liftF x) front s Q := by
  refine ⟨a, (G, s.2), ?_, h⟩
  unfold EqM.liftF
  rw [hx]

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.mono
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.pure
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.bind
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.mustAs
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.testAs
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.get
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.ask
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.claims
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.emit
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.paid
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.change
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.ite
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.forInList
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.forInArray
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.intro
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.also
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Ret.liftF
