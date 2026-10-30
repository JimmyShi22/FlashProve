-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Carry.lean: the closing of a segment (K10): general laws on outcomes of type
Except String. They carry an equation of the form "f at the changed argument is f at the argument, mapped by v" through
a bind, an if-then-else and a test that throws. They do the like for two outcomes that are alike (AlikeE v,
Wipe/Alike.lean: both refuse with the same word, or both return values that are equal under v). And they turn such a law
on one argument into like outcomes at two arguments that are equal once changed. No kind of member and no state is
named. Theorems alone.

  bindE            through a bind whose head is mapped by u and whose tail is mapped by v
  headE, headEqE   through a bind, where both sides have the same head, or equal heads
  sameE, sameEqE   two binds are equal: the same or equal heads, and equal tails
  iteE, iteA       through an if-then-else, arm by arm: as an equation, and for like outcomes
  unlessE          through "unless c do throw e" in front of a tail, in the form that Lean's do-notation gives it
  relE, relA       from a law on one argument to two arguments a, a' with u a = u a'
  optA             two Options with o.map u = o'.map u: both are none, or both hold values that are equal under u
  pairE, pairParts   pairs under Prod.map id g: how an equation between two is made, and what it gives

By what. Cases on the outcome, the condition or the Option.

Limits. Nothing says what the functions are. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
namespace Carry

variable {α α' β β' γ : Type}

/-- If the head x' is x mapped by u, and the tail f' at u a is f a mapped by v, then x' >>= f' is x >>= f mapped by v.
-/
theorem bindE (u : α → α') (v : β → β') {x : Except String α} {x' : Except String α'}
    {f : α → Except String β} {f' : α' → Except String β'} (hx : x' = x.map u)
    (hf : ∀ a, f' (u a) = (f a).map v) : (x' >>= f') = (x >>= f).map v := by
  subst hx
  cases x with
  | error e => rfl
  | ok a => exact hf a

/-- Two binds with the same head: if each f' a is f a mapped by v, the one bind is the other mapped by v. -/
theorem headE (v : β → β') {x : Except String α} {f : α → Except String β} {f' : α → Except String β'}
    (hf : ∀ a, f' a = (f a).map v) : (x >>= f') = (x >>= f).map v := by
  cases x with
  | error e => rfl
  | ok a => exact hf a

/-- The same for two heads that are equal. -/
theorem headEqE (v : β → β') {x x' : Except String α} {f : α → Except String β} {f' : α → Except String β'}
    (hx : x' = x) (hf : ∀ a, f' a = (f a).map v) : (x' >>= f') = (x >>= f).map v := by
  subst hx
  exact headE v hf

/-- Two binds with the same head and equal tails are equal. -/
theorem sameE {x : Except String α} {f f' : α → Except String β} (hf : ∀ a, f' a = f a) :
    (x >>= f') = (x >>= f) := by
  cases x with
  | error e => rfl
  | ok a => exact hf a

/-- Two binds with equal heads and equal tails are equal. -/
theorem sameEqE {x x' : Except String α} {f f' : α → Except String β} (hx : x' = x) (hf : ∀ a, f' a = f a) :
    (x' >>= f') = (x >>= f) := by
  subst hx
  exact sameE hf

/-- An if-then-else whose arms are another's arms mapped by v is that other one mapped by v. -/
theorem iteE (v : β → β') {c : Prop} [Decidable c] {p q : Except String β} {p' q' : Except String β'}
    (hp : p' = p.map v) (hq : q' = q.map v) : (if c then p' else q') = (if c then p else q).map v := by
  subst hp hq
  exact (apply_ite (Except.map v) c p q).symm

/-- Two if-then-elses on one condition are alike if their arms are. -/
theorem iteA {v : β → β'} {c : Prop} [Decidable c] {p q p' q' : Except String β} (hp : AlikeE v p' p)
    (hq : AlikeE v q' q) : AlikeE v (if c then p' else q') (if c then p else q) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact hp
  · rw [if_neg h, if_neg h]
    exact hq

/-- A test that throws, in front of a tail: if the one tail is the other mapped by v, so is the whole. -/
theorem unlessE (v : β → β') {c : Prop} [Decidable c] {e : String} {f : PUnit → Except String β}
    {f' : PUnit → Except String β'} (h : f' PUnit.unit = (f PUnit.unit).map v) :
    (if c then (pure PUnit.unit >>= f') else ((throw e : Except String PUnit) >>= f')) =
      (if c then (pure PUnit.unit >>= f) else ((throw e : Except String PUnit) >>= f)).map v := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact h
  · rw [if_neg hc, if_neg hc]
    rfl

/-- If f (u a) = (f a).map v for every a, then f has like outcomes at a and a' whenever u a = u a'. -/
theorem relE {u : γ → γ} {v : β → β} {f : γ → Except String β} (h : ∀ a, f (u a) = (f a).map v) {a a' : γ}
    (e : u a = u a') : AlikeE v (f a) (f a') := by
  have k : (f a).map v = (f a').map v := by rw [← h a, ← h a', e]
  exact AlikeE.of_eq k

/-- If f (u a) is like f a for every a, then f has like outcomes at a and a' whenever u a = u a'. -/
theorem relA {u : γ → γ} {v : β → β'} {f : γ → Except String β} (h : ∀ a, AlikeE v (f (u a)) (f a)) {a a' : γ}
    (e : u a = u a') : AlikeE v (f a) (f a') := by
  have h2 : AlikeE v (f (u a)) (f a') := by
    rw [e]
    exact h a'
  exact (h a).symm.trans h2

/-- Two Options with equal images under u: both are none, or both hold values that are equal under u. -/
theorem optA {u : α → α'} {o o' : Option α} (ho : o.map u = o'.map u) :
    (o = none ∧ o' = none) ∨ ∃ a a', o = some a ∧ o' = some a' ∧ u a = u a' := by
  cases o with
  | none =>
    cases o' with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some a' => cases ho
  | some a =>
    cases o' with
    | none => cases ho
    | some a' => exact Or.inr ⟨a, a', rfl, rfl, Option.some.inj ho⟩

/-- Two pairs with the same first part, and second parts equal under g, are equal under Prod.map id g. -/
theorem pairE (g : β → β') (a : α) {b b' : β} (h : g b = g b') : Prod.map id g (a, b) = Prod.map id g (a, b') :=
  congrArg (fun z => (a, z)) h

/-- Two pairs that are equal under Prod.map id g have equal first parts, and second parts equal under g. -/
theorem pairParts {g : β → β'} {x x' : α × β} (h : Prod.map id g x = Prod.map id g x') :
    x.1 = x'.1 ∧ g x.2 = g x'.2 :=
  ⟨(congrArg Prod.fst h :), (congrArg Prod.snd h :)⟩

end Carry
end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.Carry.bindE
#print axioms ProofFile.Honest.K10.Carry.headE
#print axioms ProofFile.Honest.K10.Carry.headEqE
#print axioms ProofFile.Honest.K10.Carry.sameE
#print axioms ProofFile.Honest.K10.Carry.sameEqE
#print axioms ProofFile.Honest.K10.Carry.iteE
#print axioms ProofFile.Honest.K10.Carry.iteA
#print axioms ProofFile.Honest.K10.Carry.unlessE
#print axioms ProofFile.Honest.K10.Carry.relE
#print axioms ProofFile.Honest.K10.Carry.relA
#print axioms ProofFile.Honest.K10.Carry.optA
#print axioms ProofFile.Honest.K10.Carry.pairE
#print axioms ProofFile.Honest.K10.Carry.pairParts
