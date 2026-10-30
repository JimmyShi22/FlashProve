-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/EqPort/EqKit.lean: the ground under the carried files of this folder: what it means
that a routine of the smallness test's run of claims (`EqM`,
Johnson/Desc/First/TailClaims/Equations.lean: from the count of claims in front, a sub-proof's
ledger and the list of claims so far to a refusal by name, or to a value, the ledger and the list
behind) returns, in the same words and shapes in which the library says it of the verifier program's
routines in a context (OnBytes/Tie/Pv/Psc/PscRun.lean). Typed by hand. Definitions, and theorems
with their proofs.

Main names:
  `EqM.at x front F c`: x's outcome from the ledger F and the list c, written as the library writes
    a routine's: value and ledger as a pair, then the list. In the files of this folder `x ⟫ F c`.
  `bind_ok`, `pure_ok`, `mustAs_ok`, `get_ok`, `change_ok`, `paid_ok`, `emit_ok`, `claims_ok`: when
    a routine of each make returns, and what.

Limits. Nothing is said where a routine refuses, nor under which name. EqM is a plain state monad on
a ledger and a list: no context of the verifier program's channel stands in it.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.TailClaims.Equations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Eq
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First.TailClaims

/-- A routine's outcome, written as the library writes one: value and ledger as a pair, then the
list of claims. -/
def _root_.VerifiableInference.Desc.First.TailClaims.EqM.at {α : Type} (x : EqM α) (front : Nat)
    (F : Fork) (c : Array Claim) : Except String ((α × Fork) × Array Claim) :=
  match x front (F, c) with
  | .ok r => .ok ((r.1, r.2.1), r.2.2)
  | .error e => .error e

variable {front : Nat} {α β : Type}

local notation:65 x:66 " ⟫ " F:max c:max => EqM.at x front F c

theorem at_ok (x : EqM α) (F : Fork) (c : Array Claim) (r : (α × Fork) × Array Claim) :
    x ⟫ F c = .ok r ↔ x front (F, c) = .ok (r.1.1, (r.1.2, r.2)) := by
  unfold EqM.at
  cases h : x front (F, c) with
  | error e =>
    constructor
    · intro h'
      cases h'
    · intro h'
      cases h'
  | ok y =>
    obtain ⟨a, G, d⟩ := y
    obtain ⟨⟨a', G'⟩, d'⟩ := r
    constructor
    · intro h'
      have e : ((a, G), d) = ((a', G'), d') := Except.ok.inj h'
      cases e
      rfl
    · intro h'
      have e : (a, (G, d)) = (a', (G', d')) := Except.ok.inj h'
      cases e
      rfl

/-- «x, then f» returns exactly if x returns and f does from there. -/
theorem bind_ok (x : EqM α) (f : α → EqM β) (F : Fork) (c : Array Claim)
    (r : (β × Fork) × Array Claim) :
    (x >>= f) ⟫ F c = .ok r ↔ ∃ a G c1, x ⟫ F c = .ok ((a, G), c1) ∧ f a ⟫ G c1 = .ok r := by
  simp only [at_ok]
  show (x front (F, c) >>= fun y => f y.1 front y.2) = _ ↔ _
  cases h : x front (F, c) with
  | error e =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, _, _, e', _⟩
      cases e'
  | ok y =>
    obtain ⟨a, G, d⟩ := y
    constructor
    · intro h'
      exact ⟨a, G, d, rfl, h'⟩
    · rintro ⟨a', G', d', e', h'⟩
      have e : (a, (G, d)) = (a', (G', d')) := Except.ok.inj e'
      cases e
      exact h'

theorem pure_ok (a : α) (F : Fork) (c : Array Claim) (r : (α × Fork) × Array Claim) :
    (pure a : EqM α) ⟫ F c = .ok r ↔ r = ((a, F), c) := by
  rw [at_ok]
  obtain ⟨⟨a', G'⟩, d'⟩ := r
  constructor
  · intro h
    have e : (a, (F, c)) = (a', (G', d')) := Except.ok.inj h
    cases e
    rfl
  · intro h
    cases h
    rfl

theorem mustAs_ok (name : String) (b : Bool) (F : Fork) (c : Array Claim)
    (r : (Unit × Fork) × Array Claim) :
    EqM.mustAs name b ⟫ F c = .ok r ↔ b = true ∧ r = (((), F), c) := by
  rw [at_ok]
  obtain ⟨⟨u, G'⟩, d'⟩ := r
  cases b with
  | false =>
    constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      cases h
  | true =>
    constructor
    · intro h
      have e : ((), (F, c)) = (u, (G', d')) := Except.ok.inj h
      cases e
      exact ⟨rfl, rfl⟩
    · rintro ⟨_, h⟩
      cases h
      rfl

theorem get_ok {name : String} (x : Option α) (F : Fork) (c : Array Claim)
    (r : (α × Fork) × Array Claim) :
    EqM.get name x ⟫ F c = .ok r ↔ ∃ a, x = some a ∧ r = ((a, F), c) := by
  rw [at_ok]
  obtain ⟨⟨a', G'⟩, d'⟩ := r
  cases x with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, h, _⟩
      cases h
  | some a =>
    constructor
    · intro h
      have e : (a, (F, c)) = (a', (G', d')) := Except.ok.inj h
      cases e
      exact ⟨_, rfl, rfl⟩
    · rintro ⟨a'', h, h2⟩
      cases h
      cases h2
      rfl

theorem change_ok {name : String} (f : Fork → Option Fork) (F : Fork) (c : Array Claim)
    (r : (Unit × Fork) × Array Claim) :
    EqM.change name f ⟫ F c = .ok r ↔ ∃ G, f F = some G ∧ r = (((), G), c) := by
  rw [at_ok]
  obtain ⟨⟨u, G'⟩, d'⟩ := r
  unfold EqM.change EqM.liftF ForkM.change
  dsimp only
  cases h : f F with
  | none =>
    constructor
    · intro h'
      cases h'
    · rintro ⟨_, h', _⟩
      cases h'
  | some G =>
    constructor
    · intro h'
      have e : ((), (G, c)) = (u, (G', d')) := Except.ok.inj h'
      cases e
      exact ⟨_, rfl, rfl⟩
    · rintro ⟨G'', h', h2⟩
      cases h'
      cases h2
      rfl

theorem paid_ok (i : Nat) (F : Fork) (c : Array Claim) (r : (Unit × Fork) × Array Claim) :
    EqM.paid i ⟫ F c = .ok r ↔ r = (((), F.paid i), c) := by
  rw [at_ok]
  obtain ⟨⟨u, G'⟩, d'⟩ := r
  constructor
  · intro h
    have e : ((), (F.paid i, c)) = (u, (G', d')) := Except.ok.inj h
    cases e
    rfl
  · intro h
    cases h
    rfl

theorem emit_ok (k : Claim) (F : Fork) (c : Array Claim) (r : (Unit × Fork) × Array Claim) :
    EqM.emit k ⟫ F c = .ok r ↔ r = (((), F), c.push k) := by
  rw [at_ok]
  obtain ⟨⟨u, G'⟩, d'⟩ := r
  constructor
  · intro h
    have e : ((), (F, c.push k)) = (u, (G', d')) := Except.ok.inj h
    cases e
    rfl
  · intro h
    cases h
    rfl

theorem claims_ok (F : Fork) (c : Array Claim) (r : (Nat × Fork) × Array Claim) :
    EqM.claims ⟫ F c = .ok r ↔ r = ((front + c.size, F), c) := by
  rw [at_ok]
  obtain ⟨⟨n, G'⟩, d'⟩ := r
  constructor
  · intro h
    have e : (front + c.size, (F, c)) = (n, (G', d')) := Except.ok.inj h
    cases e
    rfl
  · intro h
    cases h
    rfl

end Fo.Eq
