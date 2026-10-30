-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Hotel.lean: an explicit bijection A ⊕ {0,1}* ≃ {0,1}* from an injective encoding of A as bit
strings with a parser (`StrCode`). The bijection and its inverse are explicit functions; no choice
is used to define them.

Use: the step from typed oracles (one oracle for each kind of query) to one hash function, by domain
separation, needs every bit string to be the encoding of exactly one point: an oracle, a query and
the index of a hash block of the answer (`OracleCoding.bij`, Rom/Family.lean). In
Compile/Batch/ImplOf.lean A holds the points of the scheme's typed oracles, and the summand {0,1}*
the queries to the auxiliary oracle `other` and, by a second use of `hotel`, the ghost points.

Construction (Schröder-Bernstein, computable here because the chains get shorter): write a string as
false^k ++ r with r = [] or r = true :: t. It is free if r = [] or t does not parse. Then `enc` (inl
a) = true :: put a, and `enc` (inr s) = s if s is free, false :: s if not.
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.List.Basic

namespace Rom

/-- an injective encoding as bit strings, with a parser -/
structure StrCode (A : Type) where
  put : A → List Bool
  parse : List Bool → Option A
  parse_put : ∀ a, parse (put a) = some a
  put_parse : ∀ s a, parse s = some a → put a = s

namespace StrCode
variable {A : Type} (c : StrCode A)

/-- the string is not of the form false^k ++ true :: put a -/
def free : List Bool → Bool
  | [] => true
  | true :: t => (c.parse t).isNone
  | false :: s => free s

def enc : A ⊕ List Bool → List Bool
  | .inl a => true :: c.put a
  | .inr s => if c.free s then s else false :: s

def dec : List Bool → A ⊕ List Bool
  | [] => .inr []
  | true :: t => match c.parse t with
      | some a => .inl a
      | none => .inr (true :: t)
  | false :: s => if c.free s then .inr (false :: s) else .inr s

theorem dec_enc : ∀ x, c.dec (c.enc x) = x
  | .inl a => by simp [enc, dec, c.parse_put]
  | .inr s => by
      by_cases h : c.free s = true
      · simp only [enc, h, if_true]
        cases s with
        | nil => rfl
        | cons b t =>
            cases b with
            | true =>
                have h' : (c.parse t).isNone = true := h
                cases hp : c.parse t with
                | none => simp [dec, hp]
                | some a => simp [hp] at h'
            | false =>
                have h' : c.free t = true := h
                simp [dec, h']
      · simp only [enc, h]
        simp [dec, h]

theorem enc_dec : ∀ s, c.enc (c.dec s) = s
  | [] => by simp [dec, enc, free]
  | true :: t => by
      cases hp : c.parse t with
      | some a => simp [dec, hp, enc, c.put_parse t a hp]
      | none => simp [dec, hp, enc, free]
  | false :: s => by
      by_cases h : c.free s = true
      · simp [dec, h, enc, free]
      · simp [dec, h, enc]

/-- the bijection A ⊕ {0,1}* ≃ {0,1}* -/
def hotel : A ⊕ List Bool ≃ List Bool := ⟨c.enc, c.dec, c.dec_enc, c.enc_dec⟩

end StrCode
end Rom
