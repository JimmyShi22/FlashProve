-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GBits.lean: lists that give each round of a protocol its number of proof-of-work bits
("grinding"). Data only, but for small lemmas on the order and on `zero`.
A round with b proof-of-work bits is a round whose challenge is sampled together with b further
bits, all of which must be 0 (`Round.grind`, Iop/Grind.lean; there the prover also sends a nonce);
b = 0: the round is as it is. This file has the lists of these numbers, defined by recursion on the
list of rounds, like `Err` (Iop/Rbr.lean), and how they are composed.
    `GBits s`          a number for each round of s
    `GBits.zero s`     0 everywhere
    `GBits.app`, `GBits.rep`    two lists of rounds in a row; n copies of one round with the same
                                number
    `GBits.Le g g'`    round by round at most; `GBits.zero_le`, `Le.refl`, `Le.trans`, `Le.app`
    `GBits.sum`, `GBits.count`  the sum of the numbers; how many rounds have proof-of-work bits (b ≠
                                0)
Limits: nothing is said on a protocol, a prover or a bound.
-/
import Iop.Rbr

set_option autoImplicit false

namespace Iop

/-- For each round a number of proof-of-work bits. -/
def GBits : Shape → Type
  | [] => Unit
  | _ :: s => ℕ × GBits s

namespace GBits

/-- no round has proof-of-work bits -/
def zero : (s : Shape) → GBits s
  | [] => ()
  | _ :: s => (0, zero s)

def app : {s t : Shape} → GBits s → GBits t → GBits (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (e, a), b => (e, app a b)

/-- n copies of the round r, each with b proof-of-work bits -/
def rep (r : Round) (b : ℕ) : (n : ℕ) → {t : Shape} → GBits t → GBits (List.replicate n r ++ t)
  | 0, _, g => g
  | n + 1, _, g => (b, rep r b n g)

/-- round by round at most -/
def Le : {s : Shape} → GBits s → GBits s → Prop
  | [], _, _ => True
  | _ :: _, (b, g), (b', g') => b ≤ b' ∧ Le g g'

theorem Le.refl : ∀ {s : Shape} (g : GBits s), Le g g
  | [], _ => trivial
  | _ :: _, (_, g) => ⟨Nat.le_refl _, Le.refl g⟩

theorem Le.trans : ∀ {s : Shape} {a b c : GBits s}, Le a b → Le b c → Le a c
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _), h, h' => ⟨Nat.le_trans h.1 h'.1, Le.trans h.2 h'.2⟩

theorem zero_le : ∀ {s : Shape} (g : GBits s), Le (zero s) g
  | [], _ => trivial
  | _ :: _, (_, g) => ⟨Nat.zero_le _, zero_le g⟩

theorem Le.app :
    ∀ {s t : Shape} {a a' : GBits s} {b b' : GBits t},
      Le a a' → Le b b' → Le (GBits.app a b) (GBits.app a' b')
  | [], _, _, _, _, _, _, hb => hb
  | _ :: _, _, (_, _), (_, _), _, _, ha, hb => ⟨ha.1, Le.app ha.2 hb⟩

theorem zero_app : ∀ (s t : Shape), GBits.app (zero s) (zero t) = zero (s ++ t)
  | [], _ => rfl
  | _ :: s, t => congrArg (Prod.mk 0) (zero_app s t)

theorem rep_zero (r : Round) :
    ∀ (n : ℕ) (t : Shape), rep r 0 n (zero t) = zero (List.replicate n r ++ t)
  | 0, _ => rfl
  | n + 1, t => congrArg (Prod.mk 0) (rep_zero r n t)

/-- the sum of the numbers -/
def sum : {s : Shape} → GBits s → ℕ
  | [], _ => 0
  | _ :: _, (b, g) => b + sum g

/-- how many rounds have proof-of-work bits -/
def count : {s : Shape} → GBits s → ℕ
  | [], _ => 0
  | _ :: _, (b, g) => (if b = 0 then 0 else 1) + count g

end GBits
end Iop
