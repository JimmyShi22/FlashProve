-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GBitsCount.lean: helper lemmas on how many rounds have proof-of-work bits (`GBits.count`) and on
how many such bits there are in all (`GBits.sum`; both of Iop/GBits.lean), for lists that are
composed: by `GBits.zero`, `GBits.app`, `GBits.rep`.
Notation: `Round`: a structure (Iop/Shape.lean): one round: a prover message and then a challenge;
`Shape : Type 1` (there): the list of a protocol's rounds, in order; `GBits s : Type`
(Iop/GBits.lean): for each round a number of proof-of-work bits; `GBits.zero s : GBits s` (there):
no round has proof-of-work bits; `GBits.app g g' : GBits (s ++ t)`, for `g : GBits s`,
`g' : GBits t` (there): two lists of rounds in a row;
`GBits.rep r b n g : GBits (List.replicate n r ++ t)`, for `g : GBits t` (there): n copies of the
round r, each with b proof-of-work bits, then g.
Limits: nothing is said on any protocol.
-/
import Iop.GBits

set_option autoImplicit false

namespace Iop
namespace GBits

theorem count_zero : ∀ s : Shape, (GBits.zero s).count = 0
  | [] => rfl
  | _ :: s => by
    show (if (0 : ℕ) = 0 then 0 else 1) + (GBits.zero s).count = 0
    rw [if_pos rfl, count_zero s]

theorem count_app :
    ∀ {s t : Shape} (g : GBits s) (g' : GBits t), (GBits.app g g').count = g.count + g'.count
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (b, g), g' => by
    show (if b = 0 then 0 else 1) + (GBits.app g g').count =
      (if b = 0 then 0 else 1) + g.count + g'.count
    rw [count_app g g', Nat.add_assoc]

theorem count_rep (r : Round) (b : ℕ) :
    ∀ (n : ℕ) {t : Shape} (g : GBits t),
      (GBits.rep r b n g).count = n * (if b = 0 then 0 else 1) + g.count
  | 0, _, g => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | n + 1, _, g => by
    show (if b = 0 then 0 else 1) + (GBits.rep r b n g).count = _
    rw [count_rep r b n g, Nat.succ_mul]
    omega

theorem count_rep0 (r : Round) (n : ℕ) {t : Shape} (g : GBits t) :
    (GBits.rep r 0 n g).count = g.count := by
  rw [count_rep, if_pos rfl, Nat.mul_zero, Nat.zero_add]

theorem sum_zero : ∀ s : Shape, (GBits.zero s).sum = 0
  | [] => rfl
  | _ :: s => by
    show 0 + (GBits.zero s).sum = 0
    rw [sum_zero s]

theorem sum_app :
    ∀ {s t : Shape} (g : GBits s) (g' : GBits t), (GBits.app g g').sum = g.sum + g'.sum
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (b, g), g' => by
    show b + (GBits.app g g').sum = b + g.sum + g'.sum
    rw [sum_app g g', Nat.add_assoc]

theorem sum_rep (r : Round) (b : ℕ) :
    ∀ (n : ℕ) {t : Shape} (g : GBits t), (GBits.rep r b n g).sum = n * b + g.sum
  | 0, _, g => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | n + 1, _, g => by
    show b + (GBits.rep r b n g).sum = _
    rw [sum_rep r b n g, Nat.succ_mul]
    omega

end GBits
end Iop
