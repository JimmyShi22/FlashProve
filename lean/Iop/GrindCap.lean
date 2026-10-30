-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/GrindCap.lean: the data of the honest prover's search for a nonce, after the rule planned for
the implementation: nonces are the numbers below 2^64; in a round with b proof-of-work bits the
honest prover tries 0, 1, .., 2^(b + 7) − 1. Data, and the condition on them. (Words of this
library: lean/GLOSSARY.md.)
    `cap64`          `GrData (Fin (2^64))` (Iop/GrindWire.lean): mo b, the last number tried, is
                     2^(b + 7) − 1; a number is encoded as itself modulo 2^64; a nonce is decoded as
                     its value
    `cap64_ok`       the numbers tried with at most 57 such bits are decoded to themselves (that
                     with 58 they are not is not proved in this library)
    `cap64_ok_le`    so with at most n ≤ 57
The rule is known here only at second hand, as a statement of what the implementation is to do: "the
least n, counted from 0, that passes; cap T = 2^(g + 7)". The released programs do not follow that
plan: their search has one cap, 2^63 − 1 tries whatever the work bits, at which the process ends,
and their verifier takes any nonce that passes, not only the least (by readings of their source).
What happens at the cap is not a matter of these data.
Notation: `GrData W`: a structure (Iop/GrindWire.lean): what the wire record adds to the numbers of
proof-of-work bits; its fields, in `GrData` (there): `mo : ℕ → ℕ`: in a round with b proof-of-work
bits the honest prover tries the nonces for 0, .., mo b: at most mo b + 1 attempts; `enc : ℕ → W`:
the nonce for a number; `dec : W → ℕ`: the number that a nonce encodes; `D.OK n : Prop`
(`GrData.OK`, there): `∀ b k, b ≤ n → k ≤ D.mo b → D.dec (D.enc k) = k`.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.GrindWire

namespace Iop

/-- at most 2^(b + 7) attempts; the numbers below 2^64 as nonces -/
def cap64 : GrData (Fin (2 ^ 64)) :=
  ⟨fun b => 2 ^ (b + 7) - 1, fun k => Fin.ofNat (2 ^ 64) k, fun w => w.val⟩

theorem cap64_tries (b : ℕ) : cap64.mo b + 1 = 2 ^ (b + 7) :=
  Nat.sub_add_cancel (Nat.one_le_two_pow)

theorem cap64_ok : cap64.OK 57 := by
  intro b k hb hk
  have h1 : 2 ^ (b + 7) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 0 < 2 ^ (b + 7) := by positivity
  have hk' : k ≤ 2 ^ (b + 7) - 1 := hk
  show k % 2 ^ 64 = k
  exact Nat.mod_eq_of_lt (by omega)

theorem cap64_ok_le {n : ℕ} (hn : n ≤ 57) : cap64.OK n := fun b k hb hk =>
  cap64_ok b k (le_trans hb hn) hk

end Iop
