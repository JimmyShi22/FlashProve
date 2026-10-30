-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/HeldCounts.lean: the number of typed values of a written round, and the counts of the
rounds of positions in the forms in which the blocks have them.

`held_positions` and `held_cs` (OnBytes/Slice/HeldKindsAny.lean) end in a comparison that holds the
number of the round's typed values, `nVals (Fmt.dsOf d.entry d.kind)`. This file computes that
number for every round of a kind other than seeds and sealing, from the entry's numbers of draws.
With it the two theorems are stated for the very counts that the blocks of a proximity test have:
with n for 2 ^ logN positions, t draws and a radius e, (n - e - 1) ^ t in a round that draws
positions alone, and (n - e - 1) ^ t q + n ^ t (L (rows - 1)) in a round that draws positions and
one batching element.

Main theorems: `nVals_append`, `nVals_replicate`, `nVals_dsOf`, `nVals_positions`,
`nVals_positions_one`, `held_positions_count`, `held_cs_count`.
What is not claimed: that these counts bound a prover's chance. Nothing on rounds of the kinds seeds
and sealing. What OnBytes/Slice/HeldKindsAny.lean does not claim is not claimed here. For proofs
only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Slice.HeldKindsAny

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob _root_.Run OnBytes.Params
open scoped ENNReal

/-- The typed values of two lists of draws, one after the other. -/
theorem nVals_append : ∀ a b : List Fmt.Draw, nVals (a ++ b) = nVals a * nVals b
  | [], b => by simp [nVals]
  | .elem :: a, b => by
      show Fmt.Fld.two.p ^ 3 * nVals (a ++ b) = Fmt.Fld.two.p ^ 3 * nVals a * nVals b
      rw [nVals_append a b, Nat.mul_assoc]
  | .elemNZ :: a, b => by
      show (Fmt.Fld.two.p ^ 3 - 1) * nVals (a ++ b) = (Fmt.Fld.two.p ^ 3 - 1) * nVals a * nVals b
      rw [nVals_append a b, Nat.mul_assoc]
  | .pos k :: a, b => by
      show 2 ^ k * nVals (a ++ b) = 2 ^ k * nVals a * nVals b
      rw [nVals_append a b, Nat.mul_assoc]
  | .trits n :: a, b => by
      show 4 ^ n * nVals (a ++ b) = 4 ^ n * nVals a * nVals b
      rw [nVals_append a b, Nat.mul_assoc]
  | .sealed :: a, b => by
      show (2 ^ 64) ^ 4 * nVals (a ++ b) = (2 ^ 64) ^ 4 * nVals a * nVals b
      rw [nVals_append a b, Nat.mul_assoc]

/-- The typed values of one draw, t times. -/
theorem nVals_replicate (x : Fmt.Draw) : ∀ t : ℕ, nVals (List.replicate t x) = nVals [x] ^ t
  | 0 => rfl
  | t + 1 => by
      have e : List.replicate (t + 1) x = [x] ++ List.replicate t x := rfl
      rw [e, nVals_append, nVals_replicate x t, pow_succ, Nat.mul_comm]

/-- The typed values of a written round of a kind other than seeds and sealing: a power of two for
each position, p ^ 3 for each element, p ^ 3 - 1 for each element other than 0, four for each pair
of bits. -/
theorem nVals_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (hk1 : k ≠ .seeds) (hk2 : k ≠ .sealed) :
    nVals (Fmt.dsOf e k) = (2 ^ e.logN) ^ e.poss * ((Fmt.Fld.two.p ^ 3) ^ (e.drawE - e.drawNZ) *
      ((Fmt.Fld.two.p ^ 3 - 1) ^ e.drawNZ * 4 ^ e.trits)) := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg hk1, if_neg hk2, nVals_append, nVals_append, nVals_append, nVals_replicate,
    nVals_replicate, nVals_replicate]
  simp [nVals, Nat.mul_assoc]

/-- A round that draws positions alone. -/
theorem nVals_positions {d : PQ.RD} (hE : d.entry.drawE = 0) (hNZ : d.entry.drawNZ = 0)
    (ht : d.entry.trits = 0) (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) :
    nVals (Fmt.dsOf d.entry d.kind) = (2 ^ d.entry.logN) ^ d.entry.poss := by
  rw [nVals_dsOf _ _ hk1 hk2, hE, hNZ, ht]
  simp

/-- A round that draws positions and one element. -/
theorem nVals_positions_one {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d)
    (hE : d.entry.drawE = 1) (hNZ : d.entry.drawNZ = 0) (ht : d.entry.trits = 0)
    (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) :
    nVals (Fmt.dsOf d.entry d.kind) = (2 ^ d.entry.logN) ^ d.entry.poss * s.cardE := by
  rw [nVals_dsOf _ _ hk1 hk2, hE, hNZ, ht, cardE_eq H]
  simp

/-- A round that draws t positions among n = 2 ^ logN and nothing else, and is priced by the
agreement to the power t: the count (n - e - 1) ^ t meets the bound. e: a radius with
n - e - 1 ≤ a n, for a number a that the agreement encloses. -/
theorem held_positions_count {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d)
    {agree : Bound} {a : ℚ} (ha : Encl agree a) (hg : agree.bad = false) (e : ℕ)
    (he : ((2 ^ d.entry.logN : ℕ) : ℚ) - (e : ℚ) - 1 ≤ a * ((2 ^ d.entry.logN : ℕ) : ℚ))
    (hb : (Bound.pow agree d.entry.poss).bad = false)
    (hr : r.error = (Bound.pow agree d.entry.poss).error)
    (hE : d.entry.drawE = 0) (hNZ : d.entry.drawNZ = 0) (ht : d.entry.trits = 0)
    (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) :
    Meets s d ((2 ^ d.entry.logN - e - 1) ^ d.entry.poss) :=
  held_positions H ha hg (2 ^ d.entry.logN) e d.entry.poss (by positivity) he hb hr _
    (by rw [nVals_positions hE hNZ ht hk1 hk2])

/-- A round that draws t positions among n = 2 ^ logN and one batching element, and is priced by the
agreement to the power t and a list size times the error of a combination by powers: the count
(n - e - 1) ^ t q + n ^ t (L (rows - 1)) meets the bound. -/
theorem held_cs_count {s : Setting} {r : PlanRound} {d : PQ.RD} (H : Held s r d)
    {agree : Bound} {a : ℚ} (ha : Encl agree a) (hg : agree.bad = false) (e L rows : ℕ)
    (he : ((2 ^ d.entry.logN : ℕ) : ℚ) - (e : ℚ) - 1 ≤ a * ((2 ^ d.entry.logN : ℕ) : ℚ))
    (hb : (Bound.pow agree d.entry.poss + Bound.ofNat L * powersError s rows).bad = false)
    (hr : r.error = (Bound.pow agree d.entry.poss + Bound.ofNat L * powersError s rows).error)
    (hE : d.entry.drawE = 1) (hNZ : d.entry.drawNZ = 0) (ht : d.entry.trits = 0)
    (hk1 : d.kind ≠ .seeds) (hk2 : d.kind ≠ .sealed) :
    Meets s d ((2 ^ d.entry.logN - e - 1) ^ d.entry.poss * s.cardE +
      (2 ^ d.entry.logN) ^ d.entry.poss * (L * (rows - 1))) :=
  held_cs H ha hg (2 ^ d.entry.logN) e d.entry.poss L rows (by positivity) he hb hr _
    (by rw [nVals_positions_one H hE hNZ ht hk1 hk2])

end OnBytes.Slice

#print axioms OnBytes.Slice.nVals_dsOf
#print axioms OnBytes.Slice.held_positions_count
#print axioms OnBytes.Slice.held_cs_count
