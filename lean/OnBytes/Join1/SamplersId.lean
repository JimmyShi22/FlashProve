-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Join1/SamplersId.lean: the samplers that change nothing: each round's verifier message is
its own source.

For a protocol whose written verifier messages are the hash blocks themselves (with their test
bits): the sampler's law and the work then stand inside the protocol's own counts, and the pass
through samplers (Iop/Pull.lean) has nothing left to do.

Main names:
  `Sampler.idS r`, `Samplers.idS s`: source := the round's verifier messages, the map := the
    identity, w := 1.
  `idS_good`: `(Samplers.idS s).Good κ K` for every 1 ≤ κ, 1 ≤ K. `idS_good_one`: at κ = K = 1.
  `idS_fib`: `(Samplers.idS s).Fib`.
  `pull_idS`: `Shape.pull s (Samplers.idS s) = s`. `grind_zeroS`:
    `Shape.grind W s (GBits.zero s) = s`: the rounds behind these samplers, and with no bit of work,
    are the rounds themselves.

Limits: nothing on any protocol: the two equations are between lists of rounds; that a protocol
passed through these samplers and no bits decides as before is not stated here.

Terms: lean/GLOSSARY.md.

-/
import Iop.GBits
import Iop.Grind
import Iop.PullProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- The sampler that changes nothing. -/
def Sampler.idS (r : Round) : Sampler r where
  Src := r.Chal
  φ := id
  w := 1

/-- In each round the sampler that changes nothing. -/
def Samplers.idS : (s : Shape) → Samplers s
  | [] => PUnit.unit
  | r :: s => (Sampler.idS r, Samplers.idS s)

/-- They are good at every κ and K that are at least 1. -/
theorem idS_good : ∀ (s : Shape) (κ K : ℝ≥0∞), 1 ≤ κ → 1 ≤ K → (Samplers.idS s).Good κ K
  | [], _, _, _, hK => hK
  | r :: s, κ, K, hκ, hK => by
      refine ⟨fun c => cnt_le_one fun a b ha hb => ha.trans hb.symm, ?_, 1,
        idS_good s κ 1 hκ le_rfl, ?_⟩
      · show ((1 : ℕ) : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) ≤ κ * (Fintype.card r.Chal : ℝ≥0∞)
        rw [Nat.cast_one]
        exact mul_le_mul' hκ le_rfl
      · show ((1 : ℕ) : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) * 1 ≤
          K * (Fintype.card r.Chal : ℝ≥0∞)
        rw [Nat.cast_one, mul_one]
        exact mul_le_mul' hK le_rfl

/-- At κ = K = 1. -/
theorem idS_good_one (s : Shape) : (Samplers.idS s).Good 1 1 := idS_good s 1 1 le_rfl le_rfl

/-- Every fibre has at most w elements. -/
theorem idS_fib (s : Shape) : (Samplers.idS s).Fib := (idS_good_one s).fib

/-- Behind the samplers that change nothing the rounds are the rounds themselves. -/
theorem pull_idS : ∀ s : Shape, Shape.pull s (Samplers.idS s) = s
  | [] => rfl
  | r :: s => by
      show r.pull (Sampler.idS r) :: Shape.pull s (Samplers.idS s) = r :: s
      rw [pull_idS s]
      rfl

/-- With no bit of work the rounds are the rounds themselves. -/
theorem grind_zeroS (W : Type) [Inhabited W] : ∀ s : Shape, Shape.grind W s (GBits.zero s) = s
  | [] => rfl
  | r :: s => by
      show r.grind W 0 :: Shape.grind W s (GBits.zero s) = r :: s
      rw [grind_zeroS W s]
      rfl

end Iop
