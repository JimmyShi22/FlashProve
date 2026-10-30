-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Blocks.lean: under every coding of the typed oracles into one hash function with
blocks of lam > 0 bits, no typed answer has more than K + 1 hash blocks. In the oracles typedOracleFamily lam K L
a round's answer is K digests and one more.
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
  blocks_le        the statement above: m.blocks o ≤ K + 1, for every coding m of the oracles
                   typedOracleFamily lam K L and every oracle o.
  blocks_of_card   If a type with (2 ^ lam) ^ c elements is in bijection with the b-tuples of blocks
                   of lam > 0 bits, then b = c.

Limits. One upper bound for all oracles: most answers have one block.

How it fits. Within.lean takes a bound Bk on the blocks of a typed answer under the coding at every
d. A coding has a bijection from each oracle's answers onto tuples of hash blocks, so the number of
answers fixes the number of blocks, and Bk := K + 1 serves at every coding without unfolding one.
AtDescription.lean, Joined.lean, IdAlone.lean and LaidId.lean use blocks_le in this way.

Sources. Oracles whose answer is one digest: Rom.OracleCoding.blocks_eq_one (Johnson/Top/BlocksOne.lean).
The proof of blocks_of_card has the form of that of Rom.blocks_eq_of_equiv (Rom/CutKit.lean).
-/
import Johnson.Top.BlocksOne
import OnBytes.TypedOracleCompiler.Compile.Batch.Oracles

set_option autoImplicit false

namespace OnBytes.FrontRoad
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop

/-- If a type with (2 ^ lam) ^ c elements is in bijection with the b-tuples of blocks of lam > 0
bits, then b = c. -/
theorem blocks_of_card {lam : ℕ} (hl : 0 < lam) {R : Type} [Fintype R] {b c : ℕ}
    (e : R ≃ (Fin b → Fin lam → Bool)) (hc : Fintype.card R = (2 ^ lam) ^ c) : b = c := by
  have h := Fintype.card_congr e
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at h
  rw [hc] at h
  exact (Nat.pow_right_injective (a := 2 ^ lam) (by
    have : 2 ^ 1 ≤ 2 ^ lam := Nat.pow_le_pow_right (by omega) hl
    omega) h).symm

/-- For every coding m of the oracles typedOracleFamily lam K L, with lam > 0, and every oracle o, an answer of o
has at most K + 1 hash blocks. -/
theorem blocks_le {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (m : OracleCoding (typedOracleFamily lam K L) lam)
    (hl : 0 < lam) (o : OracleName) : m.blocks o ≤ K + 1 := by
  have one : ∀ o' : OracleName, ((typedOracleFamily lam K L).Rng o' ≃ (Fin lam → Bool)) → m.blocks o' ≤ K + 1 :=
    fun o' e => by
      rw [m.blocks_eq_one hl o' e]
      omega
  have many : ∀ o' : OracleName, ((typedOracleFamily lam K L).Rng o' = ((Fin K → Fin lam → Bool) × (Fin lam → Bool))) →
      m.blocks o' ≤ K + 1 := fun o' h => by
    have e : ((Fin K → Fin lam → Bool) × (Fin lam → Bool)) ≃
        (Fin (m.blocks o') → Fin lam → Bool) := (Equiv.cast h).symm.trans (m.rng o')
    refine le_of_eq (blocks_of_card hl e ?_)
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    rw [pow_succ]
  cases o with
  | leaf => exact one _ (Equiv.refl _)
  | node => exact one _ (Equiv.refl _)
  | rleaf => exact one _ (Equiv.refl _)
  | rnode => exact one _ (Equiv.refl _)
  | g t => exact one _ (Equiv.refl _)
  | other => exact one _ (Equiv.refl _)
  | fb t => exact many _ rfl
  | fbw t k => exact many _ rfl
  | ann =>
    have e : Unit ≃ (Fin (m.blocks OracleName.ann) → Fin lam → Bool) := m.rng OracleName.ann
    have h0 : m.blocks OracleName.ann = 0 := blocks_of_card hl e (by simp)
    rw [h0]
    omega

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.blocks_le
