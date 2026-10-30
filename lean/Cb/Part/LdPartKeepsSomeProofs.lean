-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartKeepsSomeProofs.lean: the proofs of the three statements of
Cb/Part/LdPartKeepsSome.lean, and one definition that needs one of them:
`P.idle₀ K p k hP hS hk hK`: the idle row of the kept messages' naming as a term, at a kept segment
by choice. Nothing else is said here.
-/
import Cb.Part.LdPartKeepsSome
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

theorem ldPartKeepsSome_rp : Spec.ldPartKeepsSome_rp := fun _ _ _ _ _ _ P K hK j => P.rp_pos K hK j

theorem ldPartKeepsSome_lt : Spec.ldPartKeepsSome_lt := by
  intro F E _ _ _ _ Cf P p k s hP _ hs
  unfold LdPartD.onKept at hs
  rw [decide_eq_true_eq] at hs
  obtain ⟨q, hq, e⟩ := hs
  rw [← e]
  exact (hP.keptIn k q hq).2.1

theorem ldPartKeepsSome_need : Spec.ldPartKeepsSome_need := by
  intro F E _ _ _ _ Cf P K k h
  refine ⟨fun y => ?_⟩
  have e : P.rpS K (P.onKept k) y.1.1 = 0 := if_neg (by rw [h]; exact Bool.false_ne_true)
  exact Nat.not_lt_zero _ (lt_of_lt_of_eq y.1.2.2 e)

/-- The idle row as a term. -/
def LdPartD.idle₀ {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    {Cf : LdCf F E} (P : LdPartD Cf) (K : LdPartPk) (p k : ℕ) (hP : P.Props p) (hS : P.KeepsSome)
    (hk : k + 1 < P.n) (hK : 0 < K.P) :
    (Σ s : Fin P.n, Fin (P.rpS K (P.onKept k) s)) × Fin K.P :=
  P.idleRow K k (hS k hk).choose_spec
    (ldPartKeepsSome_lt F E Cf P p k _ hP hk (hS k hk).choose_spec) hK

end Cb
