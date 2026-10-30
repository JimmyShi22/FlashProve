-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/FoldAdd.lean: the library's folds of a table's rows at a point are additive in the
table. Statements and proofs. Pure algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has. A fold at a point γ is the sum over the vertices b of the Boolean cube of the
multilinear equality weight Alg.eqk γ b times row b, that is, the multilinear extension in the row
variables evaluated at γ. Here a fold is this map, not the protocol's phase of that name
(Johnson/LinkSim/AtText/Defs.lean's terms).
  foldV_add, foldV_zero0       foldV γ (v + v') = foldV γ v + foldV γ v', and foldV γ 0 = 0, for a
                               table v whose rows are indexed by the cube (foldV, Cb/Ld/LdRel.lean).
  foldAll_add, foldAll_zero0   the same for foldAll, which folds all row variables
                               (Cb/Gen/FoldWords.lean).

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/State.lean uses foldV_add; Johnson/LinkSim/AtText/Front.lean and
Johnson/LinkSim/AtText/TwoAnswers.lean use foldAll_add; Johnson/LinkSim/AtText/PadPlace.lean uses
foldAll_zero0.

Limits. The point is the same on both sides.
Terms: lean/GLOSSARY.md.

-/
import Cb.Ld.LdRel
import Cb.Gen.FoldWords

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb

variable {E : Type} [Field E]

/-- The fold foldV at a point is additive in the table. -/
theorem foldV_add {ι J : Type} [Fintype ι] [DecidableEq ι] (γ : ι → E)
    (v v' : (ι → Bool) × J → E) : foldV γ (v + v') = foldV γ v + foldV γ v' := by
  funext c
  show (∑ b, Alg.eqk γ b * (v (b, c) + v' (b, c))) =
    (∑ b, Alg.eqk γ b * v (b, c)) + ∑ b, Alg.eqk γ b * v' (b, c)
  simp only [mul_add, Finset.sum_add_distrib]

/-- The fold foldV of the zero table is 0. -/
theorem foldV_zero0 {ι J : Type} [Fintype ι] [DecidableEq ι] (γ : ι → E) :
    foldV γ (0 : (ι → Bool) × J → E) = 0 := by
  have e := foldV_add γ (0 : (ι → Bool) × J → E) 0
  rw [add_zero] at e
  exact left_eq_add.mp e

/-- The fold foldAll at a point is additive in the table. -/
theorem foldAll_add {V : Type} [AddCommGroup V] [Module E V] {N : Type} [Fintype N]
    [DecidableEq N] (γ : N → E) (f f' : (N → Bool) → V) :
    foldAll γ (f + f') = foldAll γ f + foldAll γ f' := by
  show (∑ v, Alg.eqk γ v • (f v + f' v)) = (∑ v, Alg.eqk γ v • f v) + ∑ v, Alg.eqk γ v • f' v
  simp only [smul_add, Finset.sum_add_distrib]

/-- The fold foldAll of the zero table is 0. -/
theorem foldAll_zero0 {V : Type} [AddCommGroup V] [Module E V] {N : Type} [Fintype N]
    [DecidableEq N] (γ : N → E) : foldAll γ (0 : (N → Bool) → V) = 0 := by
  have e := foldAll_add γ (0 : (N → Bool) → V) 0
  rw [add_zero] at e
  exact left_eq_add.mp e

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.foldV_add
#print axioms OnBytes.LinkSim.foldAll_add
