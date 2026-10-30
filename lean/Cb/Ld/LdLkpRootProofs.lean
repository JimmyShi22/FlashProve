-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpRootProofs.lean: proofs for Cb/Ld/LdLkpRoot.lean (the point of a forest: claims on the
products of all trees into the sum claim of level 0).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdLkpRoot.lean):
  `ldLkpRoot_link` (under `D.Step` and `R.IncOK`), `ldLkpRoot_back`, `ldLkpRoot_ok`: the conditions
    of the step.
  `ldLkpRoot_err`: the bound on the number of bad points: g |E|^(g-1) of |E|^g.
  `ldLkpRoot_jt`: the output joint: the tree's joint at level 0.
  `ldLkpRoot_good`: under `D.Step` and `R.IncOK`: the point of a forest, at the base: `R.rootA`,
    `BkA.Good`.
  `ldLkpRoot_exact`: see its statement in Cb/Ld/LdLkpRoot.lean.

Limits: what the head of Cb/Ld/LdLkpRoot.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpRoot
import Cb.Ld.LdLkpTreePProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpRoot_link : Spec.ldLkpRoot_link E := by
  intro R hS hI st ϱ m
  have h := (ldLkpP_sum E R.D hS 0
    (hSumAll (R.D.T0.vars (R.toIn.nx st ϱ)) (R.D.T0.sum (R.toIn.nx st ϱ) m) +
        ∑ j, R.D.T0.slS (R.toIn.nx st ϱ) j * m j,
      R.toIn.nx st ϱ) m).1 rfl
  refine h.symm.trans ?_
  show Alg.mle (R.D.U st m 0) ϱ + ∑ j, R.D.inc0 st ϱ j * m j =
    ∑ θ, Alg.eqk ϱ θ * (R.D.U st m 0 θ + ∑ j, R.form st θ j * m j)
  simp only [hI st ϱ]
  unfold Alg.mle
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem ldLkpRoot_back : Spec.ldLkpRoot_back E := fun _ _ _ => rfl

theorem ldLkpRoot_ok : Spec.ldLkpRoot_ok E := fun R => ok_eqPt E (Fin (R.D.g + 0))

theorem ldLkpRoot_err : Spec.ldLkpRoot_err E := fun R => by
  show Fintype.card (Fin (R.D.g + 0)) * Fintype.card E ^ (Fintype.card (Fin (R.D.g + 0)) - 1) = _
  simp

theorem ldLkpRoot_jt : Spec.ldLkpRoot_jt E := fun _ _ _ _ _ _ _ => rfl

theorem ldLkpRoot_good : Spec.ldLkpRoot_good E := fun R Ex M Wp Kc R0 msg hS hI =>
  pscIn_goodAt E R.toIn Ex M Wp Kc R0 msg (ldLkpRoot_link E R hS hI)
    (ldLkpRoot_back E R) (ldLkpRoot_ok E R)

theorem ldLkpRoot_exact : Spec.ldLkpRoot_exact E := fun R Ex M Wp _ P =>
  draw_exact_any Ex (M × Wp) R.toIn.ev.D R.toIn.nxX P

end
end Cb
