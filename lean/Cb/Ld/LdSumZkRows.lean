-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumZkRows.lean: zero knowledge of an interleaved encoding from zero knowledge of one row.

The file has the statement `Spec.ld_zk_il` and its proof, for E finite and not empty.
The file follows the paper that this protocol builds on (lean/CREDITS.md).
The zero-knowledge sumcheck (Cb/Ld/LdSum.lean) asks that the encoding of its fresh mask table hide t
long positions. The rows of a table are encoded with independent randomness, so this follows from
the same property of the code of one row.
(In that paper the errors of the rows add; here all errors are 0.) The proof renames the randomness
row by row (Prob/LawEquiv.lean).
-/
import Cb.Ld.LdRel
import Prob.LawEquiv
import Prob.LawKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec

def ld_zk_il : Prop :=
  ∀ (E P : Type) [Fintype E] [Nonempty E] (C : LdCode E P) (R : Type) [Fintype R]
      [DecidableEq R] (t : ℕ),
    C.Zk t → (C.il R).Zk t

end Spec

theorem ld_zk_il : Spec.ld_zk_il := by
  intro E P _ _ C R _ _ t hZ S hS m m'
  have hrow : ∀ i : R, ∃ e : (C.Q → E) ≃ (C.Q → E),
      ∀ r, C.Nn.shows S (fun j => m (i, j)) r = C.Nn.shows S (fun j => m' (i, j)) (e r) :=
    fun i => exists_equiv_of_map_eq _ _ (hZ S hS _ _)
  choose e he using hrow
  refine map_unif_reindex
    ((Equiv.curry R C.Q E).trans ((Equiv.piCongrRight e).trans (Equiv.curry R C.Q E).symm)) _ _
    fun r => ?_
  funext p
  have h1 : ∀ i : R, C.enc (fun j => m (i, j)) (fun q => r (i, q)) p.1 =
      C.enc (fun j => m' (i, j)) (e i fun q => r (i, q)) p.1 := fun i =>
    eq_of_heq (Sigma.mk.inj (congrFun (he i fun q => r (i, q)) p)).2
  refine Sigma.ext rfl (heq_of_eq (funext fun s => ?_))
  exact congrFun (h1 s.1) s.2

end Cb
