-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTieQ.lean: the one condition of the tie is met by the powers of square-and-multiply.
This file is about one part of the lookup argument: the chain of sumchecks that ties the product
over the keys to the products over the table (the tie, `TieP`, Cb/Ld/LdLkpTie.lean).

Statement (`Cb.Spec.ldLkpTie_hU`) and proof. A guard against an empty theorem, and what a caller of
Cb/Ld/LdLkpTie.lean plugs in.

For any values PT_j and any W ≥ 1 let Q_j := `Cb.Lkp.hU W PT j` (Cb/Gen/LkpAlg.lean). Then
  Q_j = Q_(j+1)² · PT_j for j < W - 1 (for a `D : TieP E` whose Q is `hU W` of its PT:
  `D.StepTo (W - 1)` of Cb/Ld/LdLkpTie.lean);
  Q_(W-1) = PT_(W-1) (so the claim that is open after the last step is a claim on the last product);
  Q_0 = the product over j < W of PT_j ^ (2 ^ j) (so "PK = Q_0" is the third clause of the claim
  after the first challenge, `Cb.Lkp.Mid`).

Limits: this file says nothing at j ≥ W - 1 for the first line: there it fails in general.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpTie
import Cb.Gen.LkpAlgProofs

set_option autoImplicit false

namespace Cb
open Finset Cb.Lkp

namespace Spec

def ldLkpTie_hU : Prop :=
  ∀ (E : Type) [Field E] (W : ℕ) (PT : ℕ → E), 1 ≤ W →
    (∀ j < W - 1, Lkp.hU W PT j = Lkp.hU W PT (j + 1) ^ 2 * PT j) ∧
    Lkp.hU W PT (W - 1) = PT (W - 1) ∧
    Lkp.hU W PT 0 = ∏ j ∈ range W, PT j ^ 2 ^ j

end Spec

theorem ldLkpTie_hU : Spec.ldLkpTie_hU := by
  intro E _ W PT hW
  have h := honest_rows E W PT hW
  exact ⟨fun j hj => by rw [h.mul j hj, h.sq j hj], h.top, h.eq.symm⟩

end Cb
