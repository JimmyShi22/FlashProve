-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CompleteRef.lean: a postcondition that asks nothing holds of every program (`tri_true`;
`Tri`: Compile/EraseKit.lean).
-/
import Compile.CompleteAcc

noncomputable section

namespace Compile.Cmpl
open Iop Rom Prob

/-! ## Postconditions -/

section Law

variable {S : OSpec} {sp : Split S} {α β γ : Type} (f : Fam S)

variable {f}

theorem tri_true (c : Step S sp α) (vs : List Bits) : Tri f c vs fun _ _ => True := fun _ _ =>
  trivial

end Law

end Compile.Cmpl
