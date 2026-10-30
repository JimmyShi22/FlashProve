-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_life2_Wr.lean: putting adversaries in a sequence is associative.

  `advBind_assoc`    (P.bind f).bind g = P.bind fun a => (f a).bind g, for adversaries (`Adv`,
                     Rom/World.lean; `Adv.bind`, Compile/Step1_defc_Gen.lean).
-/
import Compile.Spec
import Compile.Step1_defc_Gen
import Rom.LateAdv
import Compile.Step1_defc_L
import Compile.Step1_life2_Chall
import Iop.ShapeKit

noncomputable section

namespace Compile
namespace Life2
open Iop Rom Prob
open Compile.DefC (virtL)

variable {I X : Type} {lam : ℕ}

variable (p : Params)

/-! ## Sequences of adversaries -/

section Adm2

variable {S : OSpec} {Out In α β γ : Type}

theorem advBind_assoc (P : Adv S Out In α) (f : α → Adv S Out In β) (g : β → Adv S Out In γ) :
    (P.bind f).bind g = P.bind fun a => (f a).bind g := by
  induction P with
  | halt a => rfl
  | sample m k ih => simp only [Adv.bind, ih]
  | query o q k ih => simp only [Adv.bind, ih]
  | call m k ih => simp only [Adv.bind, ih]

end Adm2

end Life2
end Compile
