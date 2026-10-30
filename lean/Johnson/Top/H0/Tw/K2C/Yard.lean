-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Yard.lean: A YARDSTICK BESIDE THE KIND «the code switch»: NO BLOCK IMPORTS
THIS FILE. Each test that the kind's own text asks in place of a yes-or-no function of the program's
files says, at every input, what that function says; and what each own test checks is stated as a
proposition.
  handedOk_eq · sizedOk_eq      K2C/Head.lean's against Head.planHanded · Head.Covered.sized
  handedOk_iff · sizedOk_iff    what they check
(K2/Target.lean's tests: K2/TargetAgree.lean.)
No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

theorem handedOk_eq (hp : Head.HPlanH2) (list : Tail2) (F : Fork) : handedOk hp list F =
    Head.planHanded hp list F := rfl

theorem sizedOk_eq (c : Head.Covered) (T : Nat) : sizedOk c T = c.sized T := rfl

theorem sizedOk_iff (c : Head.Covered) (T : Nat) : sizedOk c T = true ↔ c.tokv.size = T ∧ c.hOn.size
    = T ∧ c.hWin.size = T ∧ c.hOnC.size = T := by
  simp [sizedOk, and_assoc]

theorem handedOk_iff (hp : Head.HPlanH2) (list : Tail2) (F : Fork) :
    handedOk hp list F = true ↔ list.planned = true ∧ list.nt = hp.Tp.nt ∧ F.trees.map arraySig =
        hp.Fp.trees.map arraySig := by
  simp [handedOk, and_assoc]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.handedOk_iff
