-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkToy.lean: small facts at the toys: a placing of two data, and three counts of
elements.




Definitions and proofs.

















Main names:
  `LdToy.plc2`: each of the two data has a corner of its own. `plc2_inj`: it is injective.
  `cardK'`, `cardBn`, `c_one`: `K` has 101 elements, `Bn` has 100, and `Fin 1 → K` has 101.













Limits: no security: these are the numbers of a toy.



Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkStd
import Cb.Obj.LdObjectLinkStdErr
import Cb.Obj.LdObjectToyConf
import Cb.Ld.LdTowerToyStage

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdToy

/-- each of the two data has a corner of its own -/
def plc2 : Fin 2 → Unit → Bool := fun i _ => decide (i = 1)

theorem plc2_inj : Function.Injective plc2 := by
  intro a b h
  have h' := congrFun h ()
  revert h'
  fin_cases a <;> fin_cases b <;> simp [plc2]

end LdToy

open LdToy

namespace LdToy

theorem cardK' : Fintype.card K = 101 := ZMod.card 101

theorem cardBn : Fintype.card Bn = 100 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, cardK']

theorem c_one : Fintype.card (Fin 1 → K) = 101 := by
  rw [Fintype.card_fun, cardK', Fintype.card_fin, pow_one]

end LdToy

end Cb
