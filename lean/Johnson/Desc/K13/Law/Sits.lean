-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Sits.lean: "W sits as the plan says": five public facts on a record of (Eval)
(`EvalAt`, Johnson/Desc/K13/Law/StepBack.lean) against a plan's codes and shape, as a proposition
and as a test with code. A structure, two definitions, and a statement with its proof. It stands
over that file alone.
Main names:
  `SitsPlain cs Sh D`: the record's statement's codes are the plan's · W's number bears a message of
    the shape that the plan has for W · W's layout is the plan's · every message length of the
    plan's codes is a power of two · the number of W's shape's code is in the plan's list.
  `sitsL cs Sh D`: the five as named tests with code, for a print. `sitsB`: all of them.
  `sitsB_iff`: the test says yes exactly where the five hold.

What is not claimed. That a record of a run meets them: a run can show it. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.StepBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open OnBytes.Params (LinShape)

/-- **W sits as the plan says.** -/
structure SitsPlain (cs : Codes) (Sh : LinShape) (D : EvalAt) : Prop where
  codes : D.st.codes = cs
  shape : (D.st.oracles[D.w]?).map (·.shape) = some Sh.w
  lay : D.lay = linLayW cs Sh
  lengths : cs.lengthsOk = true
  code : Sh.w.code < cs.base.size

/-- The five as named tests with code. -/
def sitsL (cs : Codes) (Sh : LinShape) (D : EvalAt) : List (String × Bool) :=
  [("the record's codes are the plan's", decide (D.st.codes = cs)),
   ("W's number bears the plan's shape", decide ((D.st.oracles[D.w]?).map (·.shape) = some Sh.w)),
   ("W's layout is the plan's", decide (D.lay = linLayW cs Sh)),
   ("the codes' lengths are powers of two", cs.lengthsOk),
   ("the shape's code is in the list", decide (Sh.w.code < cs.base.size))]

/-- All of them. -/
def sitsB (cs : Codes) (Sh : LinShape) (D : EvalAt) : Bool := (sitsL cs Sh D).all (·.2)

/-- The test says yes exactly where the five hold. -/
theorem sitsB_iff (cs : Codes) (Sh : LinShape) (D : EvalAt) :
    sitsB cs Sh D = true ↔ SitsPlain cs Sh D := by
  simp only [sitsB, sitsL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.codes, h.shape, h.lay, h.lengths, h.code⟩⟩

end VerifiableInference.Desc.K13.Law

