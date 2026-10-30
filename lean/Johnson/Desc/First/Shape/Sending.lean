-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Sending.lean: THE SENDING (the kind K1) AT THE FIRST CHAIN's STATE: the
two small laws that tie SendCore.lean's laws on the one shape of statement, book and roots to the
first chain's shape (Chain.lean). By rfl.

  `core_stateOf`: K1.stateOf reads the component core. `chainSh_laid`: K1.laid writes it, and
    nothing is owed behind.

Limits. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.First.Shape.SendCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh OrcSh coreSh orcSh)

variable {L : Type}

/-- The state's core is its statement's part's. -/
theorem core_stateOf (s : S) (l : L) : coreSh (coreOf (K1.stateOf s l)) = (chainSh s).core := rfl

/-- Laying a record back turns the core, and nothing is owed behind it. -/
theorem chainSh_laid (s : S) (d : DState L) :
    chainSh (K1.laid s d) = ((chainSh s).setCore (coreSh (coreOf d))).setRowsOwed none := rfl

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.core_stateOf
#print axioms VerifiableInference.Desc.First.Shape.chainSh_laid
