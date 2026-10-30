-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatedGuards.lean: a block with a refusal at a marked record behind another
block's decision (`Guards c b`, Johnson/Desc/First/K8/LawSeated.lean) says yes only where that
block does (`Block.UnderR`, Johnson/Desc/Sound/SeatGuardChain.lean); so does the same block behind a
driver's guard. Two statements with their proofs. With them the laws that pass along `UnderR`
(Johnson/Desc/Sound/SeatedPiece.lean) reach a block as a chain holds it.

What is not claimed. That a given chain lays such a block. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K8.LawSeated
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

variable {Cl : Type}

theorem Guards.underR {c b : Block S Cl} (h : Guards c b) : c.UnderR b :=
  ⟨h.1, fun _ _ _ _ hd => h.yes hd⟩

/-- Behind a driver's guard too. -/
theorem Guards.guarded_underR {c b : Block S Cl} (h : Guards c b) (same : S → S → Bool)
    (but : Place → Bool) : (c.guarded same but).UnderR b :=
  (VerifiableInference.Desc.guarded_underR same but c).trans h.underR

end VerifiableInference.Desc.First.K8
