-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/TieB.lean: no soundness is claimed.
K1.Tie (Johnson/Desc/K1/Law/Port2.lean: one OOD answer · the codes' lengths · the shape is lawful at the codes · the pads fit) as a test with code, so that a file of evaluations can evaluate it at the plan's shapes and its accept is the premise by Lean.
  tieB cs s · tie_iff : tieB cs s = true ↔ K1.Tie cs s
-/
import Johnson.Desc.K1.Law.Port2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Slice
open VerifiableInference.Desc

def tieB (cs : Codes) (s : OracleShape) : Bool :=
  decide (s.answers = 1) && cs.lengthsOk && Blk.shapeOk cs s && (K1.Msg.of cs s).padFits

theorem tie_iff (cs : Codes) (s : OracleShape) : tieB cs s = true ↔ K1.Tie cs s := by
  unfold tieB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.one, h.lengths⟩, h.shape⟩, h.fits⟩⟩

end ToldDesc

#print axioms ToldDesc.tie_iff
