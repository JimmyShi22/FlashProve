-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/ProofFullPins.lean: WHERE THE PROOF FILE's VALUE IS LAID, WHAT THE ENTRY TESTS'
SECOND PART (ProofAsks.lean)
GIVES. A law file.

  laidPOf_pins         where the value is laid: the IOP as written F and the public plan Z are made,
                       by the
                       very functions at the very arguments; the lookups' three tests accept at Z;
                       and if
                       Z stands at the full size's key, both pins' bare tests accept: `madeRow Z`,
                       `cutRow F Z`
  laidPOf_pins_scope   **in the goals' scope the key is the full size's: so there both pins' tests
                       accept**

What these tests' yes gives is their files' to say (PlanWritten/MadeTestLaws.lean,
Goal/Numbers/MadeInScope.lean; PlanWritten/CutTestLaws.lean; First/Look/K3AsksDoorLaw.lean).
Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Laid.ProofAsksLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open OnBytes.Maker
open VerifiableInference

variable {o : ProofFile.SecondHashFunctionArgument} {D : WholeD} {r : RunPF}

/-- **Where the value is laid, the entry tests' rows accept at the maker's own F and Z.** -/
theorem laidPOf_pins {pol lay KL : ByteArray} (h : proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F Z, ProofFile.onlineDescription o pol lay KL = .ok F ∧ ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      Desc.K3Asks.digEntry Z = true ∧ Desc.K3Asks.readsEntry Z = true ∧
      Desc.K3Asks.headEntry Z = true ∧
      (Desc.Door.atFullKey Z = true →
        PlanWritten.madeRow Z = true ∧ PlanWritten.cutRow F Z = true) := by
  obtain ⟨F, hF, -, -, hs, -⟩ := laidPOf_ok h
  obtain ⟨Z, hM, -⟩ := Desc.Door.every_yes (_root_.LPFD.asks_dig hs)
  have hZ := Desc.Door.planOf_some.1 hM
  obtain ⟨a, b, c⟩ := _root_.LPFD.asks_rest hs hZ
  exact ⟨F, Z, hF, hZ, a, b, c, fun hk => _root_.LPFD.asks_pins hs hZ hk⟩

end LPFD.Full

#print axioms LPFD.Full.laidPOf_pins
