-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/DoorPublic.lean: THE TWO CLAUSES OF THE SECOND CHAIN's START ON PUBLIC VALUES ALONE,
UNDER THE HEAD: the codes' lengths, the shape lawful at the codes, and that the shape does not split the row
(Dot): from the description's test on its own blocks, at the second chain's first block.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.PlanPasses
import Johnson.Desc.Plain.StartThreeAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Third (plainArm)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **hl and plainArm.** -/
theorem door_public (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ((ProofFile.pAt Zp).codes.lengthsOk && linOk (ProofFile.pAt Zp).codes (ProofFile.pAt Zp).S) = true ∧
      plainArm (ProofFile.pAt Zp).S = true := by
  have hm : ∃ b ∈ (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, b.planOk = true →
      ((ProofFile.pAt Zp).codes.lengthsOk && linOk (ProofFile.pAt Zp).codes (ProofFile.pAt Zp).S &&
        plainArm (ProofFile.pAt Zp).S) = true :=
    ⟨_, List.mem_cons_self .., fun h => by
      have h1 : (F0T OnBytes.secondHashFunction Zp Np cF).second.first.planOk = true :=
        (Bool.and_eq_true_iff.1 h).1
      have h2 : (((ProofFile.pAt Zp).codes.lengthsOk && linOk (ProofFile.pAt Zp).codes (ProofFile.pAt Zp).S &&
          plainArm (ProofFile.pAt Zp).S) && true && true) = true := h1
      simpa only [Bool.and_true] using h2⟩
  obtain ⟨b, hb, hk⟩ := hm
  have t := hk ((VerifiableInference.Desc.Keeps.planOk_blocks _ h.laid.planOk).2.2 b hb)
  exact Bool.and_eq_true_iff.1 t

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.door_public
