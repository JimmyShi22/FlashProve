-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WPublicAtHead.lean: public numbers under the head, as the test's tie at the last chain
spends them.

  codes_at_head    one table of codes: the plan's, the two written senders', the closed shape's
  rounds_at_head   the rounds in front of numbers 2 and 356

Limits.
- The full size and the format's second hash function alone.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.WNumbersAtHead
import AtFullSide.K13.WFillAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit
import Johnson.ToldDescR.RcLastCode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc.K1 (parGF parWF qAt)
open ProofFile.Honest.K12.AtFile (narrowW)
open P5J (AtMg AtMgA TS)

/-- The written senders' codes and the closed shape's. An evaluation in Lean's kernel. -/
theorem codes_written : parGF.codes = H2K.Member.codesFull ∧ parWF.codes = H2K.Member.codesFull ∧
    narrowW.st.codes = H2K.Member.codesFull := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}

/-- **Under the head one table of codes.** -/
theorem codes_at_head (h : AtMg o Z D r Zp Np cF) :
    (ToldDesc.p14At Zp).codes = H2K.Member.codesFull ∧ (qAt Zp Np).codes = H2K.Member.codesFull := by
  obtain ⟨x, -, Wr⟩ := ProofFile.Honest.K12.Light.written_at_head h
  refine ⟨?_, ?_⟩
  · show Zp.p.chains.made.sized.proof.codes = _
    exact Wr.codes
  · rw [ProofFile.Honest.K12.Light.qAt_written Wr Np]
    rfl

variable {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The rounds in front of numbers 2 and 356.** -/
theorem rounds_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ProofFile.Honest.roundsTo cF.blocksInOrder 2 ≤ 48290 ∧ ProofFile.Honest.roundsTo cF.blocksInOrder 356 = 48290 := by
  have e : ProofFile.Honest.roundsTo cF.blocksInOrder 356 = 48290 :=
    (AtFullSide.K13.k13_wHeard_is_rounds h).symm.trans (AtFullSide.K13.k13_wHeard_at_head h)
  exact ⟨e ▸ ProofFile.Honest.roundsTo_mono _ _ _ (by decide), e⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.codes_written
#print axioms AtFullSide.K12.codes_at_head
#print axioms AtFullSide.K12.rounds_at_head
