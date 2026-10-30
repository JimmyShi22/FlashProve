-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestTies.lean: WHAT TIES compile, BY THE THIRD EXIT, TO WHAT STANDS AT THE PLAIN EXIT.

1.  The supports: whatever the committer and the prover by the third exit can return under a hash
    function, those by the plain exit can, and the other way round: a statement on readOne's supports
    speaks of readOneF's.
2.  The budget: at theSettings with the chosen search limits the honest side of compile at flashProveAtFiles stays
    within honestQueryBudget. No premise of the road is spent; it is the first conjunct of FinalComplete
    and the second clause of RepliesFit at that honest part.
3.  What is claimed of the protocol is nothing: this file proves neither completeness nor zero
    knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.FinalRoadProof
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestAtSettings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace OnBytes.FrontRoad
open VerifiableInference.OnPublicFiles OnBytes.Prover OnBytes.WholeKey

variable {R : InnerCompilerInput} {T : LayoutsByPublicReading R} {h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits}
  {more : (d : T.D) → Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 R.queryLayout.K
    (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) 256}

/-- The committer's supports at the two exits are one. -/
theorem support_readOneF_C (F : FactorsAt T h more) (f : ZKCP.Oracle 256) (i : R.Index) :
    (((readOneF T h more).C i).run f).support = (((readOne T h).C i).run f).support := by
  rw [run_readOne_C F f i]

/-- The prover's supports at the two exits are one. -/
theorem support_readOneF_P (F : FactorsAt T h more) (f : ZKCP.Oracle 256)
    (k : T.D × OnBytes.WholeKey.Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance) (u : Unit) :
    (((readOneF T h more).P k x u).run f).support = (((readOne T h).P k x u).run f).support := by
  rw [run_readOne_P F f k x u]

end OnBytes.FrontRoad

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.AtEveryRequest (WithinBudget)
open IntegerTransformer (Settings)

/-- **The budget of the final statement, at compile.** -/
theorem compile_withinBudget (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (starts : SaltStarts provers) (slotSalts : RequestLeafSaltLayout) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (h : starts.LengthsFit 256 256)
    (slots : ∀ reading, slotSalts.Fit (flashLayout files settings fallbackInstance reading)) :
    WithinBudget (compile (flashProveAtFiles files settings
        (theHonestPartOf files settings fallbackInstance provers starts (writtenLimits files)
          slotSalts)))
      honestQueryBudget := by
  rw [compile_flashProve_eq]
  exact theSettings_withinBudgetF files settings fallbackInstance provers starts slotSalts scope live
    h slots _

end VerifiableInference.Compilation

#print axioms OnBytes.FrontRoad.support_readOneF_C
#print axioms OnBytes.FrontRoad.support_readOneF_P
#print axioms VerifiableInference.Compilation.compile_withinBudget
