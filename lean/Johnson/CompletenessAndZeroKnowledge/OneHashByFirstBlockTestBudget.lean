-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestBudget.lean: THE HONEST SIDE OF slotSystemF IN HASH QUERIES.

factorsAt_of_pass: the premise of the third exit from the coding's first block and the test on first
blocks. slotSystemF_withinBudget: the count at letters. commitC_written, proveC_written: at the written
data and the search limits 2 ^ (work + 6), with M + 1 copies, the numerals. slotSystemF_two_pow_48: so at
up to 81 copies the honest side of slotSystemF stays within 2 ^ 48 hash queries on every path.
Upper bounds on every path. Nothing here is a goal.
-/
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestFront
import Johnson.CompletenessAndZeroKnowledge.CommitFactors
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestCount
import Johnson.CompletenessAndZeroKnowledge.PassAtBuilt
import Johnson.Goal.Conditions.HonestNumber

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead VerifierAndGoals
open VerifiableInference.AtEveryRequest (WithinBudget)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Read
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {hK : 0 < R.queryLayout.K} {pass : Pass 256 (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)}

/-- **The premise of the third exit**, from the coding's first block and the test on first blocks. -/
theorem factorsAt_of_pass (F : ∀ d, FirstIs hK (T.m d)) (H : ∀ d, PassFits R.queryLayout (T.Sd d) hK pass) :
    FactorsAt T h fun _ => moreP pass where
  C := fun d i => factorsF_of hK pass (T.m d) (F d) (factors_commitW (T.cA d) (h d) (H d) i)
  P := fun d k b => factorsF_of hK pass (T.m d) (F d) (factors_proveW (T.at d) (h d) (H d) k b)

variable {T h}
variable {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
  (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)
  (more : (d : T.D) → More (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) 256)

theorem queryBound_frontKFC (q₀ C : ℕ) (hq : T.Pub.QueryBound q₀)
    (hC : ∀ d i, ((commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i).overOneF (T.m d) (more d)).QueryBound C)
    (w : J) : ((committerAndProverOverOneHash T h more idx x₀ κ ϖ Vf).C w).QueryBound (q₀ + C + 1) := by
  have hG : ((readToldF T h more).C (idx w)).QueryBound (q₀ + (C + 0 + 0)) :=
    hq.bind fun d =>
      OComp.QueryBound.bind
        (OComp.QueryBound.bind (hC d (idx w)) fun _ => trivial)
        fun _ => trivial
  exact ZKCP.OComp.QueryBound.bind _ 1
    (fun keys => ZKCP.OComp.QueryBound.mapO _ _ 1 (ZKCP.queryBound_keyDigest _ _)) _ _
    (queryBound_oneOf_C (readToldF T h more) (idx w) hG)

theorem queryBound_frontKFP (C : ℕ)
    (hP : ∀ d isk b, ((proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk b).overOneF (T.m d) (more d)).QueryBound C)
    (isk : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (x' : List Token × List Token) :
    ((committerAndProverOverOneHash T h more idx x₀ κ ϖ Vf).P isk x' ()).QueryBound C := by
  have hG : ((readToldF T h more).P isk.2 [(instOf R x₀ x', ())]).QueryBound C :=
    hP isk.2.1 isk.2.2 [(instOf R x₀ x', ())]
  exact ZKCP.OComp.QueryBound.mapO _ _ _
    (queryBound_oneOf_P (readToldF T h more) isk.2 (instOf R x₀ x') () hG)

end Read

section Slot
variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
  (encF : TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- **The honest side of slotSystemF stays within slotBudgetFine.** NC and NP count hash queries
at the third exit: a failed try one, a whole answer K + 1. -/
theorem slotSystemF_withinBudget {hK : 0 < (D.input Z c₀ m₀).queryLayout.K}
    {pass : Pass 256 (typedOracleCarrier (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
      (D.input Z c₀ m₀).linkRoundSplits)} {q₀ NC NP : ℕ} (hq : T.Pub.QueryBound q₀)
    (F : ∀ d, FirstIs hK (T.m d)) (H : ∀ d, PassFits (D.input Z c₀ m₀).queryLayout (T.Sd d) hK pass)
    (hp : ∀ d, PathsFit (D.input Z c₀ m₀).queryLayout (h d))
    (hC : ∀ d, commitC (D.input Z c₀ m₀).queryLayout (h d) ≤ NC)
    (hP : ∀ d, proveC (D.input Z c₀ m₀).queryLayout (h d) ≤ NP) :
    WithinBudget (slotSystemF D Z c₀ m₀ T h (fun _ => moreP pass) s idx x₀ Form parse encF bound)
      (slotBudgetFine q₀ NC NP) := by
  have hC' : ∀ w, ((frontIdF D Z c₀ m₀ T h (fun _ => moreP pass) s idx x₀ Form parse encF).C
      w).QueryBound (q₀ + NC + 1) := fun w =>
    queryBound_frontKFC _ _ _ _ _ _ q₀ NC hq
      (fun d i => (hashCalls_commitW (T.m d) (F d) (H d) (hp d) i).mono (hC d)) w
  have hP' : ∀ isk x', ((frontIdF D Z c₀ m₀ T h (fun _ => moreP pass) s idx x₀ Form parse encF).P
      isk x' ()).QueryBound NP := fun isk x' =>
    queryBound_frontKFP _ _ _ _ _ _ NP
      (fun d isk b => (hashCalls_proveW (T.m d) (F d) (H d) (hp d) isk b).mono (hP d)) isk x'
  refine ⟨0, q₀ + NC + 1, (q₀ + NC + 1) + NP, le_of_eq ?_, fun _ => trivial,
    fun w coins => ?_, fun w coins prompt output => ?_⟩
  · unfold slotBudgetFine
    ring
  · exact queryBound_deterministicOf _ _
      (ZKCP.OComp.QueryBound.mapO _ _ _ (ZKCP.OComp.QueryBound.withCoins _ _ _ (hC' w)))
  · exact (RandomizedAlgorithm.queryBound_ofUpload _ _).2
      (ZKCP.queryBound_P_coinsFirst _ bound w coins (prompt, output) () _ _ (hC' w)
        fun isk => hP' isk _)

end Slot

end OnBytes.FrontRoad

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Johnson.G (writtenKFull writtenPFull fr_a)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))
  (eK : S.DK = writtenKFull) (eP : S.DP = writtenPFull)
  (h : HonestSide 256 (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).LeafBody
    (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits)
include eK eP

theorem tabW_written : tabW (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout = 8589982768 := by
  have hd : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depth = 32 := fr_a
  have hk : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.K = 24087 :=
    congrArg (· + 1) (wireBlocksButOne_atWrittenRounds S eK eP)
  unfold tabW
  rw [hd, hk]
  norm_num

/-- **The committer at the third exit, at the written data and limits.** -/
theorem commitC_written (hT : h.capT = capT S) (hL : h.capL = capL)
    (dT : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depthReqT = 0)
    (dL : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depthReqL = 0) :
    commitC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout h =
      (h.M + 2) * 8589982768 + 5223661230411 + (h.M + 1) * 1649307525166 := by
  rw [commitC_eq, tabW_written S c₀ m₀ eK eP, hT, dT, chainT_written S c₀ m₀ eK eP]
  unfold linkC
  rw [hL, dL, chainL_written S c₀ m₀ eK eP]

/-- **The prover at the third exit, at the written data and limits.** -/
theorem proveC_written (hB : h.capB = capB S)
    (dB : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depthReq = 6) :
    proveC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout h = 177887278538 := by
  unfold proveC
  rw [hB, dB, chainB_written S c₀ m₀ eK eP]

/-- **At up to 81 copies the count is within 2 ^ 48.** -/
theorem budget_written (hT : h.capT = capT S) (hL : h.capL = capL) (hB : h.capB = capB S)
    (dT : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depthReqT = 0)
    (dL : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depthReqL = 0)
    (dB : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout.depthReq = 6) :
    slotBudgetFine 8 (commitC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout h)
        (proveC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout h) ≤ 2 ^ 48 ↔ h.M + 1 ≤ 81 := by
  rw [commitC_written S c₀ m₀ eK eP h hT hL dT dL, proveC_written S c₀ m₀ eK eP h hB dB]
  exact copies_within_two_pow_48 h.M

end FlashProve

#print axioms OnBytes.FrontRoad.factorsAt_of_pass
#print axioms OnBytes.FrontRoad.slotSystemF_withinBudget
#print axioms FlashProve.commitC_written
#print axioms FlashProve.proveC_written
#print axioms FlashProve.budget_written
