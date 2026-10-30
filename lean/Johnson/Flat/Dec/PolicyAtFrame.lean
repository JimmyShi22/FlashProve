-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/PolicyAtFrame.lean: the meaning FOR THE CLAIM "the decoded matrix holds an index, and
the output meets the acceptance policy at that index's weights" (`CompilerSoundnessConditionStatements.soundFor`,
Johnson/Top/InnerCompiledVerifier.lean; `Policy.MeetsPolicy`, Policy/Front/MeetsPolicy.lean) at the full-size frame whose
entry file's rounds' data, stored openings and decision are letters too (Johnson/Flat/Dec/), where the
claims are those at a table pp of scales and policy (`claimsReqAt`, Johnson/Top/H/TargetAtPolicy.lean).
THE SIBLING OF Johnson/Flat/PolicyAtFrame.lean, IN THE FORM WITH AN EXTRACTOR THAT CAN SAY none.

Why that form. `phiAt` (the sibling) gives the all-zero weights at a matrix that holds no index, and under
these every output meets every policy with 257 ≤ theta and 257 ≤ C: the claim `claimPolicy` is nearly free
there, and an extractor followed by a total map never says none. Here the map goes into Option and
the claim says that an index is held.

Two definitions, three theorems, one check by rfl.
  `phiO valid M`: the weights, at valid settings, of the index that the matrix holds; none where it holds
    none (`phiO_none`).
  `claimPolicyO pp lawful M prompt output`: there is an index j that M holds (`Flat.indexOf M = some j`)
    with `Policy.MeetsPolicy` at the settings of pp's scales, at pp's policy and at j's weights.
  `meaningPolicyOD`: `CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtFullSize T) (claimPolicyO pp lawful)`, spelled out, at a lawful
    pp and a shape within the reference's, if T's builder is `Flat.buildReq`. Of T it reads the builder
    alone; of the three decisions and the three files' data nothing.
  `carriesPolicyO`: along an equation pp' = pp: where the claim holds at pp', `phiO` says some, with
    `Policy.MeetsPolicy` at pp at what it says.
The four texts follow those of Johnson/PV/DescribeO.lean; here they stand at the frame, with three
letters more.

Every "there is", walked. `claimPolicyO`'s j: pinned by `Flat.indexOf M = some j`: one value at most.
`carriesPolicyO`'s w: pinned by `phiO valid M = some w`. The meaning's premise "there is a witness": given.
THE TWO SILLY MEMBERS: the statements read no decision: they hold at a verifier that says yes to all and
at one that says no to all: THE MEANING IS MOVED, NOT SHRUNK: what proofSound then asks of the proof
file's protocol is `Flat.RelLAt pp` at that table's own scales and policy. At a builder that refuses all
the meaning holds for nothing: hb shuts that case.

Limits: those of the sibling's head, but for what it says of `phiAt` and of the entry's decision. NO VALUE OF
THIS FRAME HAS RUN ON A REAL PROOF. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.PolicyAtFrame
import Johnson.Flat.Dec.TwoSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model.Layout (kRef hRef)
open Inst.Model (ScalesAndPolicy Lawful)

/-- The weights, at valid settings, of the index that the matrix holds; NONE where it holds none. -/
def phiO {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    {rows cols : ℕ} (M : Fin rows → Fin cols → Flat.GE) : Option (ModelWeights settings) :=
  (Flat.indexOf M).map (weightsOfIndex valid)

/-- At a matrix that holds no index it says none. -/
theorem phiO_none {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) {rows cols : ℕ} (M : Fin rows → Fin cols → Flat.GE)
    (h : ¬ Flat.InRange M) : phiO valid M = none := by
  unfold phiO Flat.indexOf
  rw [dif_neg h]
  rfl

/-- The claim on a decoded matrix: IT HOLDS AN INDEX, and the output meets the table's policy at that
index's weights. -/
def claimPolicyO (pp : ScalesAndPolicy) (lawful : Lawful pp) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) : Prop :=
  ∃ j, Flat.indexOf M = some j ∧
    Policy.MeetsPolicy (settingsOf (Cm.Scales.of pp)) pp.pol
      (weightsOfIndex (settingsAreValid_settingsOf (Cm.lawful_of lawful)) j) prompt output

section
variable (N : MatrixNums) (pp : ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : Flat.Req × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : Flat.Req → Flat.Req) (salt K : ℕ)
  (P : (threeProtocolsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E) DK DP runK runP ds xs
    dec rK rP depthReq early salt).Provers)

/-- **The meaning for the claim `claimPolicyO pp lawful`**, at every data of rounds and every three
decisions. Under: a lawful table of scales and policy; two bounds on the matrix's shape; T's builder
is `Flat.buildReq`. -/
theorem meaningPolicyOD (lawful : Lawful pp) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP ds xs dec
      rK rP depthReq early salt K P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) :
    ∀ i (x' : List Token × List Token) a x, T.build x' a = some x →
      (∃ w, (soundnessAnalysisDataAtFullSize T).Rno i x w) → claimPolicyO pp lawful i x'.1 x'.2 := by
  rintro i x' a x hbx ⟨_, hw⟩
  obtain ⟨j, hj, tr, ht⟩ := hw.2
  exact ⟨j, Flat.indexOf_eq hr hc hj,
    OnBytes.Road.L5.sound_ledger (Cm.lawful_of lawful) _ rfl lawful.polOK j x' a x.1
      (Flat.buildReq_some ((hb x' a).symm.trans hbx)) ⟨tr, ht⟩⟩

/-- The sentence is the library's name `CompilerSoundnessConditionStatements.soundFor`. -/
example (lawful : Lawful pp)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP ds xs dec
      rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtFullSize T) (claimPolicyO pp lawful) =
      (∀ i (x' : List Token × List Token) a x, T.build x' a = some x →
        (∃ w, (soundnessAnalysisDataAtFullSize T).Rno i x w) → claimPolicyO pp lawful i x'.1 x'.2) := rfl

end

/-- Where the claim holds, `phiO` says some, with the goal's sentence at what it says. -/
theorem carriesPolicyO {pp pp' : ScalesAndPolicy} (e : pp' = pp) (lawful' : Lawful pp')
    (valid : settingsAreValid (settingsOf (Cm.Scales.of pp)) = true) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) :
    claimPolicyO pp' lawful' M prompt output →
      ∃ w, phiO valid M = some w ∧
        Policy.MeetsPolicy (settingsOf (Cm.Scales.of pp)) pp.pol w prompt output := by
  subst e
  rintro ⟨j, hj, hm⟩
  exact ⟨_, by unfold phiO; rw [hj]; rfl, hm⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.phiO_none
#print axioms VerifiableInference.OnPublicFiles.meaningPolicyOD
#print axioms VerifiableInference.OnPublicFiles.carriesPolicyO
