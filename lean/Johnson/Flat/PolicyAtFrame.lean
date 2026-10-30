-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/PolicyAtFrame.lean: the meaning FOR THE CLAIM "the output meets the acceptance policy"
(`CompilerSoundnessConditionStatements.soundFor`, Johnson/Top/InnerCompiledVerifier.lean; `Policy.MeetsPolicy`,
Policy/Front/MeetsPolicy.lean) at the full-size input whose rounds' data and two decisions are
letters (Johnson/Flat/TwoSizesAt.lean), where the claims are those at a table pp of scales and
policy (`claimsReqAt`, Johnson/Top/H/TargetAtPolicy.lean).

Three definitions, five theorems, one check by rfl.
  `phiAt valid M`: the weights, at valid settings, of the index that the matrix M holds; at a matrix
    that holds none: the all-zero weights (`Policy.zeroWeights`, Policy/Front/TrueUnder.lean).
    `phiAt_of_holds`: within the reference's shape, at a matrix that holds i they are i's.
  `claimPolicy pp lawful M prompt output`: `Policy.MeetsPolicy` at the settings of pp's scales, at
    pp's policy and at `phiAt … M`.
  `meaningPolicyOfFull`: `CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtFullSize T) (claimPolicy pp lawful)`, spelled out,
    at A := claimsReqAt … N pp, at a lawful pp and a shape within the reference's, if T's builder is
    `Flat.buildReq`. Of T it reads the builder alone. By `sound_ledger`
    (Johnson/Road/Lane5SoundLedger.lean).
  `carriesPolicy`: along an equation pp' = pp, the claim at pp' gives `Policy.MeetsPolicy` at pp, at
    any proof that the settings are valid.
  `ppAtFiles policy KL`: the table that the reader `settingsAtRef` (Johnson/Flat/SettingsRead.lean)
    returns; the reference's where it refuses (at exact match); there `InScope` (Ladder.lean) is
    false. `ppAtFiles_of_read`. `lawful_ppAtFiles`: it is lawful at all files.

A choice stands in `phiAt`: the index that a matrix holds is taken by `Exists.choose`
(`Flat.indexOf`, Johnson/Flat/LedgerClaim.lean). Within the reference's shape a matrix holds one
index at most (`Flat.holds_unique`; of the choice: `Flat.indexOf_eq`): `meaningPolicyOfFull` spends
that.

Limits. GENERAL IN THE FRAME'S LETTERS: NO VALUE OF THIS FRAME HAS RUN ON A REAL PROOF. That a
description's decision that runs on real proofs is of this frame's make is inferred, not held. NO T
IS LAID in this library: that the letters' type has a member is not shown, and if it has none the
theorem says nothing. THE MEANING IS MOVED, NOT SHRUNK: what proofSound then asks of the proof
file's protocol is the claim `Flat.RelLAt pp` at the requests of `Flat.Req`, at that table's own
scales and policy, and what keySound asks of the key file's protocol is that a decoded matrix holds
a well-formed table of digits. Nothing of either is proved here. N and pp are letters: nothing here
ties N to the committed matrix's numbers; `ppAtFiles` ties a table to two files, and no theorem here
lays it for pp.
AT A MATRIX THAT HOLDS NO INDEX THE CLAIM IS NEARLY FREE: `phiAt` gives the all-zero weights there,
and under these every output meets every policy with 257 ≤ theta and 257 ≤ C, within the side
conditions of `Policy.meetsPolicy_zeroWeights` (Policy/Front/TrueUnder.lean). `meaningPolicyOfFull`
never stands there: the relation's first clause is that the matrix holds an index. An extractor that
is followed by `phiAt` gives weights also at a matrix that holds none: that it returns no such
matrix is not shown here.
What a policy rules out depends on the weights' scores as well as on its three
numbers; at a policy that leaves every counted token free the claim says nothing of them (see
`Policy.MeetsPolicy`). The types of P and T hold the three files of this make, whose entry file's
decision is a run of the verifier program's own routine (the head of Johnson/Flat/TwoSizesAt.lean);
no proof here reads it.
The reader `settingsAtRef` is the goals' own (`readFiles`, Ladder.lean). Its scan of the parameter
file (`polScan`, OnBytes/Model/Config.lean) is the library's text of the programs' scan: `ppAtFiles`
and its two theorems stand over that text.
The request stays at the reference sizes. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TwoSizesAt
import Johnson.Top.H.TargetAtPolicy
import Johnson.Road.Lane5SoundLedger
import Johnson.Flat.SettingsRead

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
open Inst.Model (ScalesAndPolicy Lawful ppRef lawful_ref)

/-- The weights, at valid settings, of the index that the matrix holds; at a matrix that holds no
index: the all-zero weights (`Policy.zeroWeights`, Policy/Front/TrueUnder.lean, by unfolding). -/
def phiAt {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    {rows cols : ℕ} (M : Fin rows → Fin cols → Flat.GE) : ModelWeights settings :=
  weightsOfIndex valid ((Flat.indexOf M).getD (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero))

/-- Within the reference's shape, at a matrix that holds i they are i's weights. -/
theorem phiAt_of_holds {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) {rows cols : ℕ} (hr : rows ≤ hRef)
    (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → Flat.GE} {i : Cm.Idx} (h : Flat.Holds M i) :
    phiAt valid M = weightsOfIndex valid i := by
  unfold phiAt
  rw [Flat.indexOf_eq hr hc h]
  rfl

/-- The claim on a decoded matrix, at a lawful table of scales and policy: the output meets the
table's policy, at the settings of the table's scales and at `phiAt` of the matrix: the weights that
it holds, or the all-zero weights if it holds no index. -/
def claimPolicy (pp : ScalesAndPolicy) (lawful : Lawful pp) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) : Prop :=
  Policy.MeetsPolicy (settingsOf (Cm.Scales.of pp)) pp.pol
    (phiAt (settingsAreValid_settingsOf (Cm.lawful_of lawful)) M) prompt output

section
variable (N : MatrixNums) (pp : ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : Flat.Req × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : Flat.Req → Flat.Req) (salt K : ℕ)
  (P : (threeProtocolsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E) DK DP runK runP rK rP
    depthReq early salt).Provers)

/-- **The meaning for the claim `claimPolicy pp lawful`**, at every data of rounds and every two
decisions: `CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtFullSize T) (claimPolicy pp lawful)`, spelled out. Under: a
lawful table of scales and policy; two bounds on the matrix's shape; T's builder is
`Flat.buildReq`. -/
theorem meaningPolicyOfFull (lawful : Lawful pp) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP rK rP
      depthReq early salt K P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) :
    ∀ i (x' : List Token × List Token) a x, T.build x' a = some x →
      (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize T).Rno i x w) → claimPolicy pp lawful i x'.1 x'.2 := by
  rintro i x' a x hbx ⟨_, hw⟩
  obtain ⟨j, hj, tr, ht⟩ := hw.2
  unfold claimPolicy
  rw [phiAt_of_holds _ hr hc hj]
  exact OnBytes.Road.L5.sound_ledger (Cm.lawful_of lawful) _ rfl lawful.polOK j x' a x.1
    (Flat.buildReq_some ((hb x' a).symm.trans hbx)) ⟨tr, ht⟩

/-- The sentence is the name `CompilerSoundnessConditionStatements.soundFor`. -/
example (lawful : Lawful pp)
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize (claimsReqAt (frS.toDecR frZ 402653181) N pp) E DK DP runK runP rK rP
      depthReq early salt K P) :
    CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtFullSize T) (claimPolicy pp lawful) =
      (∀ i (x' : List Token × List Token) a x, T.build x' a = some x →
        (∃ w, (soundnessAnalysisDataWithFixedLinkAtFullSize T).Rno i x w) → claimPolicy pp lawful i x'.1 x'.2) := rfl

end

/-- Along an equation of tables the claim gives `Policy.MeetsPolicy` at the other table, at any
proof that its settings are valid. -/
theorem carriesPolicy {pp pp' : ScalesAndPolicy} (e : pp' = pp) (lawful' : Lawful pp')
    (valid : settingsAreValid (settingsOf (Cm.Scales.of pp)) = true) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) (prompt output : List Token) :
    claimPolicy pp' lawful' M prompt output →
      Policy.MeetsPolicy (settingsOf (Cm.Scales.of pp)) pp.pol (phiAt valid M) prompt output := by
  subst e
  exact id

/-- The table of scales and policy that the reader returns at two files; the reference's where it
refuses. -/
def ppAtFiles (policy KL : ByteArray) : ScalesAndPolicy :=
  match settingsAtRef policy KL with
  | .ok pp => pp
  | .error _ => ppRef

/-- Where the reader returns a table, it is that table. -/
theorem ppAtFiles_of_read {policy KL : ByteArray} {pp : ScalesAndPolicy} (h : settingsAtRef policy KL = .ok pp) :
    ppAtFiles policy KL = pp := by
  unfold ppAtFiles
  rw [h]

/-- It is lawful at all files. -/
theorem lawful_ppAtFiles (policy KL : ByteArray) : Lawful (ppAtFiles policy KL) := by
  unfold ppAtFiles
  split
  · exact settingsAtRef_lawful ‹_›
  · exact lawful_ref

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.phiAt_of_holds
#print axioms VerifiableInference.OnPublicFiles.meaningPolicyOfFull
#print axioms VerifiableInference.OnPublicFiles.carriesPolicy
#print axioms VerifiableInference.OnPublicFiles.ppAtFiles_of_read
#print axioms VerifiableInference.OnPublicFiles.lawful_ppAtFiles
