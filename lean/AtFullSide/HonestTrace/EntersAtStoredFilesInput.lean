-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/EntersAtStoredFilesInput.lean

It states no goal. No property of the protocol is claimed.

THE INPUT OF A RUN AT THE BASE RETURN: a rider on AtFullSide/HonestTrace/EntersAtStoredFiles.lean. At a served
request ("AtPublicFiles.AtFiles.ServedRequest") the base return's prover says yes to the index, has a trace at every
written instance of the request, and the index that the matrix holds serves the request at the return's own
public part: the form of the premise Sv of "enters_firstThread". That it is that form is not guarded
by Lean here (Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean). No call feeds this file's
sentence into that theorem as Sv: where that theorem is called (EntersItemsFirstChain.lean) its Sv
is made from "ReadyInput".

Main theorems:
* "servedInput_atBaseReturn": where the public files are in scope, are read and pass "protocolDataWellFormed", at every return
  A of the maker at the base filling and every head H at it: for every matrix M and typed request x' with
  ServedRequest: at every record the range test says yes and the trace is there; and some index i that M holds
  has ServesAt (P5J.At.X A.Z) i x'.val.
* THE FORM TO JOIN WITH OTHER LAWS: "servedInput_atStoredFiles": at the stored full-size files "VerifierAndGoals.storedPublicFiles", at a GIVEN
  return A, a GIVEN head H at it and a GIVEN served request (M, x'): all of the above, hok and "no mark" at its written
  instances. No other premise.
* THE ONE EXISTENCE ON THE REQUEST's SIDE: "servedRequest_atStoredFiles": at "VerifierAndGoals.storedPublicFiles" some request is served.
* "inputAroundTheStart_atStoredFiles": these with "baseReturn_atStoredFiles" under "there are": NO PREMISE. A corollary:
  NOT TO BE JOINED with another "there are".

Limits.
* EVERYTHING HERE STANDS AT A RETURN OF THE BASE FILLING. The honest prover's term (E2E/TheHonestProver.lean) is made
  at that filling read through the coins' map ("OnlineProverParts.through id (tableCoins files) …"): another type of coins and
  another return. So these are not the premises of "enters_firstThread" at the term's own return: nothing here
  crosses.
* Two tests of "ready" alone: hR, that "ready" returns, is not paid here. hReq and Ti are other files'.
* The served request's weights are made up ("Meaning.served_met").
* The limits of EntersAtStoredFiles.lean stand.
* "VerifierAndGoals.storedPublicFiles" is a term written in the library, the stored full-size example of the three public
  files: no Lean ties it to files in a folder.
* "theLive_zFull" (AtFullSide/Top/LiveAtFull.lean) is a closed fact by evaluation in Lean's kernel:
  no independent checker has replayed it; only a build of the side library shows a break in it; a
  yes of "protocolDataWellFormed" is no sign that the verifier accepts any proof.
* Nothing on completeness, soundness, hiding or any other property of the protocol.
-/
import AtFullSide.HonestTrace.EntersAtStoredFiles
import Johnson.HonestTrace.Joint.JointMeetsPlug
import Johnson.HonestTrace.Joint.JointMeetsBServed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.HonestTrace.EntersAtStoredFiles

open ProofFile.Honest (onlineProverFromPublicFiles openHonest)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers ScriptIsTheSenders)
open ProofFile.Honest.K1 (firstParts)
open AtPublicFiles.AtFiles (FullSizeMatrix ServedRequest)
open LPFD.Full (XF instanceAsPlainRecord)
open OnBytes.Flat (RecFull)
open FlashProve (committerCoinCountLessOne)
open VerifiableInference.OnPublicFiles.Flat (Holds)

/- Lean compares the stored files by their name: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles

/-- **A served request at the base return**: the range test says yes, the trace is there at every record, and
an index that the matrix holds serves the request at the return's public part. -/
theorem servedInput_atBaseReturn (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {A : BaseReturn} (H : HeadAtReturn Z A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFilling = .ok A) {M : FullSizeMatrix} {x' : XF}
    (served : ServedRequest committerCoinCountLessOne Z read M x') :
    (∀ rec : RecFull, A.H.inRange M = true ∧ (A.H.trace M (instanceAsPlainRecord (x', rec))).isSome = true) ∧
      ∃ i : Cm.Idx, Holds M i ∧ OnBytes.HonestTrace.ServesAt (P5J.At.X A.Z) i x'.val := by
  have below := OnBytes.HonestTrace.JointMeets.servedRequest_below scope read M x' served
  have S := HonestTraceRun.Meets.serves_at_plug scope live H.head.laid (P := baseFilling) rfl rfl hA
  exact ⟨fun rec => S.both rec below,
    OnBytes.FrontRoad.served_of_valid Z A.Z H.places H.firstChain scope read live H.head.laid M x'
      below⟩

/-- **THE ONE EXISTENCE ON THE REQUEST's SIDE: at the stored full-size files some request is served.** No premise. The
weights are made up ("Meaning.served_met"). -/
theorem servedRequest_atStoredFiles :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (read : VerifierAndGoals.readFiles VerifierAndGoals.storedPublicFiles = .ok pp) (M : FullSizeMatrix) (x' : XF),
      ServedRequest committerCoinCountLessOne VerifierAndGoals.storedPublicFiles read M x' := by
  obtain ⟨scope, pp, read, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨M, x', served, -⟩ := OnBytes.HonestTrace.JointMeets.servedRequest_member scope read
  exact ⟨pp, read, M, x', served⟩

/-- **At the stored full-size files, at a given return, a given head at it and a given served request.** No other
premise. -/
theorem servedInput_atStoredFiles {A : BaseReturn} (H : HeadAtReturn VerifierAndGoals.storedPublicFiles A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL baseFilling =
      .ok A) {pp : Inst.Model.ScalesAndPolicy} (read : VerifierAndGoals.readFiles VerifierAndGoals.storedPublicFiles = .ok pp) {M : FullSizeMatrix} {x' : XF}
    (served : ServedRequest committerCoinCountLessOne VerifierAndGoals.storedPublicFiles read M x') :
    (∀ rec : RecFull, A.H.inRange M = true ∧ (A.H.trace M (instanceAsPlainRecord (x', rec))).isSome = true ∧
        H.description.okStart (instanceAsPlainRecord (x', rec)) = true ∧
        (H.description.start₁ (H.description.pub (instanceAsPlainRecord (x', rec)))).failed.isNone = true) ∧
      ∃ i : Cm.Idx, Holds M i ∧ OnBytes.HonestTrace.ServesAt (P5J.At.X A.Z) i x'.val := by
  obtain ⟨hin, hi⟩ := servedInput_atBaseReturn VerifierAndGoals.storedPublicFiles VerifierAndGoals.filesRead.full.1 read
    AtFullSide.Top.theLive_zFull H made served
  obtain ⟨-, -, hz⟩ := aroundTheStart_atStoredFiles H made
  exact ⟨fun rec => ⟨(hin rec).1, (hin rec).2, (hz (x', rec)).1, (hz (x', rec)).2⟩, hi⟩

/-- **The same under "there are".** No premise. A corollary: not to be joined with another "there are". -/
theorem inputAroundTheStart_atStoredFiles (numbers : FallNumbers) :
    ∃ (A : BaseReturn) (H : HeadAtReturn VerifierAndGoals.storedPublicFiles A) (pp : Inst.Model.ScalesAndPolicy)
      (read : VerifierAndGoals.readFiles VerifierAndGoals.storedPublicFiles = .ok pp) (M : FullSizeMatrix) (x' : XF) (i : Cm.Idx),
      onlineProverFromPublicFiles OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL baseFilling = .ok A ∧
      A.F = H.description ∧
      ScriptIsTheSenders H
        (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A H.firstChain numbers) ∧
      ServedRequest committerCoinCountLessOne VerifierAndGoals.storedPublicFiles read M x' ∧ Holds M i ∧
      OnBytes.HonestTrace.ServesAt (P5J.At.X A.Z) i x'.val ∧
      ∀ rec : RecFull, A.H.inRange M = true ∧ (A.H.trace M (instanceAsPlainRecord (x', rec))).isSome = true ∧
        H.description.okStart (instanceAsPlainRecord (x', rec)) = true ∧
        (H.description.start₁ (H.description.pub (instanceAsPlainRecord (x', rec)))).failed.isNone = true := by
  obtain ⟨A, H, hA⟩ := baseReturn_atStoredFiles
  obtain ⟨pp, read, M, x', served⟩ := servedRequest_atStoredFiles
  obtain ⟨eF, hS, -⟩ := aroundTheStart_atStoredFiles H hA
  obtain ⟨hin, i, hi, Sv⟩ := servedInput_atStoredFiles H hA read served
  exact ⟨A, H, pp, read, M, x', i, hA, eF, hS numbers, served, hi, Sv, hin⟩

end OnBytes.HonestTrace.EntersAtStoredFiles

#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.servedInput_atBaseReturn
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.servedRequest_atStoredFiles
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.servedInput_atStoredFiles
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.inputAroundTheStart_atStoredFiles
