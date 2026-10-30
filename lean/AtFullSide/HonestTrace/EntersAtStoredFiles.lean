-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/EntersAtStoredFiles.lean

It states no goal. No property of the protocol is claimed.

THE PREMISES AROUND "enters_firstThread" (Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean), AT THE STORED
FULL-SIZE FILES, WITH NO PREMISE LEFT. That theorem says that the first thread holds at the start
that "ready" gives. It takes: a return A of the maker, the head at it (HeadAtReturn), the thread's parts
(FirstThreadParts), hR ("ready" returns), hok (the instance's test), hReq, Sv and Ti.
("No mark at the first state" is no premise of it: it proves that itself: "no_mark_at_start".)
This file pays the return, the head,
the parts and hok, and shows "no mark" in the description's own words, at the BASE filling "baseFilling": the kinds'
sides at the matrices, before the coins' map is laid over it. It does not import that theorem's file:
that hok is that theorem's premise to the letter was held by reading, against
Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean: Lean does not guard it here.

Main theorems:
* "noMark_of_okStart": "no mark" follows from hok, at every return and head: at any public files. By two laws of the
  library ("reqOk_of_okStart", "start_noMark"); a twin in other words of "no_mark_at_start" of that theorem's file.
* "baseReturn_with_head": where the public files are in scope, are read and pass "protocolDataWellFormed": the maker
  returns at the base filling, and the head at that return has a member.
* THE FORMS TO JOIN WITH OTHER LAWS, AT A GIVEN RETURN A AND A GIVEN HEAD H AT IT (a head carries data that the thread
  reads; that a head at a return is one: "headAtReturn_unique", EntersAtStoredFilesOneHead.lean):
  "aroundTheStart_atGivenHead": if the instance's test accepts every written instance: the description that the maker
  returned is H's; the thread's parts at the closed Script are the senders' ("ScriptIsTheSenders"), at all numbers
  of the falls; hok and "no mark" at every written instance.
  "aroundTheStart_atStoredFiles": the same at the stored full-size files "VerifierAndGoals.storedPublicFiles", with no premise but A, H and
  that the maker returned A.
* THE ONE EXISTENCE: "baseReturn_atStoredFiles": at "VerifierAndGoals.storedPublicFiles" there are such A and H: NO PREMISE.
* "premisesAroundTheStart", "premisesAroundTheStart_atStoredFiles": the two together under "there are": corollaries.
  NOT TO BE JOINED with another "there are": use the forms above.

Limits.
* EVERYTHING HERE STANDS AT A RETURN OF THE BASE FILLING. The honest prover's term (E2E/TheHonestProver.lean) is made
  at that filling read through the coins' map ("OnlineProverParts.through id (tableCoins files) …"): another type of coins and
  another return. So these are not the premises of "enters_firstThread" at the term's own return: nothing here
  crosses.
* hR IS NOT PAID HERE: that "ready" returns at this return is not shown here. hReq, Sv, Ti are other
  files'. So no stand of the first thread is shown here.
* "written instance": "LPFD.Full.instanceAsPlainRecord z" at a typed request and a record, served or not.
* The numbers of the falls are a free argument: no fall's test reads them.
* It stands over the side library (theLive_zFull, item_zFull): closed facts by evaluation
  in Lean's kernel, which no independent checker has replayed; at the hash "OnBytes.secondHashFunction" alone.
* "VerifierAndGoals.storedPublicFiles" is a term written in the library, the stored full-size example of the three
  public files: no Lean ties it to files in a folder.
* Nothing on completeness, soundness, hiding or any other property of the protocol.
-/
import AtFullSide.K12.ReturnsAtAnyIndex
import AtFullSide.K1.FirstScriptIsSenders
import AtFullSide.Top.LiveAtFull
import Johnson.P5J.HeadOfLive
import Johnson.Goal.Files.FilesReadProof
import AtFullSide.E2E.StartAtWrittenFiles
import Johnson.Desc.ProofFile.Honest.OpenHonest
import Johnson.AtFull.Shape.ReqOkOfStart
import Johnson.IMR.EndFive
import E2E.TheHonestProver
import AtFullSide.HonestTrace.EntersAtStoredFilesOneHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.HonestTrace.EntersAtStoredFiles

open ProofFile.Honest (onlineProverFromPublicFiles OnlineProverWithDescription OnlineProverParts IndexCommitterCoins Cells onlineProverPartsInUse openHonest)
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers ScriptIsTheSenders)
open ProofFile.Honest.K1 (firstParts scriptIsTheSenders_parts)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open LPFD.Full (XF instanceAsPlainRecord)
open OnBytes.Flat (RecFull)
open P5J (LaidAt F0T)

/- Lean compares the stored files by their name: unfolded, they are whole files of bytes. -/
attribute [local irreducible] VerifierAndGoals.storedPublicFiles

/-! ## 1. No mark at the first state -/

section AnyReturn
variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Where the instance's test says yes, the first state bears no mark**: at every return of the maker and
every head at it. -/
theorem noMark_of_okStart (h : HeadAtReturn files A) {x : ProofFile.Inst}
    (hok : h.description.okStart x = true) :
    (h.description.start₁ (h.description.pub x)).failed.isNone = true := by
  have hq := Johnson.AtFull.Shape.reqOk_of_okStart hok
  have e : (ProofFile.startS A.Z x.pub).failed = none :=
    _root_.Meaning.K2.start_noMark h.head.laid.pub hq
  show (ProofFile.startS A.Z x.pub).failed.isNone = true
  rw [e]
  rfl

end AnyReturn

/-! ## 2. The base return and the head at it -/

/-- **The base filling**: the kinds' sides, the closings, the proximity tests' and the message W's, at the
matrices and at the library's own coins. The online filling of E2E/TheHonestProver.lean is this one read
through the coins' map. -/
abbrev baseFilling : OnlineProverParts FullSizeMatrix IndexCommitterCoins Cells Unit Unit :=
  onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- The input's named member is in range. (Proved here, not called from
AtFullSide/Honest/TermMade.lean.) -/
theorem matrixInput_dummy_inRange : matrixInput.inRange matrixInput.dummy = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf
    (VerifiableInference.OnPublicFiles.Flat.matrixOf ProofFile.Honest.fullIn.dummy)).isSome = true
  rw [VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf ProofFile.Honest.fullIn.dummy)]
  rfl

/-- A return of the maker at the base filling. -/
abbrev BaseReturn := OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit

/-- **The maker returns at the base filling, and the head at that return has a member**, where the public
files are in scope, are read and pass the verifier's test on them. The description that the maker returned is
the head's. -/
theorem baseReturn_with_head (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : VerifierAndGoals.InScope Z = true)
    (read : VerifierAndGoals.readFiles Z = .ok pp) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ (A : BaseReturn) (H : HeadAtReturn Z A),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFilling = .ok A ∧ A.F = H.description := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_of_live Z scope read live
  obtain ⟨A, hA, eZ, eF, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest matrixInput_dummy_inRange
  subst eZ
  exact ⟨A, ⟨⟨_, hA⟩, Np, cF, x, h⟩, hA, eF⟩

/-- **The premises around the start, at a given return and a given head at it.** start: the instance's test accepts
every written instance, at whatever letters the description is laid. numbers: the stated numbers of the falls, free. -/
theorem aroundTheStart_atGivenHead (Z : VerifierAndGoals.PublicFiles)
    (start : ∀ {D r Zp Np cF}, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
      ∀ z : XF × RecFull, (F0T OnBytes.secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true)
    {A : BaseReturn} (H : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFilling = .ok A) :
    A.F = H.description ∧
      (∀ numbers : FallNumbers, ScriptIsTheSenders H
        (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A H.firstChain numbers)) ∧
      ∀ z : XF × RecFull, H.description.okStart (instanceAsPlainRecord z) = true ∧
        (H.description.start₁ (H.description.pub (instanceAsPlainRecord z))).failed.isNone = true :=
  ⟨description_of_head H, fun numbers => scriptIsTheSenders_parts H made numbers, fun z =>
    ⟨start H.head.laid z, noMark_of_okStart H (start H.head.laid z)⟩⟩

/-- **The same under "there are".** A corollary: not to be joined with another "there are". -/
theorem premisesAroundTheStart (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (start : ∀ {D r Zp Np cF}, LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
      ∀ z : XF × RecFull, (F0T OnBytes.secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true)
    (numbers : FallNumbers) :
    ∃ (A : BaseReturn) (H : HeadAtReturn Z A),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFilling = .ok A ∧ A.F = H.description ∧
      ScriptIsTheSenders H
        (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A H.firstChain numbers) ∧
      ∀ z : XF × RecFull, H.description.okStart (instanceAsPlainRecord z) = true ∧
        (H.description.start₁ (H.description.pub (instanceAsPlainRecord z))).failed.isNone = true := by
  obtain ⟨A, H, hA, -⟩ := baseReturn_with_head Z scope read live
  obtain ⟨eF, hS, hz⟩ := aroundTheStart_atGivenHead Z start H hA
  exact ⟨A, H, hA, eF, hS numbers, hz⟩

/-! ## 3. At the stored files -/

/-- **THE ONE EXISTENCE: at the stored full-size files the maker returns at the base filling and there is a head at
that return.** No premise. The return is one (the maker is a function) and so is the head
("headAtReturn_unique"). -/
theorem baseReturn_atStoredFiles :
    ∃ (A : BaseReturn) (_ : HeadAtReturn VerifierAndGoals.storedPublicFiles A),
      onlineProverFromPublicFiles OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL baseFilling = .ok A := by
  obtain ⟨scope, pp, read, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨A, H, hA, -⟩ := baseReturn_with_head VerifierAndGoals.storedPublicFiles scope read AtFullSide.Top.theLive_zFull
  exact ⟨A, H, hA⟩

/-- **At the stored full-size files, at a given return and a given head at it.** No other premise. -/
theorem aroundTheStart_atStoredFiles {A : BaseReturn} (H : HeadAtReturn VerifierAndGoals.storedPublicFiles A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL baseFilling =
      .ok A) :
    A.F = H.description ∧
      (∀ numbers : FallNumbers, ScriptIsTheSenders H
        (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A H.firstChain numbers)) ∧
      ∀ z : XF × RecFull, H.description.okStart (instanceAsPlainRecord z) = true ∧
        (H.description.start₁ (H.description.pub (instanceAsPlainRecord z))).failed.isNone = true :=
  aroundTheStart_atGivenHead VerifierAndGoals.storedPublicFiles (fun L z => AtPublicFiles.Start.okStart_zFull L z) H made

/-- **The same under "there are".** No premise. A corollary: not to be joined with another "there are". -/
theorem premisesAroundTheStart_atStoredFiles (numbers : FallNumbers) :
    ∃ (A : BaseReturn) (H : HeadAtReturn VerifierAndGoals.storedPublicFiles A),
      onlineProverFromPublicFiles OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL baseFilling = .ok A ∧
      A.F = H.description ∧
      ScriptIsTheSenders H
        (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A H.firstChain numbers) ∧
      ∀ z : XF × RecFull, H.description.okStart (instanceAsPlainRecord z) = true ∧
        (H.description.start₁ (H.description.pub (instanceAsPlainRecord z))).failed.isNone = true := by
  obtain ⟨A, H, hA⟩ := baseReturn_atStoredFiles
  obtain ⟨eF, hS, hz⟩ := aroundTheStart_atStoredFiles H hA
  exact ⟨A, H, hA, eF, hS numbers, hz⟩

end OnBytes.HonestTrace.EntersAtStoredFiles

#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.noMark_of_okStart
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.baseReturn_with_head
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.aroundTheStart_atGivenHead
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.premisesAroundTheStart
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.baseReturn_atStoredFiles
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.aroundTheStart_atStoredFiles
#print axioms OnBytes.HonestTrace.EntersAtStoredFiles.premisesAroundTheStart_atStoredFiles
