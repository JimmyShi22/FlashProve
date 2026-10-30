-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WSaysAtLetters.lean: the clause saysAt of K12's stand at the last chain's test, at
TheLetters' names: thread₃, said₃.

  saysAt_at_letters   SaysLeft and SaysAt at every stand and every row of coins

By what. saysAt_rest (WSaysRest.lean), saysAt_own and owe_of_says (K12/AtFile/WSays.lean). hsam:
samples_at_W_at_letters (AtFullSide/K14/FivesAtTheLetters.lean) has this form with ds := [].

Limits: hsam and the public premises of saysAt_rest, at these names; the job, the field and the way in
are paid here. NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.WSaysRest
import AtFullSide.Honest.TheLetters
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WField
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open AtFullSide.Honest.TheLetters
open VerifiableInference.Desc.K1 (qAt)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open OnBytes.Slice (rdE frS)
open OnBytes.Means (sampleItem)
open ProofFile.Honest.K12.AtFile (SaysLeft narrowW FieldAtW LetterAtW saysAt_own owe_of_says field_of_said_W
  letter_at_filling enters_at_W)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW ends_at_lastThread)
open ProofFile.Honest.FirstThread (HeadAtReturn sharedShape)
open ProofFile.Honest.K12.Light (ManyJob SaysAt)
open ProofFile.Honest.Term (matrixInput)
open Desc.K14.Honest
open ProofFile.Honest.K14
open VerifierAndGoals.AtTheName (dpZ)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **SaysAt at a stand at TheLetters' names.** -/
theorem saysAt_at_letters (h : HeadAtReturn Z A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {O : OpenShared A} (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hsam : ∀ k st m E, ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E →
      ∀ G, st.st.groups[st.loc.own]? = some G → sampleItem rdE st.st G.members.toList
        (wordsAtW h (first h) (reads h) st k m.st.input (m.st.heard ++ [])))
    (hAp : ProofFile.Honest.FirstThread.SharedTenantsApart h)
    (hpl : P.ownMany.toRun.toTest.p.place = placeW)
    {layO : OnBytes.TreeLay}
    (hP : Plan2 (qAt A.Z h.places) (ProofFile.Honest.K12.Light.sentOf (qAt A.Z h.places).S) layO)
    (hcov : ∀ k : Coins A.B, ∃ own, (k.look 1 ⟨sendPlace 5, 0⟩).2.cut ⟨0, 0⟩
      (sendingPart (jobOmega ⟨qAt A.Z h.places, 0⟩)).takes = some own)
    (n5 : (dueAt (A.B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega ⟨qAt A.Z h.places, 0⟩)).takes.e)
    (hdS : dueAt A.B.shared senderO = (sendingPart (jobOmega ⟨qAt A.Z h.places, 0⟩)).takes)
    (htf : rowOF.2.2.f ≤ (sendingPart (jobOmega ⟨qAt A.Z h.places, 0⟩)).takes.f)
    (hte : rowOF.2.2.e ≤ (sendingPart (jobOmega ⟨qAt A.Z h.places, 0⟩)).takes.e)
    (ht₁ : 83 ≤ h.description.t₁)
    (hten : h.sharedNumbers.tenant .oOmega = (((dpZ Z).at frS.P.T.a).t₁ + 1, 0))
    (hpoint : ((declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).head?).map
      (·.entry.drawE) = some (qAt A.Z h.places).par.S.kCol)
    (hx199 : (narrowW.st.oracles[199]?).map (·.shape) = some (qAt A.Z h.places).par.S.omega)
    (hso : sharedShape A.Z h.places .oOmega = (qAt A.Z h.places).par.S.omega)
    (ha : ∀ a, sendPub A.Z = some ⟨qAt A.Z h.places, a⟩ → a = 0) :
    ∀ k st m E (c : RowCoins [(firstPart P.ownMany.toRun.toTest :
        Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart P.ownMany.toRun.toTest]),
      ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) P.ownMany.toRun.toTest.p.place
        [(firstPart P.ownMany.toRun.toTest :
          Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
          restPart P.ownMany.toRun.toTest] 0 = .ok c →
      (∃ ws, SaysLeft P.ownMany m.st.input (frontOf m) (restCoins P.ownMany.toRun.toTest c.2.1) st ws) ∧
        SaysAt P.ownMany m.st.input (frontOf m) (restCoins P.ownMany.toRun.toTest c.2.1) := by
  intro k st m E c u hl
  have hF : FieldAtW (P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain) (thread₃ h P R)
      (said₃ h P R) 2 := field_of_said_W _ _ 2 (fun _ _ s => s.1)
  obtain ⟨M', hM', -, -, -, -, -, Lt⟩ := letter_at_filling (Wt := ProofFile.Honest.FirstThread.WtF) h.head
    matrixInput OnBytes.HonestTrace.Sz.ref openHonest hA
  obtain rfl : M' = P.ownMany := Option.some.inj (hM'.symm.trans P.ownIsTheFilling)
  have H₀ : LetterAtW (P5J.F0T OnBytes.secondHashFunction A.Z h.places h.firstChain) (thread₃ h P R) 2 P.ownMany
      enterOwn leaveOwn ((ToldDesc.ownAt h.places).retype :
        VerifiableInference.Desc.Block VerifiableInference.Desc.Third.S₃ ProofFile.Cl) idleT12 :=
    Lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hEnter : ∀ k st m E, ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E →
      enterOwn st = .ok (P.ownMany.rec₀ m.st.input (frontOf m)) :=
    fun _ _ _ _ u' => (enters_at_W H₀ hF u').1
  obtain ⟨ws, hL⟩ := saysAt_rest h matrixInput OnBytes.HonestTrace.Sz.ref openHonest hA hM' (first h) rfl
    _ R.own (said₃ h P R) hF hEnter hsam hAp hpl hP hcov n5 hdS htf hte ht₁ hten hpoint hx199 hso ha
    k st m E c u hl
  obtain ⟨f, e, -, -, hk⟩ := ends_at_lastThread h (first h) _ _ R.own u.1
  obtain ⟨⟨s₀, B⟩, -⟩ := VerifiableInference.Desc.Last.behindOk_of_two hk
  exact ⟨⟨ws, hL⟩, saysAt_own P.ownMany _ _ _ (hEnter k st m E u) (owe_of_says B.tidy hL)⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.saysAt_at_letters
