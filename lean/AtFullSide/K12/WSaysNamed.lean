-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WSaysNamed.lean: what the last chain's test says at TheLetters' names, with the premise
on the sample rows alone beside the head, the maker's return at the base filling, and the letters.

  saysAt_named   SaysLeft and SaysAt at every stand of thread₃, said₃ at number 2 and every row of coins
  five_named     the five at number 2, at openLast: five_at_thread₃ with its one premise paid

By what. saysAt_at_letters (WSaysAtLetters.lean), publicFourteen_at_head (WPublicFourteen.lean).

Limits. hsam: hsam_at_letters (WSamplesAtLetters.lean) has it from the hash build's law, on a ground
that holds AtFullSide/Frames/LastAtValues e02d6544. NOT IN FRONT OF A LAW OVER COINS: that a stand is reached is not said. The full size and the
format's second hash function alone. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.WSaysAtLetters
import AtFullSide.K12.WPublicFourteen
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtTheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open AtFullSide.Honest.TheLetters
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.K12.AtFile (SaysLeft)
open ProofFile.Honest.K12.Light (SaysAt)
open ProofFile.Honest.Term (matrixInput)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **SaysAt at every stand at TheLetters' names.** -/
theorem saysAt_named (h : HeadAtReturn Z A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    {O : OpenShared A} (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hsam : ∀ k st m E, ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E →
      ∀ G, st.st.groups[st.loc.own]? = some G → OnBytes.Means.sampleItem OnBytes.Slice.rdE st.st
        G.members.toList (ProofFile.Honest.K12.AtFile.LotWJoint.wordsAtW h (first h) (reads h) st k m.st.input
          (m.st.heard ++ []))) :
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
  obtain ⟨layO, Q⟩ := publicFourteen_at_head h matrixInput OnBytes.HonestTrace.Sz.ref openHonest hA
    P.ownIsTheFilling
  exact saysAt_at_letters h hA P R hsam Q.tenantsApart Q.place Q.plan Q.covers
    Q.countAtFive Q.dueShared Q.rowBase Q.rowExtension Q.firstTrees Q.tenantOmega Q.point Q.shapeAt199
    Q.sharedShapeOmega Q.pointInFront

/-- **The five at the last chain's test, at TheLetters' names.** -/
theorem five_named (h : HeadAtReturn Z A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (O : OpenShared A) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hsam : ∀ k st m E, ThrS (thread₃ h (ProofFile.Honest.K12.AtFile.openLast h hA O) R)
        (said₃ h (ProofFile.Honest.K12.AtFile.openLast h hA O) R) 2 k st m E →
      ∀ G, st.st.groups[st.loc.own]? = some G → OnBytes.Means.sampleItem OnBytes.Slice.rdE st.st
        G.members.toList (ProofFile.Honest.K12.AtFile.LotWJoint.wordsAtW h (first h) (reads h) st k m.st.input
          (m.st.heard ++ [])))
    (fl : ℕ → VerifiableInference.Desc.Third.S₃ → List Fmt.Drawn → Option String) :
    ProofFile.Honest.K12.AtFile.FiveAt (thread₃ h (ProofFile.Honest.K12.AtFile.openLast h hA O) R)
      (said₃ h (ProofFile.Honest.K12.AtFile.openLast h hA O) R) fl 2 :=
  ProofFile.Honest.K12.AtFile.five_at_thread₃ h hA O R
    (fun k st m E c u hl => (saysAt_named h hA (ProofFile.Honest.K12.AtFile.openLast h hA O) R hsam k st m E c u hl).1)
    fl

end AtFullSide.K12

#print axioms AtFullSide.K12.saysAt_named
#print axioms AtFullSide.K12.five_named
