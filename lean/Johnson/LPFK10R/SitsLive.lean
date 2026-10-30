-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsLive.lean: THE ROW K10_sits UNDER THE GATE's OWN YES: where the proof file's slot's gate says yes (FlashProve.protocolDataWellFormed) at public files in scope, THE IOP AS WRITTEN IN LEAN RETURNS, ITS DATA RETURN, AND EVERY SUB-PROTOCOL OF THE KIND K10 IN
ITS THREE CHAINS IS THE SEATED CLOSING OF A LINK. One statement and its proof. (In the Lean names a «block» is a sub-protocol and a «description» the IOP as written in Lean.)
WHY. k10_sits_file (SitsFile.lean, beside this file) stands under two premises: Open (onlineDescription's return, opened) and HeadIsTwo Z. By reading, the first follows from the gate's yes (FlashProve.pseat_name,
Johnson/Goal/Description/ProofSeat.lean, with seat_open). The second is head_is_two in scope.
  k10_sits_live   InScope P · readFiles P = .ok pp · protocolDataWellFormed (asDescriptionFiles P) = true: THERE ARE F, Z, Bs, base, c, A, B WITH: onlineDescription secondHashFunction P.pol P.lay P.KL = .ok F · F.planOk = true · F.data "proof file" = .ok (theProofData (asDescriptionFiles P)) · every test of LPFD.lawsAsk
                  says yes · theProofRun (asDescriptionFiles P) is F's own run · Open … · and k10_sits_file's four parts. (pseat_name's five conjuncts are all handed on: what stands in front of K10's four parts names no kind.)
LIMITS. k10_sits_live's three premises (in scope · read · protocolDataWellFormed's yes) are shown here of no files. Other Lean files prove them at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`, not throughout the scope: the first two `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean), the third `theLive_zFull`, `theLive_zGap` (AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean: a side library). Limits there. THE PROOF FILE ALONE: the key file's IOP is not here. At OnBytes.secondHashFunction, in scope. Nothing on soundness.

-/
import Johnson.LPFK10R.SitsFile
import Johnson.Goal.Description.ProofSeat

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Close (Par K10LawAt)
open ProofFile (Cl)
open IM

/-- **K10_sits under the gate's own yes.** -/
theorem k10_sits_live (P : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true) :
    ∃ (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat),
      ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F ∧ F.planOk = true ∧
      F.data "proof file" = .ok (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles P)) ∧
      (∀ t ∈ LPFD.lawsAsk OnBytes.secondHashFunction P.pol P.lay P.KL F
        (FlashProve.theProofData (VerifierAndGoals.asDescriptionFiles P)), t.2 = true) ∧
      FlashProve.theProofRun (VerifierAndGoals.asDescriptionFiles P) = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      (F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
          c).first = c) ∧
      (∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
        ∃ (l : ℕ) (sub : ModelPart) (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par),
          (ProofFile.subsOf Z)[l]? = some sub ∧ c.links[l]? = some Lk ∧ k9At Z l = some p ∧
          ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ Lk.close[1]? = some b ∧
          LaidAlone ProofFile.sameReply b
            (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype b.name
            (cAt l sub 1 KindName.K10) ∧ K10LawAt b Q) ∧
      (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ KindName.K10) ∧
        ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ KindName.K10 := by
  obtain ⟨F, h1, h2, h3, h4, h5⟩ := FlashProve.pseat_name P live
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open h1
  obtain ⟨k0, k1, k2, k3⟩ := k10_sits_file O (head_is_two hS hR O)
  exact ⟨F, Z, Bs, base, c, A, B, h1, h2, h3, h4, h5, O, k0, k1, k2, k3⟩

end LPFK10

#print axioms LPFK10.k10_sits_live
