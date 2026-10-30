-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/TieWhole.lean: the tie at the fast form's one Bool.
`innerCompiledVerifierAnswerOnDecodedProof_whole`, `tie_tenth_whole`: what `PV.RunPure.Full.wholeFullAllAt` answers at the plan that the
record lays is the value of the goals' verify at the built D*. `steps_eq_whole`: so the two forms of
a run have one answer where both return.

-/
import Johnson.Goal.Tie.TieSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Maker OnBytes.Tie
open LPFD.Full (XF)
open PV.Head (cThru sevenThru)
open PV.RunPure.Full (stepsFullAllAt wholeFullAllAt)

attribute [local irreducible] PV.EncId.encF

set_option maxHeartbeats 2000000 in
/-- The left half's right side is the whole fast form's one Bool, at any plan's values G. -/
theorem innerCompiledVerifierAnswerOnDecodedProof_whole (L : DescriptionData) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD)
    (h : roundsDataFit DK DP = true) (c : ByteArray) (hc : c.size = 32) (seven : List ByteArray)
    (O : ByteArray → ByteArray) (commitment : Commitment) (prompt output : List Token)
    (f : DecodedProof) (b : Bool)
    (hb : wholeFullAllAt {} G (PV.MFull.spI (L.it Zk)) O c seven DK DP (L.runK Zk) (L.runP Zk)
        (L.dec Zk) commitment
      prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB = some b) :
    b = (dataAtFilesFromRounds L Zk G DK DP h).innerCompiledVerifierAnswerOnDecodedProof c hc seven (hashOf O) commitment prompt output f := by
  unfold wholeFullAllAt at hb
  rw [dif_pos hc] at hb
  rw [← Option.some.inj hb]
  exact LPFD.Full.seamWhole (L.A Zk) (L.E Zk) G c hc DK DP (L.runK Zk) (L.runP Zk) (L.dec Zk)
    (L.P Zk G DK DP) (_root_.Fmt.HO O) L.hStar (L.it Zk) (sROf G) (PV.RunArgsF.pdLOf seven)
    (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1) ((fit3_iff DK DP).1 h).1
    ((fit3_iff DK DP).1 h).2.1 ((fit3_iff DK DP).1 h).2.2 (L.N Zk G DK DP) L.d₀ O commitment prompt
    output f.aux f.cm f.rcd f.copy _ _ _

/-- **The run's one Bool is the goals' verify at the built D*, the form bytes.** -/
theorem tie_tenth_whole (L : DescriptionData) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes)
    (h : tiePremB (L.live (asDescriptionFiles Z)) Z O B = true) (commitment : Commitment)
    (prompt output : List Token) (f : DecodedProof) (hf : decodeD (cThru O (asDescriptionFiles Z)) B = some f)
    (b : Bool)
    (hb : wholeFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z))) O
      (cThru O (asDescriptionFiles Z))
      (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (L.DK (asDescriptionFiles Z))
      (L.DP (asDescriptionFiles Z)) (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment
      prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB = some b) :
    b = (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output
        B).evaluate (hashOf O) := by
  unfold tiePremB tieRows at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨scope, live, hO, h7, _⟩ := h
  rw [verify_descriptionOfDataOnBytes L Z scope live O hO h7 commitment prompt output B f hf]
  exact innerCompiledVerifierAnswerOnDecodedProof_whole L (asDescriptionFiles Z) _ _ _ (L.hlive _ live) _ hO _ O commitment prompt output f b hb

/-- So the two forms of a run have one answer where both return. -/
theorem steps_eq_whole (L : DescriptionData) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes)
    (h : tiePremB (L.live (asDescriptionFiles Z)) Z O B = true) (commitment : Commitment)
    (prompt output : List Token) (f : DecodedProof) (hf : decodeD (cThru O (asDescriptionFiles Z)) B = some f)
    (s : FastSteps)
    (hs : stepsFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z))) O
      (cThru O (asDescriptionFiles Z))
      (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (L.DK (asDescriptionFiles Z))
      (L.DP (asDescriptionFiles Z)) (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment
      prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB = some s) (b : Bool)
    (hb : wholeFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z))) O
      (cThru O (asDescriptionFiles Z))
      (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (L.DK (asDescriptionFiles Z))
      (L.DP (asDescriptionFiles Z)) (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment
      prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB = some b) : s.yes = b :=
  (tie_tenth L Z O B h commitment prompt output f hf s hs).trans
    (tie_tenth_whole L Z O B h commitment prompt output f hf b hb).symm

end FlashProve
