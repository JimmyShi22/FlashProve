-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/TieSteps.lean: the tie: a run's call of the fast form in steps is the goals' verify
at the built D*.
`stepsYes`: the conjunction of the twelve steps at a plan's values G, an item `it` and the run's
letters.
`verify_is_steps`, `verify_is_steps_form`: the goals' verify at the built D* is these steps, at the
plan that the record lays. `verify_lay_congr`, `verify_lay_congr_form`: two records of letters that
are both live at the files and share G, it, DK, DP, runK, runP and dec there have one verify.
`tenth_call`: the call `PV.RunPure.Full.stepsFullAllAt` at a plan G and the request's two strings at
an item `it` returns these steps at G and `it`.
`tie_tenth`, `tie_tenth_form`: what that call answers at the plan that the record lays is the value
of the goals' verify at `hashOf O`. `tie_tenth_oracle`, `tie_tenth_form_oracle`: at the format's own
hash, where two of the premises are theorems.
Limits. An equation of a value, at one hash function: verify has no code. It holds at any three
decisions. The entry's rounds and places are pinned. No soundness is claimed.

-/
import Johnson.Goal.Tie.TiePremisesAsRows
import Johnson.Goal.Tie.Seam10
import Fmt.Rules23Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open PV.Head (cThru sevenThru)
open PV.OkOwn (okOwnF)
open LPFD.Full (XF GF stepsFAt linkAt)
open PV.EntryFive (dsF xsF)
open PV.RunPure.Full (stepsFullAllAt)

attribute [local irreducible] PV.EncId.encF

/-- The «and» of the twelve steps at the run's pinned letters. -/
def stepsYes (G : FilesParameters XF RecFull) (it : XF → ByteArray) (O : ByteArray → ByteArray) (c : ByteArray)
    (hc : c.size = 32)
    (seven : List ByteArray) (h₀ : HId) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View →
        PQ.View → Bool)
    (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View →
        Bool)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) : Bool :=
  (stepsFAt G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF (sROf G)
    (linkAt G c hc DK DP runK runP dec (PV.RunArgsF.pdLOf seven))
    (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1) O commitment prompt output f.aux f.cm
        f.rcd f.copy
    { f.fT with cfg := c } { f.e with cfg := c } { f.fB with cfg := c }).yes

/-- The left half's right side is these steps, at every h₀. -/
theorem innerCompiledVerifierAnswerOnDecodedProof_dataAtFilesFromRounds (L : DescriptionData) (Zk : OnBytes.K.Pub) (G : FilesParameters XF RecFull) (DK DP : WholeD)
    (h : roundsDataFit DK DP = true) (c : ByteArray)
    (hc : c.size = 32) (seven : List ByteArray) (O : ByteArray → ByteArray) (h₀ : HId) (commitment
        : Commitment)
    (prompt output : List Token) (f : DecodedProof) :
    (dataAtFilesFromRounds L Zk G DK DP h).innerCompiledVerifierAnswerOnDecodedProof c hc seven (hashOf O) commitment prompt output f =
      stepsYes G (L.it Zk) O c hc seven h₀ DK DP (L.runK Zk) (L.runP Zk) (L.dec Zk) commitment
          prompt
          output
          f :=
  (LPFD.Full.seamSteps (L.A Zk) (L.E Zk) G c hc DK DP (L.runK Zk) (L.runP Zk) (L.dec Zk) (L.P
      Zk
      G DK DP) h₀ L.hStar (L.it Zk)
    (sROf G) (PV.RunArgsF.pdLOf seven) (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1)
    ((fit3_iff DK DP).1 h).1 ((fit3_iff DK DP).1 h).2.1 ((fit3_iff DK DP).1 h).2.2 (L.N Zk G
        DK DP) L.d₀ O commitment
    prompt output f.aux f.cm f.rcd f.copy { f.fT with cfg := c } { f.e with cfg := c } { f.fB with
        cfg := c }).symm

section
variable (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
  (live : L.live (asDescriptionFiles Z) = true) (O : ByteArray → ByteArray)
  (hO : (cThru O (asDescriptionFiles Z)).size = 32)
  (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32) (h₀ : HId)
  (commitment : Commitment) (prompt output : List Token)
include scope live h7

/-- **THE GOALS' verify AT THE BUILT D* IS THE TWELVE STEPS.** -/
theorem verify_is_steps (B : FormBytes) (f : DecodedProof) (hdec : decodeD (cThru O (asDescriptionFiles Z)) B =
        some f) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf O) =
      stepsYes (L.G (asDescriptionFiles Z)) (L.it (asDescriptionFiles Z)) O (cThru O (asDescriptionFiles Z)) hO (sevenThru O
                                           recordGround
                                           (asDescriptionFiles Z) (cThru
                                                      O (asDescriptionFiles Z))) h₀
        (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z)) (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec
                                                        (asDescriptionFiles Z)) commitment prompt
        output f :=
  (verify_descriptionOfDataOnBytes L Z scope live O hO h7 commitment prompt output B f hdec).trans
    (innerCompiledVerifierAnswerOnDecodedProof_dataAtFilesFromRounds L (asDescriptionFiles Z) _ _ _ (L.hlive _ live) _ hO _ O h₀ commitment prompt output f)

/-- **THE SAME AT THE FORM THAT A RUN HANDS THE TERM: AT EVERY f.** -/
theorem verify_is_steps_form (Hf : CommitterAndProverOfDecodedProof) (f : DecodedProof) :
    (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L Hf) Z ((descriptionOfDataOnDecodedProof L Hf).parse Z) commitment prompt output
        f).evaluate (hashOf O) =
      stepsYes (L.G (asDescriptionFiles Z)) (L.it (asDescriptionFiles Z)) O (cThru O (asDescriptionFiles Z)) hO (sevenThru O
                                           recordGround
                                           (asDescriptionFiles Z) (cThru
                                                      O (asDescriptionFiles Z))) h₀
        (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z)) (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec
                                                        (asDescriptionFiles Z)) commitment prompt
        output f :=
  (verify_descriptionOfDataOnDecodedProof L Hf Z scope live O hO h7 commitment prompt output f).trans
    (innerCompiledVerifierAnswerOnDecodedProof_dataAtFilesFromRounds L (asDescriptionFiles Z) _ _ _ (L.hlive _ live) _ hO _ O h₀ commitment prompt output f)

end

/-- **The law of shared letters.** two DescriptionData that are both live at Zk and share the seven letters G ·
  it · DK · DP · runK · runP · dec there have one verify. -/
theorem verify_lay_congr (L L' : DescriptionData) (Z : PublicFiles) (eG : L.G (asDescriptionFiles Z) = L'.G (asDescriptionFiles Z))
    (eI : L.it (asDescriptionFiles Z) = L'.it (asDescriptionFiles Z))
    (eDK : L.DK (asDescriptionFiles Z) = L'.DK (asDescriptionFiles Z))
    (eDP : L.DP (asDescriptionFiles Z) = L'.DP (asDescriptionFiles Z)) (eK : L.runK (asDescriptionFiles Z) = L'.runK (asDescriptionFiles Z))
    (eP : L.runP (asDescriptionFiles Z) = L'.runP (asDescriptionFiles Z)) (eD : L.dec (asDescriptionFiles Z) = L'.dec (asDescriptionFiles Z))
        (scope : VerifierAndGoals.InScope Z = true)
    (live : L.live (asDescriptionFiles Z) = true) (live' : L'.live (asDescriptionFiles Z) = true) (O : ByteArray →
                              ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes) (f : DecodedProof)
    (hdec : decodeD (cThru O (asDescriptionFiles Z)) B = some f) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf O) =
      (VerifierAndGoals.verify (descriptionOfDataOnBytes L') Z ((descriptionOfDataOnBytes L').parse Z) commitment prompt output
          B).evaluate (hashOf O) := by
  rw [verify_is_steps L Z scope live O hO h7 L.hStar commitment prompt output B f hdec,
    verify_is_steps L' Z scope live' O hO h7 L.hStar commitment prompt output B f hdec, eG, eI, eDK,
        eDP,
        eK, eP, eD]

/-- The same at the typed form, at every f, and at any two honest sides. -/
theorem verify_lay_congr_form (L L' : DescriptionData) (Hf Hf' : CommitterAndProverOfDecodedProof) (Z : PublicFiles)
    (eG : L.G (asDescriptionFiles Z) = L'.G (asDescriptionFiles Z)) (eI : L.it (asDescriptionFiles Z) = L'.it (asDescriptionFiles Z))
    (eDK : L.DK (asDescriptionFiles Z) = L'.DK (asDescriptionFiles Z)) (eDP : L.DP (asDescriptionFiles Z) = L'.DP (asDescriptionFiles Z))
    (eK : L.runK (asDescriptionFiles Z) = L'.runK (asDescriptionFiles Z)) (eP : L.runP (asDescriptionFiles Z) = L'.runP (asDescriptionFiles Z))
    (eD : L.dec (asDescriptionFiles Z) = L'.dec (asDescriptionFiles Z)) (scope : VerifierAndGoals.InScope Z = true) (live : L.live
                              (asDescriptionFiles Z) = true) (live' : L'.live (asDescriptionFiles Z) = true)
    (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) :
    (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L Hf) Z ((descriptionOfDataOnDecodedProof L Hf).parse Z) commitment prompt output
        f).evaluate (hashOf O) =
      (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L' Hf') Z ((descriptionOfDataOnDecodedProof L' Hf').parse Z) commitment prompt output
          f).evaluate
        (hashOf O) := by
  rw [verify_is_steps_form L Z scope live O hO h7 L.hStar commitment prompt output Hf f,
    verify_is_steps_form L' Z scope live' O hO h7 L.hStar commitment prompt output Hf' f, eG, eI,
        eDK,
        eDP,
        eK, eP, eD]

/-! ## The run's call -/

/-- The call `PV.RunPure.Full.stepsFullAllAt` is some of these steps, at h₀ := Fmt.HO O. -/
theorem tenth_call (G : FilesParameters XF RecFull) (it : XF → ByteArray) (O : ByteArray → ByteArray)
    (c : ByteArray) (hc : c.size = 32)
    (seven : List ByteArray) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View →
        Bool)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) (s : FastSteps)
    (hs : stepsFullAllAt {} G (PV.MFull.spI it) O c seven DK DP runK runP dec commitment prompt
        output f.aux f.cm
        f.rcd f.copy f.fT f.e
      f.fB = some s) :
    s.yes = stepsYes G it O c hc seven (_root_.Fmt.HO O) DK DP runK runP dec commitment prompt
        output f := by
  unfold stepsFullAllAt at hs
  rw [dif_pos hc] at hs
  obtain rfl := Option.some.inj hs
  rfl

/-- **The run's call is the goals' verify at the built D*, the form bytes.** -/
theorem tie_tenth (L : DescriptionData) (Z : PublicFiles)
    (O : ByteArray → ByteArray) (B : FormBytes) (h : tiePremB (L.live (asDescriptionFiles Z)) Z O B = true)
        (commitment : Commitment)
    (prompt output : List Token) (f : DecodedProof) (hf : decodeD (cThru O (asDescriptionFiles Z)) B = some f) (s
                       : FastSteps)
    (hs : stepsFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z))) O
      (cThru O (asDescriptionFiles Z))
      (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (L.DK (asDescriptionFiles Z)) (L.DP
                                           (asDescriptionFiles Z))
      (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment prompt output f.aux
          f.cm f.rcd f.copy f.fT
      f.e f.fB = some s) :
    s.yes =
      (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
          (hashOf O) := by
  unfold tiePremB tieRows at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨scope, live, hO, h7, _⟩ := h
  rw [verify_is_steps L Z scope live O hO h7 (_root_.Fmt.HO O) commitment prompt output B f hf]
  exact tenth_call _ _ O _ hO _ _ _ _ _ _ commitment prompt output f s hs

/-- **THE SAME AT THE TYPED FORM, AT EVERY f**: so at whatever a control has turned behind the
  decoders. -/
theorem tie_tenth_form (L : DescriptionData) (Hf : CommitterAndProverOfDecodedProof) (Z : PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (live : L.live (asDescriptionFiles Z) = true)
    (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) (s : FastSteps)
    (hs : stepsFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z))) O
      (cThru O (asDescriptionFiles Z))
      (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))) (L.DK (asDescriptionFiles Z)) (L.DP
                                           (asDescriptionFiles Z))
      (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment prompt output f.aux
          f.cm f.rcd f.copy f.fT
      f.e f.fB = some s) :
    s.yes =
      (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L Hf) Z ((descriptionOfDataOnDecodedProof L Hf).parse Z) commitment prompt output
          f).evaluate
        (hashOf O) := by
  rw [verify_is_steps_form L Z scope live O hO h7 (_root_.Fmt.HO O) commitment prompt output Hf f]
  exact tenth_call _ _ O _ hO _ _ _ _ _ _ commitment prompt output f s hs

/-! ## At the format's own hash -/

theorem size_cThru (O : ByteArray → ByteArray) (h : ∀ s, (O s).size = 32) (Zk : OnBytes.K.Pub) :
    (cThru O Zk).size = 32 := h _

theorem size_sevenThru (O : ByteArray → ByteArray) (h : ∀ s, (O s).size = 32) (G : EntryGround)
    (Zk : OnBytes.K.Pub) (c : ByteArray) : ∀ b ∈ sevenThru O G Zk c, b.size = 32 := by
  intro b hb
  unfold sevenThru at hb
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hb
  exact h _

/-- **AT THE FORMAT's OWN HASH, THE FORM BYTES**: three premises, each a test with code. -/
theorem tie_tenth_oracle (L : DescriptionData) (Z : PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (live : L.live (asDescriptionFiles Z) = true) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof)
    (hf : decodeD (cThru _root_.Fmt.oracle (asDescriptionFiles Z)) B = some f) (s : FastSteps)
    (hs : stepsFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z)))
      _root_.Fmt.oracle
      (cThru _root_.Fmt.oracle (asDescriptionFiles Z))
      (sevenThru _root_.Fmt.oracle recordGround (asDescriptionFiles Z) (cThru _root_.Fmt.oracle (asDescriptionFiles Z)))
          (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z))
      (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment prompt output f.aux
          f.cm f.rcd f.copy f.fT
      f.e f.fB = some s) :
    s.yes =
      (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf _root_.Fmt.oracle) := by
  rw [verify_is_steps L Z scope live _root_.Fmt.oracle (size_cThru _ _root_.Fmt.size_oracle _)
    (size_sevenThru _ _root_.Fmt.size_oracle _ _ _) (_root_.Fmt.HO _root_.Fmt.oracle) commitment
        prompt output B f hf]
  exact tenth_call _ _ _root_.Fmt.oracle _ _ _ _ _ _ _ _ commitment prompt output f s hs

/-- **AT THE FORMAT's OWN HASH, THE TYPED FORM, AT EVERY f**: two premises. -/
theorem tie_tenth_form_oracle (L : DescriptionData) (Hf : CommitterAndProverOfDecodedProof) (Z : PublicFiles)
    (scope : VerifierAndGoals.InScope Z = true) (live : L.live (asDescriptionFiles Z) = true)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) (s : FastSteps)
    (hs : stepsFullAllAt {} (L.G (asDescriptionFiles Z)) (PV.MFull.spI (L.it (asDescriptionFiles Z)))
      _root_.Fmt.oracle
      (cThru _root_.Fmt.oracle (asDescriptionFiles Z))
      (sevenThru _root_.Fmt.oracle recordGround (asDescriptionFiles Z) (cThru _root_.Fmt.oracle (asDescriptionFiles Z)))
          (L.DK (asDescriptionFiles Z)) (L.DP (asDescriptionFiles Z))
      (L.runK (asDescriptionFiles Z)) (L.runP (asDescriptionFiles Z)) (L.dec (asDescriptionFiles Z)) commitment prompt output f.aux
          f.cm f.rcd f.copy f.fT
      f.e f.fB = some s) :
    s.yes =
      (VerifierAndGoals.verify (descriptionOfDataOnDecodedProof L Hf) Z ((descriptionOfDataOnDecodedProof L Hf).parse Z) commitment prompt output
          f).evaluate
        (hashOf _root_.Fmt.oracle) :=
  tie_tenth_form L Hf Z scope live _root_.Fmt.oracle (size_cThru _ _root_.Fmt.size_oracle _)
    (size_sevenThru _ _root_.Fmt.size_oracle _ _ _) commitment prompt output f s hs

end FlashProve
