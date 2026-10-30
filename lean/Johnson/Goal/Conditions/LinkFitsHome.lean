-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file states no goal.
Johnson/Goal/Conditions/LinkFitsHome.lean: THE FOUR CLAUSES ON THE LINK OF HonFit
(Johnson/Prover/All/OfHonest.lean) AT THE HOME's OWN LETTERS: the input homeR b Z of the goals'
description at the written member (Johnson/Goal/Conditions/HomeAtWider.lean): the letters at which
LastFits.honest (Johnson/Goal/Conditions/HomeLast.lean) asks them.

It writes no record: it speaks of every three records whose link's record is the frame's (linkRec,
Johnson/Prover/Link/LinkFrame.lean) and of all falls with none at the link.

Main names.
  linkFits_home   extL, whL, accL and prL at the measure 0, as a conjunction in this order, each to
    the letter of HonFit's field: so that whoever builds HonFit writes "extL := h.1", "whL :=
    h.2.1", "accL := h.2.2.1", "prL := h.2.2.2".
  linkFits_of_yes THE SAME FROM "the link's decision says yes on the honest view" IN ITS OWN FORM:
    at the description's decision at the two written keys, for every instance, stored strings and
    what they mean: what the messages' maker is handed, what is meant, the relation and the maker
    are letters; so are the coin's map and what a private input means.

How. linkRec_acc_with, linkRec_wh, linkRec_pr (LinkFrame.lean), called at the home's letters: that
the protocol and the wire of the compiled verifier are the written ones is found by Lean by
unfolding. dec_at_D (Johnson/Goal/Conditions/LinkDecAt.lean). No limit is raised.

Limits. THAT THE DECISION SAYS YES IS A PREMISE. Three more stand beside it: hfull: at what the kit
draws each external opening reads as many positions as it counts · hcar: every stored symbol that is
read carries its position · hmeant: the relation holds at the home's own instance and stored
strings. A conjunction of four is no HonFit: nothing on the other two records. Which three provers
are defined for (homeR b Z).protocol: Johnson/Goal/Conditions/LinkFitsAt.lean, limit 4. accL is an AccLaw,
so it speaks only of the challenges that pass all proof-of-work checks
(Johnson/Prover/Link/LinkYesStm.lean, common limit 2). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeLast
import Johnson.Prover.At.IdleAt
import Johnson.Prover.Link.LinkFrame
import Johnson.Goal.Conditions.LinkDecAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open _root_.Iop (prRho)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open TypedOracleCompiler.Compile.Batch.Cms (batLC wLC)
open OnBytes.Prover (ThreeProvers Falls HonFit AccLaw)
open TypedOracleCompiler.Run.PQ (drawnSL passSL symbolsCarryTheirPositions)
open _root_.Run.PQ (everyOpeningHasItsDraws)
open PV.EntryFive (dsF xsF)
open Johnson.Prover.Link (MsgV linkRec viewOf)
open _root_.Desc.K15 (frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)
open _root_.Iop (twoExternalStrings Rho)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (uL)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **linkFits AT THE HOME's OWN LETTERS.** -/
theorem linkFits_home :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (Kc : Type) [Fintype Kc] [Nonempty Kc]
    (next : (homeR b Z).Index × ((homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed) ×
        ((homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed) → RecFull × RecFull → Kc → ℕ →
        List Fmt.Drawn → MsgV)
    (Hs : ThreeProvers (homeR b Z).protocol) (F : Falls Hs) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed),
    Hs.Lk = linkRec (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (fun w => ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1)) next →
    (∀ w x c, F.Lk w x c = ∅) →
    (∀ ρ, everyOpeningHasItsDraws xsF (drawnSL (ckP .two) dsF ρ) = true) →
    (∀ i r r' ρ, symbolsCarryTheirPositions frS.P.T.a dsF xsF (drawnSL (ckP .two) dsF ρ)
      ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r') = true) →
    (∀ i x r e r' e' (c : Kc), Yes i x → e ∉ Zs i r → e' ∉ Zs i r' →
      ∀ ρ, passSL (ckP .two) dsF ρ = true →
        (dataAtFiles flashProveData Z).dec ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e')
          (viewOf dsF frS.P.T.a xsF
            (next (i, (r, e), (r', e'))
              ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c)
            ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r')
            (drawnSL (ckP .two) dsF ρ)) = true) →
    (∀ i r e r' e', Hs.Lk.ext (i, (r, e), (r', e')) =
      ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r')) ∧
    (∀ w x c ρ, RoundsQueryLayout.zero (homeR b Z).protocol.link.shape (homeR b Z).linkRoundSplits (wLC (homeR b Z).queryLayout).sh ρ ∈
        Hs.Lk.withheld w x ∪ F.Lk w x c → ρ ∈ Hs.Lk.withheld w x ∪ F.Lk w x c) ∧
    (∀ i x r e r' e' c, Yes i x → e ∉ Zs i r → e' ∉ Zs i r' →
      AccLaw (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits) (wLC (homeR b Z).queryLayout)
        ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e')
        (Hs.Lk.ext (i, (r, e), (r', e')))
        (Hs.Lk.strat (i, (r, e), (r', e'))
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c)
        (Hs.Lk.withheld (i, (r, e), (r', e'))
            ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') ∪
          F.Lk (i, (r, e), (r', e'))
            ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c)) ∧
    (∀ i x r e r' e' c, Yes i x →
      prRho (Hs.Lk.withheld (i, (r, e), (r', e'))
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') ∪
        F.Lk (i, (r, e), (r', e'))
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c) ≤ 0) := by
  intro b Z Kc _ _ next Hs F Yes Zs hLk hF hfull hcar hyes
  obtain ⟨HT, HLk, HB⟩ := Hs
  dsimp only at hLk
  subst hLk
  refine ⟨fun _ _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro w x c ρ h
    rw [hF] at h ⊢
    exact Johnson.Prover.Link.linkRec_wh (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec _ next
      w x ρ _ h
  · intro i x r e r' e' c hy h1 h2
    rw [hF]
    exact Johnson.Prover.Link.linkRec_acc_with (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (LPFD.Full.KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (_root_.Run.chalP .two _) _ next
      (i, (r, e), (r', e')) _ c ∅ hfull (hcar i r r') (hyes i x r e r' e' c hy h1 h2)
  · intro i x r e r' e' c _
    rw [hF]
    exact le_of_eq (Johnson.Prover.Link.linkRec_pr (ckP .two) dsF frS.P.T.a xsF
      (dataAtFiles flashProveData Z).dec _ next _ _)

/-- **THE SAME FROM «THE LINK's DECISION SAYS YES ON THE HONEST VIEW» IN ITS OWN FORM.** -/
theorem linkFits_of_yes :
  ∀ (LC Mt : Type)
    (Mean : RecFull × RecFull → (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str → Mt → Prop)
    (nx : RecFull × RecFull → (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str → Mt → LC → ℕ → List Fmt.Drawn →
      MsgV),
    (∀ rr y M, Mean rr y M → ∀ (C : LC) (ρ : Rho (uL (ckP .two) dsFull)),
      (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP OnBytes.Params.recordPlan)).run
        (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 })
        (viewOf dsFull frS.P.T.a frD.xs (nx rr y M C) y (drawnSL (ckP .two) dsFull ρ)) = true) →
    ∀ (b : PublicFiles → ℕ) (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (Kc : Type) [Fintype Kc] [Nonempty Kc] (coinsOf : Kc → LC)
      (Mof : (homeR b Z).Index × ((homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed) ×
        ((homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed) → Mt)
      (Hs : ThreeProvers (homeR b Z).protocol) (F : Falls Hs) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
      (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed),
    Hs.Lk = linkRec (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (fun w => ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1))
      (fun w x c => nx x ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1) (Mof w)
        (coinsOf c)) →
    (∀ w x c, F.Lk w x c = ∅) →
    (∀ ρ, everyOpeningHasItsDraws xsF (drawnSL (ckP .two) dsF ρ) = true) →
    (∀ i r r' ρ, symbolsCarryTheirPositions frS.P.T.a dsF xsF (drawnSL (ckP .two) dsF ρ)
      ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r') = true) →
    (∀ i x r e r' e', Yes i x → e ∉ Zs i r → e' ∉ Zs i r' →
      Mean ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e')
        ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r') (Mof (i, (r, e), (r', e')))) →
    (∀ i r e r' e', Hs.Lk.ext (i, (r, e), (r', e')) =
      ((homeR b Z).protocol.encodeIndex i r, (homeR b Z).protocol.encodeIndex i r')) ∧
    (∀ w x c ρ, RoundsQueryLayout.zero (homeR b Z).protocol.link.shape (homeR b Z).linkRoundSplits (wLC (homeR b Z).queryLayout).sh ρ ∈
        Hs.Lk.withheld w x ∪ F.Lk w x c → ρ ∈ Hs.Lk.withheld w x ∪ F.Lk w x c) ∧
    (∀ i x r e r' e' c, Yes i x → e ∉ Zs i r → e' ∉ Zs i r' →
      AccLaw (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits) (wLC (homeR b Z).queryLayout)
        ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e')
        (Hs.Lk.ext (i, (r, e), (r', e')))
        (Hs.Lk.strat (i, (r, e), (r', e'))
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c)
        (Hs.Lk.withheld (i, (r, e), (r', e'))
            ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') ∪
          F.Lk (i, (r, e), (r', e'))
            ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c)) ∧
    (∀ i x r e r' e' c, Yes i x →
      prRho (Hs.Lk.withheld (i, (r, e), (r', e'))
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') ∪
        F.Lk (i, (r, e), (r', e'))
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c) ≤ 0) := by
  intro LC Mt Mean nx H b Z hZ hl Kc _ _ coinsOf Mof Hs F Yes Zs hLk hF hfull hcar hmeant
  refine linkFits_home b Z Kc _ Hs F Yes Zs hLk hF hfull hcar ?_
  intro i x r e r' e' c hy h1 h2 ρ _
  rw [dec_at_D hZ hl]
  exact H _ _ _ (hmeant i x r e r' e' hy h1 h2) (coinsOf c) ρ

end FlashProve

#print axioms FlashProve.linkFits_home
#print axioms FlashProve.linkFits_of_yes
