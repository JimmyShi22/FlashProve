-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file states no goal.
Johnson/Goal/Conditions/LinkFitsOne.lean: THE FOUR CLAUSES ON THE LINK OF HonFit
(Johnson/Prover/All/OfHonest.lean) AT THE INPUT homeR b Z, FROM ONE PREMISE: "the link's decision
accepts the honest view", in its own form.

Main names.
  linkFits_one    THE STATEMENT: extL, whL, accL and prL at the measure 0, as a conjunction in this
    order, each to the letter of HonFit's field.

What is asked. hyes: for every instance, stored strings and rows' polynomials that meet the seven
clauses of meant_home (Johnson/Goal/Conditions/LinkMeant.lean), everything else that the messages'
maker is handed, and all challenges: the description's decision at the two written keys accepts the
view of the maker's messages · the files are in scope and the description is live · the link's
structure of the honest side is linkRec (Johnson/Prover/Link/LinkFrame.lean) at the two encodings of
the index and at the maker handed the instance, the two encodings, their rows' polynomials and the
coin's image · no fall at the link. What the maker is handed beside these, the maker and the coin's
map are variables.

How. linkFits_of_yes (Johnson/Goal/Conditions/LinkFitsHome.lean) at full_full, carries_home
(Johnson/Goal/Conditions/LinkFitsPaid.lean) and meant_home.

Limits. hyes IS A PREMISE. A conjunction of four is no HonFit: nothing on the other two protocols'
honest sides. Which three provers are defined for (homeR b Z).protocol:
Johnson/Goal/Conditions/LinkFitsAt.lean, limit 4. accL is an AccLaw, so it speaks only of the
challenges that pass all proof-of-work checks (Johnson/Prover/Link/LinkYesStm.lean, common limit 2).
Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Goal.Conditions.LinkMeant

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
open VerifiableInference.Desc (fieldPrimeWord)
open _root_.Desc.K15 (frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)
open _root_.Iop (twoExternalStrings Rho)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (uL)

/- Lean compares these by their names. (Not the coding: its types are unfolded below.) -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **linkFits FROM ONE PREMISE.** -/
theorem linkFits_one :
  ∀ (LC : Type)
    (nx : RecFull × RecFull → (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str →
      ((frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → OnBytes.Slice.GE) →
      ((frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → OnBytes.Slice.GE) → LC → ℕ →
      List Fmt.Drawn → MsgV),
    (∀ (rr : (frS.lkR (recZ frS.P.T.l 29 1)).X0) (y : (frS.lkR (recZ frS.P.T.l 29 1)).E0.Str)
      (M₀ M₁ : (frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → OnBytes.Slice.GE),
      ((∀ ρ s, rr.1.2 (ρ, s) =
        ∑ j, (recZ frS.P.T.l 29 1).mat rr.1.1 s j *
          M₀ ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)) ∧
      (∀ ρ s, rr.2.2 (ρ, s) =
        ∑ j, (recZ frS.P.T.l 29 1).mat rr.2.1 s j *
          M₁ ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)) ∧
      ((frS.lkR (recZ frS.P.T.l 29 1)).tab y.1 =
        fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M₀ ρ)) ∧
      ((frS.lkR (recZ frS.P.T.l 29 1)).tab y.2 =
        fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M₁ ρ)) ∧
      (frS.lwR (recZ frS.P.T.l 29 1)).SameOn ((frS.ixR (recZ frS.P.T.l 29 1)).view M₀)
        ((frS.ixR (recZ frS.P.T.l 29 1)).view M₁) ∧
      (∀ p, (((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y p).2.all (· < fieldPrimeWord)) = true) ∧
      (∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
        ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y
          (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2048)) →
      ∀ (C : LC) (ρ : Rho (uL (ckP .two) dsFull)),
        (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP OnBytes.Params.recordPlan)).run
          (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 })
          (viewOf dsFull frS.P.T.a frD.xs (nx rr y M₀ M₁ C) y (drawnSL (ckP .two) dsFull ρ)) =
            true) →
    ∀ (b : PublicFiles → ℕ) (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (Kc : Type) [Fintype Kc] [Nonempty Kc] (coinsOf : Kc → LC)
      (Hs : ThreeProvers (homeR b Z).protocol) (F : Falls Hs) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
      (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed),
    Hs.Lk = linkRec (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (fun w => ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1))
      (fun w x c => nx x ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1)
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.1.1.1)))
          (tailWords frS w.2.1.1.2))
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.2.1.1)))
          (tailWords frS w.2.2.1.2))
        (coinsOf c)) →
    (∀ w x c, F.Lk w x c = ∅) →
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
  intro LC nx H b Z hZ hl Kc _ _ coinsOf Hs F Yes Zs hLk hF
  exact linkFits_of_yes LC
    (((frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → OnBytes.Slice.GE) ×
      ((frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → OnBytes.Slice.GE))
    (fun rr y M =>
      (∀ ρ s, rr.1.2 (ρ, s) =
        ∑ j, (recZ frS.P.T.l 29 1).mat rr.1.1 s j *
          M.1 ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)) ∧
      (∀ ρ s, rr.2.2 (ρ, s) =
        ∑ j, (recZ frS.P.T.l 29 1).mat rr.2.1 s j *
          M.2 ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)) ∧
      ((frS.lkR (recZ frS.P.T.l 29 1)).tab y.1 =
        fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M.1 ρ)) ∧
      ((frS.lkR (recZ frS.P.T.l 29 1)).tab y.2 =
        fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M.2 ρ)) ∧
      (frS.lwR (recZ frS.P.T.l 29 1)).SameOn ((frS.ixR (recZ frS.P.T.l 29 1)).view M.1)
        ((frS.ixR (recZ frS.P.T.l 29 1)).view M.2) ∧
      (∀ p, (((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y p).2.all (· < fieldPrimeWord)) = true) ∧
      (∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
        ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y
          (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2048))
    (fun rr y M C => nx rr y M.1 M.2 C) (fun rr y M h C ρ => H rr y M.1 M.2 h C ρ) b Z hZ hl Kc
    coinsOf
    (fun w =>
      (honestPolys frS
        (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.1.1.1)))
        (tailWords frS w.2.1.1.2),
      honestPolys frS
        (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.2.1.1)))
        (tailWords frS w.2.2.1.2)))
    Hs F Yes Zs hLk hF full_full (carries_home b Z)
    (fun i _ r e r' e' _ _ _ => meant_home b Z i r r' e e' _ _ rfl rfl)

end FlashProve

#print axioms FlashProve.linkFits_one
