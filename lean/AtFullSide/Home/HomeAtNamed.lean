-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Home/HomeAtNamed.lean: WHAT THE COMPLETENESS SIDE's STATEMENTS TAKE UNDER "the files are
in scope, are read, and protocolDataWellFormed accepts", AT THE TWO NAMED SETS OF PUBLIC FILES (VerifierAndGoals.storedPublicFiles,
VerifierAndGoals.zGap), UNDER NO OTHER PREMISE. IT STATES NO GOAL: statements and proofs; every proof is a
call of a statement of the main library at three facts that this side library holds.

WHAT IS CALLED OF THE SIDE LIBRARY: premises_zFull and premises_zGap
(AtFullSide/Bind/LiveAtNamed.lean): in scope, read, protocolDataWellFormed accepts, together. They rest on
theLive_zFull (AtFullSide/Top/LiveAtFull.lean), theLive_zGap (AtFullSide/Top/LiveAtPolicies.lean)
and VerifierAndGoals.filesRead (Johnson/Goal/Files/FilesReadProof.lean).

  named_three: at Z = storedPublicFiles or Z = zGap: in scope; read; protocolDataWellFormed accepts.
  lastFits_idle_named: THE LAST LIST OF NAMED HYPOTHESES (LastFits,
    Johnson/Goal/Conditions/HomeLast.lean) HAS A MEMBER THERE: by lastFits_idle
    (Johnson/Goal/Conditions/HomeIdle.lean). AT IDLE PARAMETERS: THEIR THREE PROVERS ABORT AT EVERY
    VERIFIER MESSAGE, AND THE NUMBER IS AT LEAST 3 (three_le_idleAlpha, the same file): NOTHING ON
    COMPLETENESS FOLLOWS. It shows that the list's three clauses on the files bar nothing there, and
    no more.
  linkFits_named: the four clauses of HonFit on the link's prover, at the written link's prover,
    there: the statement of linkFits_at (Johnson/Goal/Conditions/LinkFitsAt.lean) with its two
    premises on the files struck.
  caps_named, number_named: the three caps fit a word of 64 bits; the sum at these caps: caps_home
    and number_home (Johnson/Goal/Conditions/NumberAtHome.lean) there.

Why here. The three facts are shown in this side library, which is built with a larger thread stack
than the files under lean/Johnson/. Nothing in the main library imports a file of it. ONLY A BUILD
OF THE SIDE LIBRARY SHOWS A BREAK IN THIS FILE.

Limits, which are those of the theorems called. A YES OF protocolDataWellFormed IS NO SIGN THAT THE VERIFIER
ACCEPTS ANY PROOF, AND NONE THAT AN HONEST PROVER's PROOF IS ACCEPTED. AT THE WRITTEN COPIES, NOT AT
THE RELEASE's FILES: each of the two sets is three terms written in Ladder/Stored.lean: no Lean code
ties them to files in a folder or to files that a program writes; the example's weights are
synthetic. At the second hash function OnBytes.secondHashFunction, and at the constant in the digest's place,
not at the digest of these files. Many closed facts beneath are proved by evaluation in Lean's
kernel; no independent checker has replayed the side library. Nothing on soundness, on completeness
or on any other property.
Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Bind.LiveAtNamed
import Johnson.Goal.Conditions.HomeIdle
import Johnson.Goal.Conditions.LinkFitsAt
import Johnson.Goal.Conditions.NumberAtHome

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace AtFullSide.Home
open FlashProve
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
open Johnson.Prover.Link (MsgV linkRec viewOf LCoins linkNext linOf)
open VerifiableInference.Desc (fieldPrimeWord)
open _root_.Desc.K15 (frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)
open _root_.Iop (twoExternalStrings Rho)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (uL)
open OnBytes.Prover (alphaAll)

/- Lean compares these by their names. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows
  storedPublicFiles zGap

/-- **In scope, read, protocolDataWellFormed accepts: together, at either named set of files.** -/
theorem named_three {Z : PublicFiles} (hZ : Z = storedPublicFiles ∨ Z = zGap) :
    InScope Z = true ∧ (∃ pp, readFiles Z = .ok pp) ∧ protocolDataWellFormed (asDescriptionFiles Z) = true := by
  rcases hZ with rfl | rfl
  · exact AtFullSide.Tie.premises_zFull
  · exact AtFullSide.Tie.premises_zGap

/-- **THE LAST LIST HAS A MEMBER AT EITHER NAMED SET OF FILES**, under no other premise. At idle
letters: the number is at least 3: nothing on completeness follows. -/
theorem lastFits_idle_named (b : PublicFiles → ℕ) (x₀ : (Z : PublicFiles) → (homeR b Z).Instance) {Z : PublicFiles}
    (hZ : Z = storedPublicFiles ∨ Z = zGap) :
    ∃ pp, LastFits (idleArgs b Z x₀) Z pp (idleAlpha b Z) :=
  let ⟨sc, ⟨pp, hr⟩, lv⟩ := named_three hZ
  ⟨pp, lastFits_idle b Z x₀ hr sc lv⟩

/-- **The four clauses on the link's prover, at the written link's prover, at either named set of
files.** -/
theorem linkFits_named :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles), (Z = storedPublicFiles ∨ Z = zGap) →
    ∀ (Kc : Type) [Fintype Kc] [Nonempty Kc] (coinsOf : Kc → LCoins)
      (Hs : ThreeProvers (homeR b Z).protocol) (F : Falls Hs) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
      (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed),
    Hs.Lk = linkRec (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (fun w => ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1))
      (fun w x c => linkNext frP frS 97
        (linOf x ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1)
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.1.1.1)))
            (tailWords frS w.2.1.1.2))
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.2.1.1)))
            (tailWords frS w.2.2.1.2)))
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
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c) ≤ 0) :=
  fun b Z hZ => linkFits_at b Z (named_three hZ).1 (named_three hZ).2.2

/-- **The three caps fit a word of 64 bits**, at either named set of files. -/
theorem caps_named {Z : PublicFiles} (hZ : Z = storedPublicFiles ∨ Z = zGap) :
    (∀ j, capT (sAt Z) j < 2 ^ 64) ∧ (∀ j, capL j < 2 ^ 64) ∧ ∀ j, capB (sAt Z) j < 2 ^ 64 :=
  caps_home Z (named_three hZ).1 (named_three hZ).2.2

/-- **The sum at these caps**, at either named set of files. -/
theorem number_named (b : PublicFiles → ℕ) {Z : PublicFiles} (hZ : Z = storedPublicFiles ∨ Z = zGap)
    (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) :
    alphaAll (Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []).queryLayout (capT (sAt Z)) capL
      (capB (sAt Z)) ζ₁ ζ₂ δT δL δB ≤
      71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + (ζ₁ + ζ₂) + (δT + δL + δB) :=
  number_home b Z (named_three hZ).1 (named_three hZ).2.2 ζ₁ ζ₂ δT δL δB

end AtFullSide.Home
