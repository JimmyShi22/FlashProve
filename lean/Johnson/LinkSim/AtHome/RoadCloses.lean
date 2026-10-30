-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/RoadCloses.lean: three statements imply the link's clauses at homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file proves.

    roadCloses : Spec.linkShiftIn → Spec.exactOfText → Spec.fieldsZero → Spec.linkFieldsHome

In words, suppose three things.
  1. The prover's algorithm (linkAll) and the simulator's algorithm (simAll) disclose the same
     (shownOf: the rounds and the groups, not the trees) after a shift of the coins, from c to
     c + s(c), where s(c) can be recovered from the shifted coin. The coins and what is added to
     them lie in the places of the finite type of coins: they are zero outside the arguments that
     this type fills (Spec.linkShiftIn, Johnson/LinkSim/AtText/SpecShiftIn.lean), under its premises
     on sizes and on the honest run.
  2. That gives exactness at all verifier messages (Spec.exactOfText,
     Johnson/LinkSim/AtText/SpecExact.lean).
  3. Exactness at all verifier messages, with no abort that depends on the private input, gives the
     four clauses with both of the link's error terms 0 (Spec.fieldsZero,
     Johnson/LinkSim/Spec.lean), with the clauses on the input oracles and the run values as
     premises.
Then these four clauses hold at homeR b Z, for the explicit honest prover and the explicit simulator
(Spec.linkFieldsHome, Johnson/LinkSim/AtHome/SpecHome.lean).

So the statements proved in other files fit together into linkFieldsHome. Each premise has its
theorem elsewhere, and Johnson/LinkSim/AtHome/Home.lean applies roadCloses to them (linkFieldsHome).

How it fits. It is the last step of the proof of linkFieldsHome in Home.lean; home_upTo is also used
there, in the proof of homeExact.

What is used between the three. home_upTo, proved here from lemmas of other files, draws the first
statement's conclusion on the finite type of coins from Spec.linkShiftIn, at every valid private
input and all verifier messages (Johnson/LinkSim/AtHome/HomeTies.lean gives its premises;
Johnson/LinkSim/AtText/CoinsDown.lean the map of the coins). In home_upTo, as in premise 7 of
Spec.exactOfText, the simulator's algorithm runs at the same, honest data as the prover's. The
simulator homeSim Z itself runs it at data made of the instance and the symbols read alone, and the
two runs give the same output (simOfAns, Johnson/LinkSim/AtText/SeamInput.lean; simReads,
Johnson/LinkSim/AtText/SimReads.lean). The clause on run values holds by the conclusion's own two
premises, that the link's run value is one constant; nothing is proved there.

Main names (namespace OnBytes.LinkSim.AtHome): addKc, home_upTo, roadCloses.

Limits.
It is an implication: by itself this file proves neither its premises nor its conclusion. The three
premises are theorems: linkShiftIn (AtText/LinkShift.lean), exactOfText (AtText/Exact.lean) and
fieldsZero (Bridge.lean). The conclusion is linkFieldsHome (AtHome/Home.lean). Beneath
Spec.linkShiftIn stand four more statements (Johnson/LinkSim/AtText/SpecStage.lean,
Johnson/LinkSim/AtText/SpecShiftIn.lean; proved: bodyShiftOr and walkSame in AtText/Induct.lean,
frontShift and frontWalk in AtText/LinkShift.lean); beneath Spec.exactOfText, one
(Spec.exactOfShift, Johnson/LinkSim/SpecForm.lean; proved in Bridge.lean).

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.HomeTies
import Johnson.LinkSim.AtText.CoinsDown

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open PV.EntryFive (dsF xsF)
open Johnson.Prover.Link (LCoins linkAll keysOf Kc coinsFull frFirst frRest drawsOf)
open _root_.Desc.K15 (frP p12Of)
open _root_.Iop (twoExternalStrings Rho)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (SOf drawnSL)
open OnBytes.LinkSim (validLk UpToShift)
open OnBytes.LinkSim.AtText (shownOf simAll addLink downToCoins coinsCancel)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- The sum of two coins of the finite type, field by field. -/
abbrev addKc : Kc → Kc → Kc := addLink frS (p12Of frP).nums.stages

/-- **From the statement at the level of the algorithms' outputs to its conclusion on the finite
type of coins**, at every valid private input and instance and all verifier messages. -/
theorem home_upTo (h : AtText.Spec.linkShiftIn) (b : PublicFiles → ℕ) (Z : PublicFiles)
    (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop) (w : HomeWt b Z)
    (x : RecFull × RecFull) (hv : validLk (homeR b Z).protocol ok Gs w x)
    (ρ : Rho (_root_.Run.Twin.up (SOf (ckP .two) dsF))) :
    UpToShift addKc
      (fun k => shownOf (linkAll frP frS 97 (homeIn b Z w x) (coinsFull k)
        (drawsOf (drawnSL (ckP .two) dsF ρ.2))))
      (fun k => shownOf (simAll frP frS 97 (homeIn b Z w x) (coinsFull k)
        (drawsOf (drawnSL (ckP .two) dsF ρ.2)))) :=
  downToCoins frP frS (by rw [home_stages]; exact List.cons_ne_nil _ _) _ _
    (h frP frS 97 (homeIn b Z w x) _ (home_sizes ρ) (home_claim b Z ok Gs w x hv ρ))

/-- **The implication.** Its three premises are taken here, not proved; Home.lean supplies their
proofs. -/
theorem roadCloses (h1 : AtText.Spec.linkShiftIn) (h2 : Seam.Spec.exactOfText)
    (h3 : OnBytes.LinkSim.Spec.fieldsZero) : Spec.linkFieldsHome := by
  intro b Z a v₀ hLk hrv hpv ok Gs
  refine h3 _ _ 256 (homeR b Z).protocol _ _ _ a (homeSim Z) (homeR b Z).queryLayout ok Gs ?_ ?_ ?_ ?_
  · rw [hLk]
    exact h2 (ckP .two) dsF frS.P.T.a xsF _ (dataAtFiles flashProveData Z).dec frP frS 97 Kc coinsFull addKc
      keysOf (HomeWt b Z) (homeExt b Z) (homeIn b Z) (validLk (homeR b Z).protocol ok Gs) frFirst frRest
      home_stages home_want home_stored (fun k k' d => coinsCancel frS _ k k' d)
      (fun w x _ => home_keys b Z w x) (fun w x _ bb pos hp => home_cols b Z w x bb pos hp)
      (fun w x hv ρ => home_upTo h1 b Z ok Gs w x hv ρ)
  · intro w x
    rw [hLk]
    rfl
  · intro i r e r' e'
    rw [hLk]
    rfl
  · intro i u u' κ ρ _ _
    exact (hpv _).trans (hrv κ).symm

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.home_upTo
#print axioms OnBytes.LinkSim.AtHome.roadCloses
