-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/HomeAccepted.lean: the link's verifier accepts the explicit prover of
homeExact, for public files in scope with a live description, at verifier messages that pass the
proof-of-work checks.
Terms of this folder: Johnson/LinkSim/Spec.lean.
Under Johnson/LinkSim/ no file calls homeSide_accepted; the heads of Home.lean, SpecHome.lean,
CompileFit.lean and Johnson/LinkSim/Spec.lean cite it.

What this file proves (homeSide_accepted). Fix b, and public files Z that are in scope and have a
live description. Take any structure of the three honest provers (Hs, of type ThreeProvers) whose link
prover is explicitLinkProver b Z, and with no fall at the link (F.Lk is empty). A fall is a further set of
verifier messages at which no acceptance is owed; unlike the abort set, it may depend on the
prover's coin (Falls, Johnson/Prover/All/OfHonest.lean). Then the four clauses on the link of HonFit
(Johnson/Prover/All/OfHonest.lean) hold, as linkFits_at states them and in its order. Here the
excepted set is the prover's abort set (withheld) together with the fall.
  1. The input oracles are the two encodings of the index.
  2. A verifier message whose proof-of-work bits, set to 0, lie in the excepted set, lies in it too.
  3. At every coin, the verifier accepts every transcript that is the prover's run up to its nonces,
     that passes the proof-of-work checks, and whose verifier messages lie outside the excepted set
     (AccLaw).
  4. At every coin, the excepted set has probability 0.
Clauses 3 and 4 are asked where Yes i x holds, and clause 3 where both seeds lie outside Zs. Yes and
Zs are bound by "for all", so the clauses hold in particular with Yes always true and Zs empty.

Why. Johnson/LinkSim/Spec.lean's limits say why exactness needs completeness of the same prover.
This file proves that the two statements speak of one term: the prover of homeExact
(Johnson/LinkSim/AtHome/Home.lean) is the prover whose acceptance linkFits_at proves.

How it fits. It is one call of linkFits_at (Johnson/Goal/Conditions/LinkFitsAt.lean) at explicitLinkProver b Z
(Johnson/LinkSim/AtHome/SpecHome.lean), through homeSide_is. It stands beside homeExact.

Sources. The statement's four clauses are linkFits_at's own, verbatim, at the coins' type Kc and the
map coinsFull (Johnson/Prover/Link/LinkCoin.lean), which are parameters there. The proof is that one
call, with homeSide_is between.

Limits. Acceptance is proved only for public files in scope with a live description. At other public
files nothing on acceptance is said.
That some public files are both in scope and live is not proved here; the library's two named sets
are both (open_zFull, open_zGap, AtFullSide/E2E/AtWrittenFiles.lean).
The four clauses are not all of HonFit: nothing is said about the other two sub-protocols' honest
provers.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.SpecHome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Iop (prRho)
open TypedOracleCompiler.Iop (RoundsQueryLayout)
open TypedOracleCompiler.Compile.Batch.Cms (batLC wLC)
open OnBytes.Prover (ThreeProvers Falls AccLaw)
open Johnson.Prover.Link (Kc coinsFull)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **Acceptance of explicitLinkProver b Z**: for public files in scope with a live description, the four
clauses of HonFit on the link hold for the explicit link prover, as linkFits_at states them. -/
theorem homeSide_accepted :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (Hs : ThreeProvers (homeR b Z).protocol) (F : Falls Hs) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
      (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed),
    Hs.Lk = explicitLinkProver b Z →
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
  fun b Z hZ hl Hs F Yes Zs h hF =>
    linkFits_at b Z hZ hl Kc coinsFull Hs F Yes Zs (h.trans (homeSide_is b Z)) hF

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.homeSide_accepted
