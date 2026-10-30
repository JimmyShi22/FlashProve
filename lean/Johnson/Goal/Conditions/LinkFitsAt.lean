-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/LinkFitsAt.lean: HonFit's four fields on the link hold for the link of homeR
b Z at the explicit honest link prover, if the public files pass InScope and protocolDataWellFormed and no further
challenges are excepted at the link (linkFits_at).
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

What this file has. linkFits_at. Take any b and any public files Z with InScope Z = true and protocolDataWellFormed
(asDescriptionFiles Z) = true. Take any finite non-empty type of coins Kc with any map coinsOf : Kc → LCoins,
any three provers Hs, one for each protocol of (homeR b Z).protocol (ThreeProvers: three values of the library's
structure Honest; homeR: Johnson/Goal/Conditions/HomeAtWider.lean), any families F of further
excepted sets of challenges (Falls), any predicate Yes and any sets of seeds Zs (what these four are
for: HomeLast.lean, clause honest). Suppose two things. First, the link's prover Hs.Lk is linkRec
(Johnson/Prover/Link/LinkFrame.lean) at the decision (dataAtFiles flashProveData Z).dec, at the two encodings of
the index, and at linkNext frP frS 97 (Johnson/Prover/Link/LinkAll.lean) given the instance, the two
encodings, their honest row polynomials and coinsOf c. Second, F.Lk is empty at every argument: no
further challenges are excepted at the link ("no fall"). Then four statements hold, as a conjunction
in this order. Each is HonFit's field (Johnson/Prover/All/OfHonest.lean) verbatim, at homeR b Z's
protocol structure protocol, annotation linkRoundSplits and compilation data queryLayout, and at pL := 0.
  extL  the honest prover's two input oracles are the two encodings of the index.
  whL   if ρ with its proof-of-work bits set to 0 lies in the abort set or in F.Lk, then so does ρ.
  accL  where Yes i x holds and the two seeds lie outside Zs: AccLaw (Johnson/Prover/Law/Defs.lean)
        for the link of homeR b Z (batLC, wLC) at the two OOD samples, the two encodings and the
        honest prover's strategy at every coin c, with B the union of the abort set and F.Lk.
  prL   where Yes i x holds, that union has measure at most 0.
Under these conditions the abort set (withheld) is empty, by the condition on the link's prover
alone (linkRec_withheld, Johnson/Prover/Link/LinkFrame.lean: linkRec's abort set is empty at every
input); prL itself says: measure at most 0. So the measure is 0: the explicit honest link prover is
accepted at all challenges that pass the proof-of-work checks. Yes and Zs are
arbitrary. So, given any instance x, this holds at every index, all encoding randomness (the
encoder's second argument; a free variable here), all seeds, every coin c and any map coinsOf. No
premise on the decision is left. What the number 97 is: LinkYesStm.lean.

How it fits. The proof is linkFits_one (Johnson/Goal/Conditions/LinkFitsOne.lean) at link_yes
(Johnson/Prover/Link/LinkJoinF.lean); Meant's constructor makes the structure from the seven
clauses. dsF and xsF in the statement are the dsFull and frD.xs of link_accLaw
(Johnson/Prover/Link/LinkAccept.lean), by unfolding: Lean accepts full_full
(Johnson/Goal/Conditions/LinkFitsPaid.lean), which is stated at dsF and xsF, in link_accLaw's proof.
The clause "honest" of LastFits asks HonFit at every d, at yesAt and at its arguments' own sets of
seeds. LastFits is the one hypothesis of completeOn_last (Johnson/Goal/Conditions/HomeLast.lean).
linkFits_named (AtFullSide/Home/HomeAtNamed.lean) is linkFits_at with its two premises on Z proved,
at the written copies of the two named sets of files. This file states no goal.

Limits. 1. linkFits_at has four conditions. The files are in scope (InScope, Ladder.lean). protocolDataWellFormed
accepts them. The link's prover is linkRec at linkNext, as above. There is no fall at the link: F.Lk
is empty. In the condition on the link's prover the honest row polynomials are taken at numsRef
(Johnson/Flat/ThreeFull.lean): a written pair of numbers, which does not depend on Z; that they are
the numbers of the full-size parameter file is not shown there (its Limits) and is no premise here.
2. What InScope and protocolDataWellFormed test, and at which files protocolDataWellFormed is proved to accept:
Johnson/Goal/Conditions/LinkDecAt.lean; Johnson/Goal/Conditions/HomeLast.lean, limit 4.
3. accL is an AccLaw, so it speaks only of the challenges that pass all proof-of-work checks (common
limit 2).
4. These are all four of HonFit's fields on the link. A conjunction of four is no HonFit, which has
fourteen fields: the other ten are not proved here, and nothing is proved here on the other two
protocols' provers. Under Johnson/Prover/, Johnson/Goal/ and AtFullSide/ no three provers (ThreeProvers) for
(homeR b Z).protocol are defined with this link prover. The triple that is defined there for that protocol, with
its falls, is idle (idleHs, Johnson/Goal/Conditions/HomeIdle.lean); the structure's own fields honestOfflineProver,
honestLinkProver, honestOnlineBatchProver are silent placeholders (theProvers, Johnson/Goal/Description/Named.lean).
The coin's type and its map are variables: no finite type is fixed here. One such type and map: Kc,
coinsFull (Johnson/Prover/Link/LinkCoin.lean).
Nothing on soundness. Nothing on what any value discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.LinkFitsOne
import Johnson.Prover.Link.LinkJoinF

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
open Johnson.Prover.Link (MsgV linkRec viewOf LCoins linkNext linOf)
open VerifiableInference.Desc (fieldPrimeWord)
open _root_.Desc.K15 (frP linkDeclaredRounds linkRoundsMatchPlan linkDescriptionAt)
open _root_.Iop (twoExternalStrings Rho)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (uL)

/- Lean compares these by their names. (Not the coding: its types are unfolded below.) -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **HonFit's four fields on the link (extL, whL, accL, prL at 0), for the link of homeR b Z at the
explicit honest link prover.** Conditions: InScope, protocolDataWellFormed, Hs.Lk is linkRec at linkNext, F.Lk is
empty. accL is an AccLaw: it speaks only of the challenges that pass all proof-of-work checks. -/
theorem linkFits_at :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
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
          ((homeR b Z).protocol.recOf i r e, (homeR b Z).protocol.recOf i r' e') c) ≤ 0) := by
  intro b Z hZ hl Kc _ _ coinsOf Hs F Yes Zs hLk hF
  exact linkFits_one LCoins (fun rr y M₀ M₁ C => linkNext frP frS 97 (linOf rr y M₀ M₁) C)
    (fun rr y M₀ M₁ h C ρ => Johnson.Prover.Link.link_yes rr y M₀ M₁
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩ C ρ)
    b Z hZ hl Kc coinsOf Hs F Yes Zs hLk hF

end FlashProve

#print axioms FlashProve.linkFits_at
