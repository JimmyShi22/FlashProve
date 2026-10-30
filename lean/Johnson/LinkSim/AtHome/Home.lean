-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/Home.lean: homeExact, on the link proof's honest prover and simulator, and
the link's clauses among the premises of index privacy.
Terms of this folder: Johnson/LinkSim/Spec.lean.

The result. homeExactAt (HomeExactAll.lean) proves that the link proof's interactive protocol, at
the library's full-size parameter set (dsFull), is perfect honest-verifier zero knowledge: error 0,
an explicit honest prover (explicitLinkProver b Z), an explicit simulator (homeSim Z). For every index, every
encoding randomness and OOD seed of both tables, and every verifier message, the prover's whole
disclosed view has exactly the simulator's distribution. As the definition has it (Honest.HVZK,
Iop/InteractiveOracleProof.lean), the simulator is given the instance, the verifier's messages and the symbols of the
input oracles at the queried positions. Here the instance is the two tables' out-of-domain (OOD)
samples, and the input oracles are the two encodings of the index, queried at no more than 62
positions each (home_beside, HomeTies.lean). So what the prover discloses to an honest verifier adds
nothing to what these samples and symbols already disclose. It holds for all public files Z, and no
premise on sizes or on the honest run is left. No verifier message is excepted: the prover never
aborts (home_withheld, TwoViews.lean). For public files in scope with a live description, the link's
verifier accepts this same prover at every verifier message that passes the proof-of-work checks
(homeSide_accepted, HomeAccepted.lean). What it sends does not ignore the index (two_plains,
TwoPlains.lean).

This file's own theorems. homeExact states the same equation through ExactOff
(Johnson/LinkSim/Spec.lean), the form that the premises of index privacy take; homeExactAt follows
from it (Johnson/LinkSim/AtHome/HomeExactAll.lean, which also says what Z still changes).
linkFieldsHome proves Spec.linkFieldsHome (Johnson/LinkSim/AtHome/SpecHome.lean): the same result,
packed for those premises. For every structure of parameters whose honest link prover is
explicitLinkProver b Z and whose link has one constant run value, the four clauses on the link (LinkFields,
Johnson/LinkSim/Spec.lean) hold at homeSim Z, with both of the link's error terms 0. SpecHome.lean's
limits say which of the four clauses has content.

How it fits. This file serves the conditional theorem on index privacy (Spec.wholeKeyPrivacy,
Johnson/WholeKey/Statement.lean): Johnson/LinkSim/AtHome/CompileFit.lean uses linkFieldsHome,
through linkFields_withLaid (Johnson/LinkSim/AtHome/CompileLaid.lean), to put this prover and
simulator into its premises. E2E/LinkLaidPrivacy.lean combines this result with the encoder's: for
public files in scope, and within its bounds on the number of copies, the number of requests per
copy and the sampled bits of a leaf's salt, all premises of index privacy hold with this link prover
and two placeholder provers (premW_laid). At one copy and search limits of 2 ^ 40 that instance is
not vacuous: for public files in scope with a live description its proofs are produced
(linkLaidEight, E2E/LinkLaidAllAtOnce.lean).

How it is proved. homeExact is exactOfText (Johnson/LinkSim/AtText/Exact.lean), applied with the
connecting lemmas of Johnson/LinkSim/AtHome/HomeTies.lean and with coinsCancel
(Johnson/LinkSim/AtText/CoinsAdd.lean). It also uses home_upTo
(Johnson/LinkSim/AtHome/RoadCloses.lean) at linkShiftIn (Johnson/LinkSim/AtText/LinkShift.lean).
Each of these is explained in its own file's head. linkFieldsHome is roadCloses, the lemma that
joins three statements into Spec.linkFieldsHome, applied to its three premises, which are theorems:
linkShiftIn, exactOfText and fieldsZero (Johnson/LinkSim/Bridge.lean).

Main names (namespace OnBytes.LinkSim.AtHome).
  homeExact        ExactOff (explicitLinkProver b Z) (validLk …) (homeSim Z) at the empty set.
  linkFieldsHome   the four clauses, with both of the link's error terms 0, for every such
                   structure of parameters.

Limits, the weightiest first. The last three are usual for an interactive oracle proof.
- It is not a statement that the index is hidden: the OOD samples and the queried symbols depend on
  the index. That they disclose nothing of it, within a budget of queries over all links and
  sessions, is a separate premise of index privacy (PremW: reads, budget₀, budget₁). It is proved
  for this same encoder, for public files in scope, at up to 44,040,191 queried positions per table
  (E2E/PremisesAtFiles.lean). E2E/LinkLaidPrivacy.lean combines the two (see "How it fits"); this
  folder does not.
- It covers one of the three sub-protocols. For the other two this folder defines no simulator, and
  at this protocol every proved instance of these premises has placeholder provers.
- Acceptance is proved only for public files in scope with a live description; the library's two
  named sets are both (AtFullSide/E2E/AtWrittenFiles.lean). Elsewhere completeness is not proved.
- It is stated at one parameter set (dsFull) and at one digest. The input's type of indices and its
  protocol structure do not depend on the digest (homeR_I_at, homeR_L_at, AtHome/HomeDigest.lean),
  and by inspection homeExact's statement reads nothing else of the input; the digest matters only
  after hashing (Spec.lean, "homeR b Z").
- The verifier is honest: its messages are fixed first and all given to the simulator, so nothing
  here bears on a verifier that chooses.
- This is the interactive form, before any hashing.
- The prover is a Lean term with uniform, fresh coins, tied to no program; the simulator's running
  time is not modelled.

Tests and notes. None of these bounds the theorem.
- No run of the prover's or of the simulator's algorithm is evaluated at any size. That these
  definitions are the protocol's link prover rests on the acceptance theorem, on two_plains and on
  inspection.
- The negative test short_tail_fails (Johnson/LinkSim/AtText/ShortTail.lean) removes the last entry
  of one row's tail from the coins. It proves that the prover's and the simulator's algorithms can
  then no longer be made equal by a change of the coins. It covers only the messages up to the first
  Merkle tree, and it rests on a premise that has not been proved for any concrete data.
- The sizes hold with nothing to spare: at every stage as many positions are opened as a row's tail
  is long (fr_tails, Johnson/LinkSim/AtText/SeamAtFull3.lean: 97, 49, 49, 50 and 40). These are
  positions of the prover's own oracle messages, not the 62 of each input oracle. With one more
  opened position at round 16 or at round 40, the test on sizes that the proof relies on (fitsOk)
  rejects (fr_fitsNo16, fr_fitsNo: checked by evaluation); "stage" and "tail" are in
  Johnson/LinkSim/AtText/Defs.lean's terms.
- In a round with a proof-of-work check, the explicit prover sends the nonce 0 without searching.
  The disclosed view holds that constant, on both sides of the equation; the verifier's decision
  reads no nonce (shown_SL, Johnson/Prover/Link/LinkFrame.lean). Acceptance is proved only at
  verifier messages that pass the checks. The hashed prover finds its nonce by a search that depends
  on the hash function's answers; that nonce stands in the hashed proof and is not covered here.
- The library's own predicate Honest.HVZK holds at error 0 (homeHVZK, AtHome/HomeHVZK.lean), by
  Honest.HVZK.of_exact.
- The other clauses of these premises that concern the link's coins and compilation data are not
  proved here; they are proved, at parameters that are substituted there by choice, in
  Johnson/LinkSim/AtHome/CompileHome.lean.

Sources. A statement here is covered by the note on sources in the head of Spec.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.RoadCloses
import Johnson.LinkSim.AtText.LinkShift
import Johnson.LinkSim.AtText.Exact

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
open Johnson.Prover.Link (keysOf Kc coinsFull frFirst frRest)
open _root_.Desc.K15 (frP)
open OnBytes.LinkSim (validLk ExactOff)
open OnBytes.LinkSim.AtText (coinsCancel)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- For the explicit honest prover and the explicit simulator, ExactOff holds with the empty
exceptional set. The set Hid, which ExactOff also excepts, is empty: it is part of the prover's
abort set, which is empty (home_withheld, TwoViews.lean). homeExactAt (HomeExactAll.lean) states the
equation with nothing excepted. -/
theorem homeExact (b : PublicFiles → ℕ) (Z : PublicFiles) (ok : (homeR b Z).Index → Prop)
    (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop) :
    ExactOff (explicitLinkProver b Z) (validLk (homeR b Z).protocol ok Gs) (homeSim Z) ∅ :=
  Seam.exactOfText (ckP .two) dsF frS.P.T.a xsF _ (dataAtFiles flashProveData Z).dec frP frS 97 Kc coinsFull
    addKc keysOf (HomeWt b Z) (homeExt b Z) (homeIn b Z) (validLk (homeR b Z).protocol ok Gs) frFirst
    frRest home_stages home_want home_stored (fun k k' d => coinsCancel frS _ k k' d)
    (fun w x _ => home_keys b Z w x) (fun w x _ bb pos hp => home_cols b Z w x bb pos hp)
    (fun w x hv ρ => home_upTo AtText.linkShiftIn b Z ok Gs w x hv ρ)

/-- Proves Spec.linkFieldsHome: the four link clauses for explicitLinkProver b Z and homeSim Z, with both
error terms 0. -/
theorem linkFieldsHome : Spec.linkFieldsHome :=
  roadCloses AtText.linkShiftIn Seam.exactOfText OnBytes.LinkSim.fieldsZero

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.homeExact
#print axioms OnBytes.LinkSim.AtHome.linkFieldsHome
