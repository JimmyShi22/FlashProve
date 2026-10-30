-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/SpecHome.lean: the explicit link prover and simulator for homeR b Z.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has. This file defines the link proof's honest prover (explicitLinkProver b Z) and its
simulator (homeSim Z) at the library's full-size parameter set (dsFull), and states what Home.lean
proves of the two (Spec.linkFieldsHome). explicitLinkProver computes its messages from the index, both tables'
encoding randomness and a uniform coin. By unfolding it is the very term whose acceptance
linkFits_at proves for public files in scope with a live description (homeSide_is;
homeSide_accepted, HomeAccepted.lean). homeSim has one parameter, the public files Z: no index, no
table's randomness, no private input and no data of the prover is among its parameters. When it runs
it is given what the definition gives a simulator (Honest.HVZK, Iop/InteractiveOracleProof.lean): the instance, the
verifier's messages and the symbols of the input oracles at the queried positions. The statement: if
a structure of parameters has explicitLinkProver b Z as link prover and one constant run value for the link,
the four clauses (LinkFields, Spec.lean) hold at homeSim Z, both error terms 0. It holds for every
range of indices and every set of OOD seeds, and asks nothing on sizes, on the honest run, or on the
public files.

The main theorem in its plainest form is homeExactAt (Johnson/LinkSim/AtHome/HomeExactAll.lean).

Detail of the statement. Spec.linkFieldsHome is proved as linkFieldsHome in
Johnson/LinkSim/AtHome/Home.lean. homeR b Z is defined in Johnson/Goal/Conditions/HomeAtWider.lean;
it, "run value", "in scope" and "live" are in Spec.lean's terms. LinkFields is taken at the
compilation data of homeR b Z ((homeR b Z).queryLayout). In the Lean the constant run value v₀ is asked twice:
of what a coin gives (rvL) and of what the plain parts give (pvL). The verifier's decision enters
none of the four clauses.

How the simulator works. homeSim Z is given the instance (the two OOD samples), the verifier's
messages and the queried symbols of the two tables. From these it builds the data of its algorithm:
the two keys, the stored columns at the queried positions, and 0 for all rows of both tables (inOf,
AtText/SeamInput.lean). It samples one uniform coin of the prover's own type Kc and runs the
prover's algorithm linkAll on that data, against the verifier's messages (simAll, AtText/Defs.lean).
It replaces one element of the output, the one that the base case's first round sends, by tauStar,
which is computed so that the verifier's last equation holds. Its output is the disclosed view of
that run (simOfStrat, SpecForm.lean). Why the two distributions are equal: at each verifier message
there is a shift of the coins, from c to c + s(c), after which the two algorithms disclose the same
(linkShiftIn, AtText/LinkShift.lean). The shift can be undone, so it is a bijection of the finite
type of coins, and uniform coins then give one distribution (UpToShift.law_eq, UpTo.lean).

Detail of the simulator. homeSim Z is simLink (Johnson/LinkSim/AtText/SpecExact.lean) at concrete
constants: the link protocol's parameters; the full-size parameters frP and frS and the number 97;
the coins Kc with coinsFull; and keysOf, which rewrites the instance's two OOD samples as two keys
(Johnson/LinkSim/AtText/Defs.lean's terms; the rest in Spec.lean's). It draws one uniform coin of
the type Kc.

Detail of the honest prover. explicitLinkProver b Z is one definition: linkSide
(Johnson/LinkSim/AtText/SpecExact.lean) at the same frP, frS and 97, the coins Kc with coinsFull,
the two encodings of the index (homeExt) and the prover's data (homeIn). By unfolding it is the
generic link prover linkRec (Johnson/Prover/Link/LinkFrame.lean) at explicit messages
(linkNext frP frS 97) (homeSide_is). linkFits_at proves its acceptance for public files in scope
with a live description, at verifier messages that pass the proof-of-work checks.

How it fits. This is the third of the three steps that Spec.lean describes: the link's clauses at
homeR b Z. It serves the conditional theorem on index privacy (Spec.wholeKeyPrivacy,
Johnson/WholeKey/Statement.lean), whose premises (PremW) contain these clauses.

Main names (namespace OnBytes.LinkSim.AtHome).
  HomeWt, homeExt, homeIn   the link's private input, the two encodings of the index, and the
                            honest prover's data.
  explicitLinkProver, homeSide_is     the explicit honest prover, and its unfolded form.
  homeSim                   the explicit simulator.
  Spec.linkFieldsHome       the statement, proved in Home.lean.

Limits. Of the four clauses one has content: the clause on the simulator, whose core is homeExact
(Home.lean). The other three hold by unfolding, because the prover's abort sets are empty by
definition, and by the statement's own premise on run values. Two premises are left: that the link's
honest prover is explicitLinkProver b Z, and that the link has one constant run value. Two structures of
parameters with this honest prover are proved to exist, and they serve two ends. premW_laid
(E2E/LinkLaidPrivacy.lean), for public files in scope, and within its bounds on the number of
copies, the number of requests per copy and the sampled bits of a leaf's salt, meets all premises of
index privacy, with placeholder provers that send fixed messages for the other two protocols. For
public files that also have a live description, at one copy and search limits of 2 ^ 40, its proofs
are produced (linkLaidEight, E2E/LinkLaidAllAtOnce.lean). link_all_met (CompileFiller.lean) is a
smaller guard inside this folder: some structure of parameters has this prover and meets all
eighteen clauses on the link; it is no instance of PremW (Notes). It is not a statement that the
index is hidden; that limit, and those on the verifier, on hashing, on the three provers and on
programs, are told once, in Home.lean's head.
The statement is at the library's full-size parameter set (dsFull) alone, and at one fixed digest
(see Home.lean's limits).
Nothing is said here about the other clauses of these premises that concern the link's coins and
compilation data.

Notes.
- On link_all_met alone: its placeholder provers abort at every verifier message, and at its numbers
  PremW as a whole is false (not_premW_fillerNums, Johnson/LinkSim/AtHome/CompileFillerNot.lean).
  Neither holds of premW_laid.
- Where the verifier's messages lie in a link prover's abort set, the scheme for which index privacy
  is stated publishes no proof string for that link and still publishes the rest of the key. Whether
  the programs' committer does the same is not said here. For explicitLinkProver b Z the abort set is empty
  (home_withheld, Johnson/LinkSim/AtHome/TwoViews.lean), so this cause does not arise for this
  prover. A compiled run that returns no proof string is another cause; nothing is said of it here.

Sources. A statement here is covered by the note on sources in the head of Spec.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecExact
import Johnson.Goal.Conditions.LinkFitsAt
import Johnson.Prover.Link.LinkCoin

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
open _root_.Run (ckP)
open OnBytes.Prover (ThreeProvers)
open OnBytes.WholeKey (AtRecs)
open PV.EntryFive (dsF xsF)
open Johnson.Prover.Link (linkRec LCoins LIn linkNext linOf keysOf Kc coinsFull)
open _root_.Desc.K15 (frP)
open _root_.Iop (twoExternalStrings Honest)
open _root_.Run.PQ (SgX)
open _root_.Compile.Lifetime (SimOf)
open OnBytes.LinkSim (LinkFields)
open OnBytes.LinkSim.Seam (simLink linkSide)

/-- The link's private input at homeR b Z: the index, and for each of the two tables its randomness
and its seed. -/
abbrev HomeWt (b : PublicFiles → ℕ) (Z : PublicFiles) : Type :=
  (homeR b Z).Index × ((homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed) ×
    ((homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed)

/-- The two encodings of the index, one with each table's randomness. -/
def homeExt (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str :=
  ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1)

/-- The honest prover's data: the instance, the two encodings, and the polynomials of their rows
(402653181: Spec.lean's terms). -/
def homeIn (b : PublicFiles → ℕ) (Z : PublicFiles) (w : HomeWt b Z) (x : RecFull × RecFull) : LIn frS :=
  linOf x (homeExt b Z w)
    (honestPolys frS
      (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.1.1.1)))
      (tailWords frS w.2.1.1.2))
    (honestPolys frS
      (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.2.1.1)))
      (tailWords frS w.2.2.1.2))

/-- The explicit honest link prover for homeR b Z. -/
def explicitLinkProver (b : PublicFiles → ℕ) (Z : PublicFiles) :
    Honest (linkProtocolOfRoundData (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec) (HomeWt b Z) :=
  linkSide (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec frP frS 97 Kc coinsFull
    (homeExt b Z) (homeIn b Z)

/-- By unfolding, explicitLinkProver b Z is the term that linkFits_at asks of its honest prover, at the coins
Kc and coinsFull. homeSide_accepted (Johnson/LinkSim/AtHome/HomeAccepted.lean) uses it there. -/
theorem homeSide_is (b : PublicFiles → ℕ) (Z : PublicFiles) :
    explicitLinkProver b Z = linkRec (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (fun w => ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1))
      (fun w x c => linkNext frP frS 97
        (linOf x ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1)
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.1.1.1)))
            (tailWords frS w.2.1.1.2))
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.2.1.1)))
            (tailWords frS w.2.2.1.2)))
        (coinsFull c)) := rfl

/-- The explicit simulator for the link at homeR b Z; its only parameter is the public files Z. -/
def homeSim (Z : PublicFiles) : SimOf (linkProtocolOfRoundData (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec) :=
  simLink (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec frP frS 97 Kc coinsFull keysOf

/-- Statement only; proved as linkFieldsHome in Johnson/LinkSim/AtHome/Home.lean. The four link
clauses for explicitLinkProver b Z and homeSim Z, with both error terms 0. -/
def Spec.linkFieldsHome : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles)
    (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits) (v₀ : a.RV),
    a.Hs.Lk = explicitLinkProver b Z → (∀ κ, a.rvL κ = v₀) → (∀ π, a.pvL π = v₀) →
    ∀ (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop),
      LinkFields a (homeSim Z) (homeR b Z).queryLayout ok Gs 0 0

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.homeSide_is
