-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SpecExact.lean: the link proof's simulator as an explicit term of the
library's type of simulators, the honest prover against which it is held, and the statement that
joins the level of the algorithms' outputs to "exact at all verifier messages".
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file has. Definitions and one statement, for all parameters. The statement is proved in
Johnson/LinkSim/AtText/Exact.lean.

The simulator.
  simLink K ds a xs dec P S t Kc lay keysOf : SimOf (linkProtocolOfRoundData K ds a xs dec).
Its parameters, all of them: the protocol's parameters K, ds, a, xs, dec; the plan's parameters P
(the link's public parameters, from which the proximity test's stages are read:
(p12Of P).nums.stages), S (its sizes) and t (a number); the finite type of coins Kc with its map lay
into the coins that the prover's algorithm reads; keysOf, a map from instances to two keys
(TableKey). At homeR b Z keysOf rewrites the instance's two OOD samples (Spec.lean's terms). None
is, or is applied to, an index, a table's randomness, a private input or the prover's data.
What it does, at an instance x, verifier messages ρ and the symbols ans of the two encodings at the
queried positions. It draws c uniformly in Kc. It runs the simulator's algorithm (simAll,
Johnson/LinkSim/AtText/Defs.lean) at the data made of x and ans alone (inOf,
Johnson/LinkSim/AtText/SeamInput.lean: both tables' rows 0; the columns in ans; the keys of x), at
the coins lay c and at the challenges of all of ρ. It turns that output into a strategy by the same
function stratOf (Johnson/Prover/Link/LinkFrame.lean) that builds the honest prover's strategy. It
outputs that run's disclosed view, with two input oracles built from ans and a fixed symbol
elsewhere (bldX). There is no verifier message at which it outputs none.

The honest prover.
linkSide … : linkRec at the prover's algorithm's next-message function (linkNext), at the data
inW w x and the coins lay c. Its input oracles ext and its data inW are parameters here.

The statement (Spec.exactOfText). If its seven premises hold, the honest prover is exact against
simLink at all verifier messages (ExactOff at the empty set, Johnson/LinkSim/Spec.lean). The
premises, in the Lean's order:
  1. the plan has a first stage: (p12Of P).nums.stages = first :: rest;
  2. every position that the verifier queries in the prover's own trees is opened by the algorithm's
     schedule (WantTie), at every list of challenges;
  3. every position of the two encodings that the algorithm opens lies below the tables' length and
     is queried by the verifier (StoredTie), at every list of challenges;
  4. addK, the sum of two coins, cancels: addK k d = addK k' d implies k = k';
  5. at a valid private input and instance, the honest data's keys are the instance's;
  6. at a valid private input and instance, the honest data's stored column at each position in
     range is the column in the input oracles' symbol there;
  7. at every valid private input and instance and at all verifier messages, what the prover's
     algorithm and the simulator's algorithm disclose agrees up to a shift of Kc's coins that can be
     undone (UpToShift, Johnson/LinkSim/UpTo.lean).
Premises 1 to 3 are public. Premise 7 compares the two algorithms at the same, honest data inW w x;
that the simulator's algorithm gives the same at the data made of x and ans alone is a lemma used in
the proof (simOfAns, Johnson/LinkSim/AtText/SeamInput.lean). No premise ties the honest data's rows
to its stored columns. That tie enters only through the premise on the honest run of
Spec.linkShiftIn (Johnson/LinkSim/AtText/SpecShiftIn.lean), the statement from which premise 7 is
drawn.

What guards against a simulator that knows the private input. In a row of "for all", the order of
the variables binds nothing by itself. The guard is that in ExactOff "for all private inputs" stands
inside, at one fixed simulator: whatever a parameter had captured must serve every valid private
input. So the guard is as strong as "valid" is wide.

How it fits. In this folder, Johnson/LinkSim/AtHome/SpecHome.lean defines homeSim by simLink and
explicitLinkProver by linkSide. Exact.lean proves Spec.exactOfText and uses linkSide and bldX. The statement
is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean) and in
Johnson/LinkSim/AtHome/RoadCloses.lean.

Main names (namespace OnBytes.LinkSim.Seam): bldX, simLink, linkSide, Spec.exactOfText.

Limits.
- What the simulator is given depends on the index: the instance (at the link, the two out-of-domain
  samples) and the symbols of the two encodings at the queried positions.
- The simulator's algorithm, and the shift of the coins beneath premise 7, read all challenges at
  once, later ones too. That is allowed against an honest verifier, whose messages are fixed first,
  and against no other.
- The statement is an implication. Whether premise 7 holds is the matter of the statement at the
  level of the algorithms' outputs (Johnson/LinkSim/AtText/SpecShift.lean and SpecShiftIn.lean) and
  of the map of the coins. At homeR b Z it is proved (home_upTo,
  Johnson/LinkSim/AtHome/RoadCloses.lean, at the theorem linkShiftIn).
- The honest prover's ext, inW and lay are parameters here. One definition substitutes them at
  homeR b Z, in Johnson/LinkSim/AtHome/SpecHome.lean.
- One link: the statement is about one run of the link proof, for one copy; nothing is said of
  several links together.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamInput
import Johnson.LinkSim.AtText.SeamGroups

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.LinkSim OnBytes.LinkSim.AtText
open OnBytes.Flat (linkProtocolOfRoundData)
open _root_.Compile.Lifetime (SimOf)
open _root_.Desc.K15 (P15 p12Of)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO SgX)
open TypedOracleCompiler.Run.PQ (RD SOf drawnSL)

/-- Two stored tables built from the symbols that were read: elsewhere a fixed symbol. -/
def bldX (a : ℕ) (ans : (twoExternalStrings (2 ^ a) SgX).Pos → Option SgX) : (twoExternalStrings (2 ^ a) SgX).Str :=
  (fun p => (ans (.inl p)).getD (0, []), fun p => (ans (.inr p)).getD (0, []))

/-- **The link proof's simulator.** Its parameters are listed in this file's head; none is an index,
a table's randomness, a private input or the prover's data. -/
def simLink (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) {Xi : Type} (dec : Xi → View → Bool)
    (P : P15) (S : Sz) (t : ℕ) (Kc : Type) [Fintype Kc] [Nonempty Kc] (lay : Kc → LCoins)
    (keysOf : Xi → TableKey × TableKey) : SimOf (linkProtocolOfRoundData K ds a xs dec) :=
  simOfStrat (linkProtocolOfRoundData K ds a xs dec) Kc (bldX a) ∅ fun x ρ ans c =>
    stratOf K ds (nextOfOut
      (simAll P S t (inOf a keysOf x ans) (lay c) (drawsOf (drawnSL K ds ρ.2))))

/-- **The honest prover**: linkRec at the prover's algorithm's next-message function. -/
def linkSide (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) {Xi : Type} (dec : Xi → View → Bool)
    (P : P15) (S : Sz) (t : ℕ) (Kc : Type) [Fintype Kc] [Nonempty Kc] (lay : Kc → LCoins)
    {Wt : Type} (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str) (inW : Wt → Xi → LIn S) :
    Honest (linkProtocolOfRoundData K ds a xs dec) Wt :=
  linkRec K ds a xs dec ext fun w x c => linkNext P S t (inW w x) (lay c)

/-- Statement only; proved as exactOfText in Johnson/LinkSim/AtText/Exact.lean. If the seven
premises listed in this file's head hold, the honest prover is exact against simLink at all verifier
messages. -/
def Spec.exactOfText : Prop :=
  ∀ (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) (Xi : Type) (dec : Xi → View → Bool) (P : P15)
    (S : Sz) (t : ℕ) (Kc : Type) [Fintype Kc] [Nonempty Kc] (lay : Kc → LCoins)
    (addK : Kc → Kc → Kc) (keysOf : Xi → TableKey × TableKey) (Wt : Type)
    (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str) (inW : Wt → Xi → LIn S) (valid : Wt → Xi → Prop)
    (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage),
    (p12Of P).nums.stages = first :: rest →
    (∀ Ds, WantTie ds (sched rest first 6 1) Ds) →
    (∀ Ds, StoredTie P a ds xs Ds) →
    (∀ k k' d, addK k d = addK k' d → k = k') →
    (∀ w x, valid w x → (inW w x).keys = keysOf x) →
    (∀ w x, valid w x → ∀ b pos (h : pos < 2 ^ a),
      (inW w x).y b pos = ((twoExternalStrings (2 ^ a) SgX).rd (ext w) (posOf a b pos h)).2) →
    (∀ w x, valid w x → ∀ ρ : Rho (_root_.Run.Twin.up (SOf K ds)),
      UpToShift addK
        (fun k => shownOf (linkAll P S t (inW w x) (lay k) (drawsOf (drawnSL K ds ρ.2))))
        (fun k => shownOf (simAll P S t (inW w x) (lay k) (drawsOf (drawnSL K ds ρ.2))))) →
    ExactOff (linkSide K ds a xs dec P S t Kc lay ext inW) valid
      (simLink K ds a xs dec P S t Kc lay keysOf) ∅

end OnBytes.LinkSim.Seam
