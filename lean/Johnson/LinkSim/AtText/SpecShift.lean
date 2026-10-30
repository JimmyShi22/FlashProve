-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SpecShift.lean: the plain statement that the link prover's and the
simulator's algorithms disclose the same, coin by coin, up to a shift of the coins that can be
undone, under public premises on sizes and one premise on the honest run. Definitions and the
statement, on the algorithms' outputs.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

This file belongs to the second of the folder's three steps, the prover's algorithm at any sizes
(Johnson/LinkSim/Spec.lean names the steps). Its statements are proved in
Johnson/LinkSim/AtText/SimReads.lean and LinkShift.lean.

The two algorithms are linkAll (Johnson/Prover/Link/LinkAll.lean) at the data X, and simAll
(Johnson/LinkSim/AtText/Defs.lean). Both are functions of the coins C and of all challenges D.
simAll takes all of X as input. That it reads of X the two keys and the stored columns at the
positions opened, and nothing else, is a statement of its own here (Spec.simReads).

What is compared is shownOf: the rounds, that is, all items sent in the clear with the challenges;
and the groups, that is, the columns of the two stored tables and of the run's own trees, one per
stage (five at the full-size parameters), at the positions that are opened. The trees themselves are
not compared: off the opened positions they may differ.

The statement (Spec.linkShift). For all data X and all challenges D, under public premises on sizes
(Sizes) and one premise on the honest run (the claim left at the base case is true at the honest
last message, for all coins): what the two algorithms disclose agrees up to a shift of the coins
that can be undone (UpToShift, Johnson/LinkSim/UpTo.lean). That is, there are two maps s, s' on
coins such that for all coins C
    the prover's algorithm at C and the simulator's algorithm at C + s C disclose the same, and
    s' (C + s C) = s C.
The second equation says that what was added can be read back off the changed coins. So C ↦ C + s C
is one to one. On a finite type of coins that it maps into itself, it is a bijection of the coins
with themselves, and then what the two algorithms disclose has the same distribution under uniform
coins (UpToShift.law_eq). Johnson/LinkSim/UpTo.lean has tests of this property, on one bit of coins:
a bare value against another fails it; a masked one satisfies it; without the second equation it
holds of any f whose values g takes. s may depend on the coins, because the coefficients of the
verifier's claims are read off the verifier's state along the run. It is meant to depend on them
through that state alone.

The premise on the honest run is less than completeness: no test of form, no tree and no proof of
work is in it. It cannot be dropped. The simulator's one replaced item is made to satisfy the
verifier's last equation. Where the sampled element of that round is not 0, the honest item
satisfies it only if that claim is true. This is argued on paper from the two algorithms, not proved
of the whole algorithm; a negative test on one part of it (a function that writes one round) is
tau_own_fails (Johnson/LinkSim/AtText/MustFail.lean), under a premise that is not proved to hold for
any data. Where that element is 0 the premise is not needed. At homeR b Z the premise is proved, in
the form that the proof chain takes (home_claim, Johnson/LinkSim/AtHome/HomeTies.lean). At the
full-size parameters, for data that satisfy Meant, it is proved at all coins and at the challenges
of every verifier message (fr_claimTrue, SeamClaim.lean); fr_claimPremise (SeamClaim.lean) puts it
in the form of Spec.linkShiftIn, at the coins in the places.

Which form the proof chain takes. This is the plain form. The proof chain to a distribution goes
through the form with a constraint on the shift (Spec.linkShiftIn,
Johnson/LinkSim/AtText/SpecShiftIn.lean). There, what is added to the coins vanishes outside the
places of the finite type of coins, and the property is asked only at coins in these places. So is
the premise on the honest run, and only where the sampled element is not 0.

Main names (namespace OnBytes.LinkSim.AtText).
  shownOf      what an algorithm discloses: its rounds and its groups (above).
  SameStored   two families of stored columns agree at the positions that are opened.
  Spec.simReads   the simulator's algorithm gives the same output at two data with the same keys
               and SameStored.
  FitsBody, Sizes   the public premises: along the stages, no tree is opened at more positions than
               its rows' tails are long; each switch's sizes fit (CsFit, OnBytes/Slice/CsData.lean);
               each fold's fresh table has room for its packing; the list of stages has a first
               stage; the last stage has h = 0 and g = 0; the front's sizes are the first stage's;
               the front's pad has a place of its own.
  Spec.linkShift   the statement above.

How it fits. SpecShiftIn.lean, SpecStage.lean and the Seam files build on these definitions.
SeamInput.lean uses simReads (in simOfAns), and so simReads is used in the proof of homeExact
(Johnson/LinkSim/AtHome/Home.lean). Under Johnson/LinkSim/ no file uses the theorem linkShift
(LinkShift.lean), which proves the plain form: it is on no proof chain to a distribution.

Limits.
- The plain form says less than its name. The coins are variables on all natural numbers, an
  infinite type, and both algorithms leave infinitely many of these variables unread. Argued on
  paper, not proved: a copy of the coins can be placed at unread places, and then the equation "what
  was added can be read back" can be satisfied by any two algorithms such that each value that the
  first takes, the second takes too. On these variables that equation has no teeth. It bites in the
  form with a constraint on the shift (Spec.linkShiftIn), where the coins and what is added are in
  the places of a finite type.
- It covers an honest verifier and one link (the verifier: Johnson/LinkSim/AtHome/Home.lean's
  limits; one link: SpecExact.lean's limits).
- Nothing here ties the algorithms' outputs to the protocol's disclosed view (Spec.exactOfText,
  SpecExact.lean, does).
- That s C vanishes outside these places is not said here.

Notes. The proofs use no further premise on sizes.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Defs
import Johnson.LinkSim.UpTo

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of readsAtLink)
open H2K.Pub (sgOf)
open Johnson.Prover.Link

/-- What an algorithm discloses: the rounds, and the columns at the positions opened. -/
def shownOf (O : BOut) : List Fmt.RoundView × List (List (ℕ × List UInt64)) := (O.rs, O.gs)

/-- Two families of stored columns agree at the positions that the round "LINK" opens. -/
def SameStored (P : P15) (D : ℕ → Fmt.Drawn) (y y' : Bool → ℕ → List UInt64) : Prop :=
  ∀ st ∈ readsAtLink P.S,
    ∀ x ∈ Fmt.listOf ((Fmt.partOf st (D 3).poss).map (· % 2 ^ st.sh.a)),
      y (st.item == 1) x = y' (st.item == 1) x

/-- Statement only; proved as simReads in SimReads.lean. **What the simulator's algorithm reads of
the data**: the keys, and the stored columns at the positions opened. -/
def Spec.simReads : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (X X' : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn),
    X.keys = X'.keys → SameStored P D X.y X'.y → simAll P S t X C D = simAll P S t X' C D

/-- Along the stages from cur on, whose first round has the number o: the tree that holds cur's rows
is opened at no more positions than its rows' tails are long; sizes fit. -/
def FitsBody (D : ℕ → Fmt.Drawn) : List Fmt.M1.Stage → Fmt.M1.Stage → ℕ → Prop
  | [], cur, o =>
    (D (o + 1)).poss.length ≤ (sgOf cur).C.r ∧ (D (o + 1)).poss.length ≤ (sgOf cur).Z.r ∧
      (sgOf cur).h = 0 ∧ (sgOf cur).g = 0
  | next :: rest, cur, o =>
    (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss.length ≤ (sgOf cur).C.r ∧
      (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss.length ≤ (sgOf cur).Z.r ∧
      (sgOf cur).h + 2 * (sgOf cur).g + 1 ≤ (sgOf cur).Z.l ∧
      CsFit (sgOf cur) (sgOf next) ∧
      FitsBody D rest next (o + ((sgOf cur).h + (sgOf cur).g) + 3)

/-- **The public premises.** They speak of the plan's numbers and of how many positions are
sampled. -/
structure Sizes (P : P15) (S : Sz) (t : ℕ) (D : ℕ → Fmt.Drawn) : Prop where
  /-- the front's sizes are the first stage's -/
  first : sg0 P = S.sg t
  /-- the pad has a place of its own: no coefficient of a fold lies there -/
  pad : S.P.T.l ≤ S.P.R * S.P.C.l - 1 ∧ S.P.t0 + S.P.T.r ≤ S.P.R * S.P.C.l - 1
  /-- along the stages -/
  body : ∃ first rest, (p12Of P).nums.stages = first :: rest ∧ FitsBody D rest first 6

/-- Statement only; proved as linkShift in LinkShift.lean. **The prover's and the simulator's
algorithms disclose the same up to a shift of the coins that can be undone**, under Sizes and the
premise on the honest run. The plain form, which says less than its name: see the head's first
limit. -/
def Spec.linkShift : Prop :=
  ∀ (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (D : ℕ → Fmt.Drawn),
    Sizes P S t D →
    (∀ C e, linkEnd P S t X C D = some e → ClaimTrue (p12Of P) e) →
    UpToShift addC (fun C => shownOf (linkAll P S t X C D))
      (fun C => shownOf (simAll P S t X C D))

end OnBytes.LinkSim.AtText
