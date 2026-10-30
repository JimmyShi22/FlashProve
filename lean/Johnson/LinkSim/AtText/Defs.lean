-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Defs.lean: the link proof's simulator, written as an algorithm of the same
form as the prover's, and the terms of the folder AtText/.
Terms of this folder: Johnson/LinkSim/Spec.lean. The terms of AtText/ are defined below.

What this file defines. simAll is the simulator's algorithm. It runs the link prover's own algorithm
linkAll at the data 0 (zeroIn X), with the same coins C and the same verifier challenges D. Then it
replaces one element of the output: the element that the base case's first round sends. In its place
it puts tauStar, the element made to satisfy the verifier's last equation. simAll takes the same
arguments as linkAll and returns the same kind of output (BOut): rounds and opened columns, not a
strategy of the typed protocol. It is given the whole data X. That it reads of X only the two keys
and the stored columns at the positions that are opened is the statement Spec.simReads
(Johnson/LinkSim/AtText/SpecShift.lean), proved as simReads (Johnson/LinkSim/AtText/SimReads.lean).

Why one element is replaced. With the data 0, the claim left at the base case need not be true at
the simulator's last message. Then, where the sampled element is not 0, the element that the
prover's algorithm sends does not satisfy the verifier's last equation. This is argued on paper from
the two algorithms, not proved of the whole algorithm; a negative test on one part of it (a function
that writes one round) is tau_own_fails (Johnson/LinkSim/AtText/MustFail.lean), under a premise that
is not proved to hold for any data. The element made to satisfy that equation is a function of what
is disclosed and of the claim's target, which the verifier's state holds.

How one run of linkAll goes. In round 0 the verifier samples a point, and the prover folds each
stored table's rows at it into one folded row. In round 1 the prover sends the first tree, which
holds the two folded rows and the row beside them; the verifier samples the seed of the link proof's
own OOD sample. In round 2 the prover sends its two OOD answers in the clear. In round 3 the
verifier samples the positions at which the stored tables are opened; each opened column gives a
claim that ties the stored table to its folded row. In round 4 the verifier samples a second point
and adds one linear claim at that point, which tests that the two folded rows agree on the entries
before the pads: the claim that the link proof is there to check. The prover sends nothing in rounds
0, 3 and 4. Round 5 is the batching. From round 6 on, the proximity test runs stage by stage: each
stage but the last is a fold and a switch, and the last is the base case (see the terms below).

How it fits. The statements on these definitions are in SpecShift.lean, SpecShiftIn.lean and
SpecStage.lean; they are used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).

Terms of AtText/. Lean names stay as they are. Kc and coinsFull, the instance's OOD samples, the
full-size parameters and the numbers 62 and 97 are defined in Johnson/LinkSim/Spec.lean.
  the prover's algorithm (linkAll, Johnson/Prover/Link/LinkAll.lean)
                 The link's honest prover, written as one function of the data X, the coins C and
                 all verifier challenges D. Its output (BOut, Johnson/Prover/Link/BodyAll.lean) has
                 three parts: the rounds (rs), the written column of each round's tree (tr), and the
                 groups (gs).
  the simulator's algorithm (simAll)
                 Defined here, above.
  parameters (P : P15), sizes (S : Sz)
                 P is the link proof's public parameters: the setting, the codes, the link's shape
                 and the proximity test's stages with their sizes (Johnson/Desc/Link/LinkDesc.lean).
                 S is the sizes of the two stored tables and of the first message (Sz,
                 OnBytes/Slice/LinkAt.lean).
  data (X : LIn S)
                 What the prover is given: the rows of the two tables as polynomials, given by their
                 coefficients (M₀, M₁), in which the index and both tables' encoding randomness
                 stand; the stored columns y of both tables; and the two keys.
  the public premises on sizes (Sizes, SpecShift.lean)
                 Public: Sizes reads the parameters, the sizes and the verifier's challenges, and no
                 data and no coin. SpecShift.lean's head lists its fields. It is proved at the
                 full-size parameters as fr_sizes (SeamAtFull3.lean).
  the data 0 (zeroIn X)
                 X with M₀ and M₁ replaced by 0; the stored columns and the keys unchanged.
  the link proof's own OOD samples (smAt, gAns, ansAt)
                 The verifier's samples on the prover's own messages inside the link proof. In
                 round 2 the prover answers one on each folded row (lFront,
                 Johnson/Prover/Link/LinkAll.lean); at each switch it answers one on its new word
                 (sAns, Johnson/Prover/Link/BodyAll.lean). Each answer is sent in the clear.
  keys           The instance's two OOD samples, written in the form (TableKey) that the verifier's
                 decision, in Lean, reads (keysOf, Johnson/Prover/Link/LinkYesStm.lean). They are
                 not the scheme's verification key.
  stored tables, stored columns
                 The link's two input oracles: the first table and the copy. y b x is the column of
                 stored table b at position x: the values of all its rows there (2,048 rows at the
                 full-size parameters).
  coins (C : LCoins)
                 All random values of one run of linkAll, as variables: functions on all natural
                 numbers (LCoins, Johnson/Prover/Link/LinkAll.lean; for the stages, BCoins,
                 Johnson/Prover/Link/BodyAll.lean). This type is infinite; the algorithm reads
                 finitely many of its places. The finite type of coins at sizes S and stages l is
                 LinkK GE S l (Johnson/Prover/Link/LinkCoin.lean); Kc is its case at the full-size
                 parameters.
  verifier challenges (D : ℕ → Fmt.Drawn)
                 D i is what the verifier samples in round i (Fmt.Drawn, Fmt/Rules6Round.lean). The
                 definitions here, and linkAll and bodyAll, read only its field elements and its
                 positions; the structure has two further fields. Every definition here takes all of
                 D at once, so a value may depend on a challenge of a later round.
  rounds, groups (shownOf, SpecShift.lean)
                 A round is what the prover sends in the clear in that round, together with that
                 round's challenges. A group is the columns of one tree or stored table at the
                 positions at which it is opened. shownOf keeps the rounds and the groups: the two
                 algorithms are compared on these. The trees themselves are not compared: off the
                 opened positions they may differ.
  tree           An oracle message of the prover: a table of rows whose columns the verifier reads
                 at sampled positions. In the output (BOut) a tree is given by its column function,
                 listed under the round that sends it. A group is its columns at the sampled
                 positions taken modulo 2^a, each once (groupAt, Johnson/Prover/Link/BodyAll.lean),
                 where 2^a is the length of the stage's main code. After hashing a tree is a Merkle
                 tree.
  opened         read at a list of sampled positions.
  row, message, tail
                 A row is a polynomial; its coefficients are the tail's entries first, then the
                 message's. Its symbol at a position is its value at that position's point. The tail
                 is the row's lowest coefficients. In the prover's own trees its entries are coins;
                 a stored table's tails stand in the data's rows M₀ and M₁ (the private input), not
                 among the coins.
  main row, mask row
                 A stage's oracle has main rows, which carry the data under test, and mask rows,
                 under a code of their own (Z), whose entries are the prover's random values or are
                 carried over from the stage before.
  folded rows, the row beside them
                 In the link's front, the rows of each stored table are folded at the verifier's
                 point into one folded row. Its message is laid out as R rows under the main code C,
                 each with a tail of its own (R = 107 at the full-size parameters: frPar,
                 OnBytes/Slice/FullRecSz.lean). Beside the two folded rows the prover sends one row
                 under the mask code Z, which holds the packing of the first fold's
                 hiding-polynomial coefficients. Lean calls the two folded rows the members, indexed
                 by a Boolean a: a = false is the fold of M₀, a = true the fold of M₁ (frontMem,
                 Johnson/Prover/Link/BodyEnds.lean). At homeR b Z the first input oracle is the
                 codeword of the rows M₀ and the second that of M₁ (home_meant,
                 Johnson/LinkSim/AtHome/HomeTies.lean; Meant.tab0 and tab1,
                 Johnson/Prover/Link/LinkYesStm.lean).
  pad            A random entry of a row's message, at a place that holds no data. Three kinds
                 occur. A stored table's row ends in 3 pad entries over the base field: part of the
                 table's encoding randomness, so of the private input. In the link's front, each of
                 the two folded rows has one pad entry (C.pad a, at Sz.padJ); the link proof's own
                 OOD answer on that row reads it with the seed's factor, which is a unit by
                 construction (lSeed, Johnson/Prover/Link/LinkAll.lean). At each switch, the last
                 free entry of the new mask table is a pad (padIx, Pad.lean). The last two kinds are
                 coins.
  free entries   The entries of a switch's new mask table that hold nothing carried over from the
                 stage before (SwK.free, Johnson/Prover/Link/LinkCoin.lean); the last of them is the
                 pad.
  stage, fold, switch
                 The link's proximity test runs in stages (five at the full-size parameters:
                 frPar.stages). Every stage but the last is a fold followed by a switch; the last
                 stage is the base case. A fold is a run of sumcheck rounds that combines a table's
                 rows into one word, under coefficients from the verifier's point. At a switch the
                 prover sends a new word under a new code, whose message holds the old word's
                 message and tail; the verifier reads the old word at sampled positions.
  hiding polynomial
                 A random polynomial that the prover adds to a fold's sumcheck (hU,
                 Cb/Ld/LdHide.lean). In the link's folds it has 2k + 1 coefficients for k variables:
                 two for each variable and a constant (sVars GE 2 k, in the type of BCoins.W). Its
                 coefficients are packed into a mask row. The name is the library's; it claims
                 nothing here.
  base case, the claim left at the base case (claimEnd, ClaimTrue)
                 The last stage ends in the base case, of two rounds. By then the test has reduced
                 to one claim: a linear form of the last main row's message plus a linear form of
                 the last mask row's message equals a target. ClaimTrue says that it holds at the
                 prover's last message. In the first round the prover sends one element and the
                 verifier samples an element (the first element of its challenges in that round). In
                 the second round the prover discloses four lists: the main message, the mask
                 message, the main tail and the mask tail, each of the masking word plus the sampled
                 element times the last message.
  masking word   At the last switch: one main row and one mask row of random entries, with their
                 tails (WordK, Johnson/Prover/Link/LinkCoin.lean).
  tauStar        The element made to satisfy the verifier's last equation: the claim's left side at
                 what the second round discloses, minus the sampled element times the claim's
                 target. That it does is read off its formula and the verifier's decision, not
                 proved: no lemma here states that equation. Proved: where the claim is true or the
                 sampled element is 0, it equals the honest run's element (last_tau_or,
                 LastStepOr.lean).
  two runs side by side, the shift of the coins (ShiftDefs.lean)
                 The shift is the map that sends the prover's coins C to C + s C, where + is addC
                 (entry by entry) and the amount s C may depend on C: it is computed from the data,
                 the challenges and the run (shC; along the stages, shB). A second map s' recovers
                 the amount from the shifted coins: s' (C + s C) = s C for every C that the
                 statement covers, so on those coins the map is one to one (UpToShift,
                 Johnson/LinkSim/UpTo.lean). The honest run is linkAll at the data X and coins C.
                 The other run is linkAll at the data 0 and the shifted coins. The shift is meant to
                 make the two runs disclose the same rounds and groups, except the element that
                 tauStar replaces. LinkShift.lean proves that it does, under the premises of
                 Spec.linkShiftIn. d is the difference of the two prover states at a stage.
  compensating tail (tailAt, ShiftDefs.lean; tailFor, Johnson/LinkSim/Tail.lean)
                 For a change dm of a row's message and a list of at most as many positions as the
                 tail is long: the tail whose own values at those positions are dm's share of the
                 symbols there. The message m + dm with the tail t has, at those positions, the
                 symbols of the message m with the tail t plus the compensating tail: the tail
                 stands in place of the change of the message.

The other names (namespace OnBytes.LinkSim.AtText).
  addPS, addB, addC   two prover states, or two values of the coins, added entry by entry.
  linkEnd        what holds at the last stage (BEnd, Johnson/Prover/Link/BodyEnd.lean): its number,
                 sizes and layout, the number of its first round, the verifier's state, the prover's
                 state and the columns of the tree in hand; none if the plan has no stage.
  claimEnd       the claim left at the base case, read from the verifier's state. If the state
                 passes on no claim of the right form for that stage, it is the claim with no
                 coefficients and the target 0.

Limits.
  - Definitions alone: this file states no theorem.
  - The coins are the prover's algorithm's variables, functions on all numbers: no finite type of
    coins is here.
Sources. It follows the library's simulators of the typed blocks in shape ("the honest prover on
message 0"; Cb/Ld/LdSwitch.lean, Cb/Ld/LdBase.lean); it calls none of them. The simulator's idea
(run the prover's algorithm with the tables' rows set to 0, and fix one value by the verifier's
final equation) follows a write-up of ours that is not in this repository, so it cannot be checked
against that text from here (lean/CREDITS.md, "This protocol's technical report", says what such a
name means). By its makers' account that write-up rests on files of this repository that follow the
paper that this protocol builds on (lean/CREDITS.md, under that heading). The first part of that
idea appears in small form in the head of Cb/Ld/LdSumZk.lean: a simulator that draws as the honest
prover does and encodes the message 0. The definition it serves is credited in lean/CREDITS.md,
"Further work that this protocol builds on". The write-up does not count as made independently of
that work.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkAll
import Johnson.Prover.Link.BodyEnd

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open VerifiableInference.Desc.Prox (BaseClaim)
open Johnson.Prover.Link

/-! ## Adding coins entry by entry -/

/-- Two prover states added entry by entry. -/
def addPS (P Q : PS) : PS where
  tabM := fun i => P.tabM i + Q.tabM i
  tabZ := fun i => P.tabZ i + Q.tabZ i
  tM := fun b q => P.tM b q + Q.tM b q
  tZ := fun b q => P.tZ b q + Q.tZ b q
  fM := fun b j => P.fM b j + Q.fM b j
  fT := fun b q => P.fT b q + Q.fT b q
  sM := fun j => P.sM j + Q.sM j
  sT := fun q => P.sT q + Q.sT q

/-- Two values of the stages' coins added entry by entry. -/
def addB (K K' : BCoins) : BCoins where
  W := fun s j x => K.W s j x + K'.W s j x
  new := fun j => addPS (K.new j) (K'.new j)
  fr := fun j i => K.fr j i + K'.fr j i

/-- Two values of the coins added entry by entry. -/
def addC (C C' : LCoins) : LCoins where
  pad := fun a => C.pad a + C'.pad a
  tN := fun a i q => C.tN a i q + C'.tN a i q
  ψN := fun q => C.ψN q + C'.ψN q
  body := addB C.body C'.body

/-! ## The data 0 -/

/-- The data 0: both tables' rows replaced by 0; the stored columns and the keys unchanged. -/
def zeroIn {S : Sz} (X : LIn S) : LIn S :=
  { X with M₀ := fun _ _ => 0, M₁ := fun _ _ => 0 }

/-! ## The last stage -/

/-- What holds at the last stage of the link's proximity test (number, sizes, first round, both
states, the tree's columns); none if the plan has no stage. -/
def linkEnd (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn) : Option BEnd :=
  match (p12Of P).nums.stages with
  | first :: rest =>
    some (bodyEnd (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
      (lPS P S X C D) (lCol P S X C D))
  | [] => none

/-- The claim left at the base case, as the prover's algorithm reads it from the verifier's state;
the claim with no coefficients and target 0 if the state holds none. -/
def claimEnd (p : P12) (e : BEnd) : BaseClaim :=
  ((stageAt p e.j e.cur).bind fun c => claimAt e.t.st.codes c (rowOf e.t)).getD
    ⟨#[], #[], (0, 0, 0)⟩

/-- That claim is true at the prover's last message. -/
def ClaimTrue (p : P12) (e : BEnd) : Prop :=
  formG (sgOf e.cur).C.l (claimEnd p e).c (mainOf (sgOf e.cur) (μOf (sgOf e.cur) e.P)) +
      formG (sgOf e.cur).Z.l (claimEnd p e).d (maskOf (sgOf e.cur) (μOf (sgOf e.cur) e.P)) =
    toE (claimEnd p e).tau

/-- The element made to satisfy the verifier's last equation: the claim's left side at the two
messages that the second round discloses, minus the sampled element times the claim's target. -/
def tauStar (p : P12) (e : BEnd) (D : ℕ → Fmt.Drawn) : Fmt.M1.E :=
  ofE (formG (sgOf e.cur).C.l (claimEnd p e).c
        (fun j => e.P.sM j + toE ((D e.o).elems.headD (0, 0, 0)) *
          mainOf (sgOf e.cur) (μOf (sgOf e.cur) e.P) j) +
      formG (sgOf e.cur).Z.l (claimEnd p e).d
        (fun j => e.P.fM 0 j + toE ((D e.o).elems.headD (0, 0, 0)) *
          maskOf (sgOf e.cur) (μOf (sgOf e.cur) e.P) j) -
      toE ((D e.o).elems.headD (0, 0, 0)) * toE (claimEnd p e).tau)

/-! ## The simulator's algorithm -/

/-- The simulator's algorithm: the prover's algorithm at the data 0, with the element of the base
case's first round replaced by tauStar. -/
def simAll (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn) : BOut :=
  match linkEnd P S t (zeroIn X) C D with
  | some e =>
    { linkAll P S t (zeroIn X) C D with
      rs := (linkAll P S t (zeroIn X) C D).rs.set e.o ⟨[.e (tauStar (p12Of P) e D)], D e.o⟩ }
  | none => linkAll P S t (zeroIn X) C D

end OnBytes.LinkSim.AtText
