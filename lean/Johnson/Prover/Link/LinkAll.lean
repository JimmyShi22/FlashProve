-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkAll.lean: the explicit honest link prover. All its messages as a function of
all verifier challenges (linkAll), and its next-message function (linkNext).
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

What this file has. linkAll P S t X C D takes the parameters P and S, the number t (97 at the
full-size parameter set: see LinkYesStm.lean), the prover's input X (LIn), a value C of the prover's
free parameters (LCoins), and the verifier's challenges D by the round's number. It returns three
lists (BOut, Johnson/Prover/Link/BodyAll.lean): for each round the items that the prover sends in
the clear, with that round's challenge; for each round the oracle message that it sends, as a column
for each position (a tree; the empty column where it sends none); and the groups of columns that the
verifier's openings read.
linkNext i hist is round i's message (MsgV, Johnson/Prover/Link/LinkFrame.lean) from the challenges
hist of the earlier rounds. It evaluates linkAll at hist, continued by empty challenges, and takes
round i's items and column. In linkAll these two depend on the challenges before round i only
(linkAll_causal, Johnson/Prover/Link/LinkCausal.lean). So linkNext at the first i challenges of a
list gives them as linkAll has them at the whole list (linkNext_at, the same file).
The rounds. Listed are linkAll's items and columns. A nonce is not among them: msgS (LinkFrame.lean)
lays 0; of rounds 0 to 5, round 3 has a proof-of-work check (by inspection). The names in quotation
marks are those of the plan's entries behind its first (recordEntries,
OnBytes/Params/EntryStagesRecord.lean; by inspection, not proved here).
  0     "LINK point": no item and no tree; the challenge is the folding point (lGam).
  1     "SEND seed": the prover sends the first tree; the challenge holds the seed of the two folded
        messages' samples (lSeed). At each position the tree's column (lCol) holds S.P.R symbols of
        each of the two folded messages and one symbol of a further row over the mask code
        (firstSyms, Johnson/Prover/Link/FrontCols.lean).
  2     "SEND answer": the prover sends these two samples' answers in the clear.
  3     "LINK": no item and no tree; the challenge samples the positions at which the two input
        oracles are read (lStored).
  4, 5  "LINK phi" and "BAT", the batching: no item and no tree.
  6 on  the proximity test's stages (bodyAll, BodyAll.lean).

How it fits. LinkYes (LinkYesStm.lean) is a statement about linkNext, and link_yes
(Johnson/Prover/Link/LinkJoinF.lean) proves it at t = 97.

Two names (namespace Johnson.Prover.Link). Every definition has a docstring below.
  LCoins  the prover's free parameters: no definition here fixes them, and LinkYes quantifies over
          every value of them. pad a is one field element for each of the two folded messages. tN
          holds the tails of these messages' rows, ψN the tail of the further row, and body the
          stages' free parameters (BCoins, BodyAll.lean). In linkFits_at
          (Johnson/Goal/Conditions/LinkFitsAt.lean) they are coinsOf c: a function, itself a
          parameter there, of the honest prover's coin c.
  lMem    the two folded messages: membMsg (Johnson/Prover/Link/FrontMsg.lean) at the fold at lGam
          of each table's row polynomials. At the entries that hold no coefficient of the fold it
          has C.pad a at the place S.padJ and 0 elsewhere.

Limits. 1. lT is the verifier's state after the batching, as the prover computes it: it runs the six
sub-protocols before the proximity test, then the test's front and its batching. Where one of the
six rejects, lT silently goes on from the state before all six (d₀); where the front or the batching
rejects, from the state before it. So a theorem on the honest run has to prove that none of them
rejects. At the full-size parameter set that is done by front6_walks_full
(Johnson/Prover/Link/FormWalks.lean) for the six and by inv0_full (LinkJoinF.lean) for the front and
the batching, each under its own conditions.
2. linkNext gives one column function to every tree of a round, so at a round with two trees both
would get the same words. At the full-size parameter set no round has two: fr_widths
(Johnson/Prover/Link/LinkAtFull.lean) lists each round's trees' widths as none or one. For general
parameters nothing in this file checks it.
3. Several definitions have silent defaults. linkNext sends no item and empty columns at a round
beyond linkAll's lists. linkAll returns three empty lists if the plan has no stage, and sg0 then
takes the default stage. lGam and lSeed read zeroE for every element that their round's challenge
lacks (readP, OnBytes/Slice/ProgField.lean). lMem has 0 at the entries that hold neither a
coefficient of the fold nor the pad.
4. At two shapes of the sizes the place S.padJ itself holds a coefficient of the fold: 0 < T.r and
t0 + T.r = R * C.l, or T.r = 0 and T.l = R * C.l. lMem then has that coefficient there and C.pad a
is read nowhere (see membMsg's docstring). At the full-size parameter set neither occurs: t0 + T.r =
446,693,375 and R * C.l = 448,790,528 (by inspection of frPar, not proved here).
5. This file has definitions only: no theorem is stated.
No distribution on the free parameters and no finite type of coins in this file (one is defined in
Johnson/Prover/Link/LinkCoin.lean). Nothing on how a value of LCoins is chosen. Nothing on what any
value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyAll
import Johnson.Prover.Link.BodyEnds
import Johnson.Prover.Link.LinkFrame
import Johnson.Desc.Link.LinkDesc
import Johnson.Desc.K15.HsemSays
import Johnson.Desc.K12.Law.ReadsK

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 frontBlock blocksOrV readsAtLink p12Of)
open H2K.JointK (laidOf)

/-- The prover's input: the two tables' row polynomials, the two input oracles' symbols by position,
and the instance's two table keys. -/
structure LIn (S : Sz) where
  M₀ : (Fin S.P.v → Bool) → S.Co → GE
  M₁ : (Fin S.P.v → Bool) → S.Co → GE
  y : Bool → ℕ → List UInt64
  keys : TableKey × TableKey

/-- The prover's free parameters: no definition here fixes them, and LinkYes (LinkYesStm.lean)
quantifies over every value of them. -/
structure LCoins where
  pad : Bool → GE
  tN : Bool → ℕ → ℕ → GE
  ψN : ℕ → GE
  body : BCoins

/-- The sizes of the test's first stage, as bodyAll reads them. -/
def sg0 (P : P15) : Sg := H2K.Pub.sgOf ((p12Of P).nums.stages.headD default)

section
variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

/-- The folding point, read from round 0's challenge; zeroE for an element that it lacks (readP). -/
def lGam : Fin S.P.v → GE := readP S.P.v ((D 0).elems.map E.ofTriple)

/-- The two folded messages: membMsg at the fold at lGam of each table's row polynomials, with fr :=
C.pad a at S.padJ and 0 elsewhere; fr is not read where S.padJ holds a coefficient (see membMsg). -/
def lMem : Bool → S.MJ → GE :=
  frontMem S (lGam S D) X.M₀ X.M₁ fun a j => if j = S.padJ then C.pad a else 0

/-- The prover's first state. Here and in lCol the further row is the packing packedN (sg0 P)
(C.body.W (sg0 P) 0) 0, of the same coefficients from which bodyAll computes the first fold's
rounds: the invariant needs that equation (ValInv.packs, Johnson/Prover/Link/BodyInv.lean). -/
def lPS : PS :=
  firstPS S (lMem S X C D) C.tN (packedN (sg0 P) (C.body.W (sg0 P) 0) 0) C.ψN

/-- The first tree's column, by position. -/
def lCol : ℕ → List UInt64 :=
  firstColW S (membN S (lMem S X C D)) C.tN (packedN (sg0 P) (C.body.W (sg0 P) 0) 0) C.ψN

/-- The seed of the two folded messages' samples, read from round 1's challenge; zeroE for every
element that it lacks. -/
def lSeed : (S.fam.om false).Z.D :=
  (readP (S.P.aR + S.P.aP) (((D 1).elems.map E.ofTriple).take (S.P.aR + S.P.aP)),
    unitOf (readE (((D 1).elems.map E.ofTriple).getD (S.P.aR + S.P.aP) zeroE)))

/-- Rounds 0 to 4: each round's items in the clear, with its challenge. Round 2 sends the two
answers; the other four send no item. -/
def lFront : List Fmt.RoundView :=
  [⟨[], D 0⟩, ⟨[], D 1⟩,
    ⟨[.answer (ofE (smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) false)),
      .answer (ofE (smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) true))], D 2⟩,
    ⟨[], D 3⟩, ⟨[], D 4⟩]

/-- The symbols of the two input oracles at the positions that round 3's challenge samples, one
group for each oracle that is read. -/
def lStored : List (List (ℕ × List UInt64)) :=
  (readsAtLink P.S).map fun st =>
    (Fmt.listOf ((Fmt.partOf st (D 3).poss).map (· % 2 ^ st.sh.a))).map fun x =>
      (x, X.y (st.item == 1) x)

/-- The same symbols in one list, each with its oracle's key and its position. -/
def lStoredCols : List OpenedColumn :=
  (readsAtLink P.S).flatMap fun st =>
    (Fmt.listOf ((Fmt.partOf st (D 3).poss).map (· % 2 ^ st.sh.a))).map fun x =>
      (Fmt.storedKey st.item, x, X.y (st.item == 1) x)

/-- The verifier's state after the batching, as the prover computes it: it runs the six
sub-protocols before the proximity test (Johnson/Desc/Link/LinkDesc.lean) on rounds 0 to 4 and
lStoredCols, then the test's front and its batching (guardedProximityTestParts). Where one of the six rejects, lT
silently goes on from the state before all six (d₀); where the front or the batching rejects, from
the state before it. -/
def lT : T12 :=
  let d₀ := _root_.Desc.K15.first P.codes X.keys
  let d₅ := ((foldBlocks 0 (frontBlock P :: blocksOrV P) d₀ (lFront S t X C D)
    (lStoredCols P S X D)).toOption.map (·.1)).getD d₀
  let t₀ : T12 := { st := d₅.st, book := d₅.book, roots := d₅.roots, g := d₅.loc.g,
                    pass := .nothing, mask := d₅.loc.firstMask }
  let tF := ((guardedProximityTestParts.front (p12Of P)).decide t₀ [] []).toOption.getD t₀
  ((guardedProximityTestParts.bat (p12Of P) (((laidOf (p12Of P)).take 1).map (·.1))).decide tF [noDigest ⟨[], D 5⟩]
    []).toOption.getD tF

/-- **All the prover's messages**: for each round its items in the clear with its challenge; for
each round its tree's column; the groups of columns that the openings read. Three empty lists if the
plan has no stage. -/
def linkAll : BOut :=
  match (p12Of P).nums.stages with
  | first :: rest =>
    let B := bodyAll (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
      (lPS P S X C D) (lCol P S X C D) D
    ⟨lFront S t X C D ++ [⟨[], D 5⟩] ++ B.rs,
      [fun _ => [], lCol P S X C D, fun _ => [], fun _ => [], fun _ => [], fun _ => []] ++ B.tr,
      lStored P S X D ++ B.gs⟩
  | [] => ⟨[], [], []⟩

/-- **Round i's message from the challenges of the rounds before.** It gives one column function to
every tree of the round (col := fun _ => ...): at a round with two trees both would get the same
words. At the full-size parameter set no round has two: fr_widths
(Johnson/Prover/Link/LinkAtFull.lean) lists each round's trees' widths as none or one (asTrees); by
name: fr_one (Johnson/Prover/Link/ChainTrees.lean). For general parameters nothing in this file
checks it. At a round beyond the list it sends no item and empty columns. A challenge beyond hist is
the empty challenge: round i's items and column depend on the challenges before round i only
(linkAll_causal, linkNext_at: Johnson/Prover/Link/LinkCausal.lean). -/
def linkNext (i : ℕ) (hist : List Fmt.Drawn) : MsgV :=
  let O := linkAll P S t X C fun j => hist.getD j ⟨[], [], [], none⟩
  ⟨((O.rs[i]?).map (·.vals)).getD [], fun _ => (O.tr[i]?).getD fun _ => []⟩

end

end Johnson.Prover.Link
