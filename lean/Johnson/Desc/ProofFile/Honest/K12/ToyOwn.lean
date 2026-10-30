-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyOwn.lean: tests (`#guard`) of `proverSideOfProximityTest` (Parts.lean), built as
those of Toy.lean, for the case in which the first fold sends its own fresh table and the first
opening has two trees. The two parts of a proximity test's prover are given their random values and
run by the functions of Johnson/Desc/ProofFile/Honest/Frame.lean, and the test's block
(`proximityTestKind guardedProximityTestParts p`) decides on what they send. Computable definitions and evaluations; no theorem.
Synthetic numbers alone.

The example: the small synthetic link of Johnson/Prover/Link/ToyLink.lean with one field changed:
`masksAhead` of its shape is false. Then the link's sending holds the two members alone; the test's
parameters say that the first fold sends its own table (`ownMask`); the round "FOLD epsilon" sends a
root; the state on entry to the test names no message for the first mask (`mask` is none); and the
first round of positions opens two trees, the sending's and the fold's own. Later fresh tables are
sent with a stage's rows as before. The stages, the rounds and the two parts' numbers of rounds are
Toy.lean's: (k, h) = (3, 0), (1, 1), (0, 0); 13 rounds; 5 and 8.

By what: as in Toy.lean, with the link's blocks computed again at the changed shape (`blocks`). The
random values are Toy.lean's, divided in another way: the sender has 14; the table's seven
coefficients and its tail, 9 values, are the first part's own (`takes`); the second part has its 125
and is also given the first part's nine (`carries`).

What is checked.
- `ownMask` is true in the test's parameters. The counts of random values; the two parts' numbers of
  rounds; `lendRow` returns; the play returns at two lists of challenges.
- The block's `decide` accepts the played rounds with the columns of the three played tables and of
  the sending's tree, at both lists.
- At the first list what the thirteen played rounds send is, word for word, what the other program
  sends, as in Toy.lean (`Fmt.M1.Own.go`, in a call in which the table was sent before the test). So
  at this example the sent elements do not depend on who sends the table.
- Negative tests, each change alone. A word of an opened column of each of the four trees made one
  larger: rejected. Each of the first part's nine random values made one larger in its own table
  alone: rejected. The book without the entry by which the second part is given the first part's
  values: `lendRow` returns an error. The same job at Toy.lean's parameters, which say that the
  table was sent before the test: `freshFits` is false, and `play` returns its error on a message's
  shape. By reading, that message is the one of "FOLD epsilon"; the error's text does not name the
  round.

Limits. Those of Toy.lean, with the two cases exchanged: here the first fold sends its own fresh
table, and the first opening has two trees, of which the sending's is the one whose columns this
file computes (`col0`). One example, two lists of challenges, one set of random values.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Toy

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyOwn
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS BOut groupAt mainSym freshSym wordsOf)
open Johnson.Prover.Link.Toy (tinyP tinyLink tinyCodes keyOfT dr eN coin gamma seedZ seedB qs phi
  theta0 vsT frontRounds tailOfMem rowOfMem p1 testRounds evalMain tabOf X3)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.Toy (sender entry storedAt noRec restList csOf front list₁ list₂ word tableAt
  possAt upCol s0)

/-! ## 1 The example and the job -/

def P' : _root_.Desc.K15.P15 := { tinyP with S := { tinyLink with masksAhead := false } }
def blocks : List (Block _root_.Desc.K15.St Unit) := (_root_.Desc.K15.linkProtocolChain P').blocksInOrder
def p : P12 :=
  ((_root_.Desc.K15.numsOf P').map (H2U.proximityTestParametersAt ⟨1, none, 6, .K12⟩)).getD
    (H2U.noP12 ⟨1, none, 6, .K12⟩)
def blk : Block T12 Unit := proximityTestKind guardedProximityTestParts p

def frontRun (rs : List Fmt.RoundView) (q : List ℕ) :=
  foldBlocks 0 (blocks.take 6) (_root_.Desc.K15.first tinyCodes (keyOfT {} 0, keyOfT {} 1)) rs
    (storedAt q)

/-- The answer to the sending's sample for member t: the first sample row (`sampleRows`) of oracle
message t in the state that `frontRun` returns, evaluated at table t. `zeroE` where `frontRun` fails
or there is no such row. -/
def ans (t : ℕ) : E :=
  match frontRun (frontRounds {} zeroE zeroE) (qs {}) with
  | .ok x =>
    match (x.1.st.oracles.getD t default).sampleRows[0]? with
    | some row => evalMain row t (tabOf {} t) 16
    | none => zeroE
  | .error _ => zeroE

def seenFront : List Fmt.RoundView := frontRounds {} (ans 0) (ans 1)

def J : TestJob ℕ Unit where
  p := p
  members := [(sender, 0, ⟨0, 7⟩), (sender, 1, ⟨0, 7⟩)]
  fresh := none
  rec₀ := fun _ fr =>
    match frontRun fr.seen.rounds ((fr.heard.getD 3 ⟨[], [], [], none⟩).poss) with
    | .ok x => (_root_.Desc.K15.enter x.1).toOption.getD noRec
    | .error _ => noRec
  rows₀ := Toy.J.rows₀
  trees₀ := fun _ _ _ P =>
    [(4, fun x => wordsOf ([0, 1, 2, 4, 5, 6].map fun b => ofE (mainSym s0 P.tabM P.tM x b))),
     (4, freshCol s0 P)]

/-! ## 2 The random values and the book -/

def senderList : List X3 :=
  (List.range 2).flatMap fun t =>
    (List.range 3).flatMap (tailOfMem t) ++ [(rowOfMem {} t 2).getD 3 Fmt.Fld.zeroE]

/-- The first part's nine random values: the seven coefficients, in the order in which `hideAt`
(Coins.lean) reads them, then the table's row's tail. -/
def ownList : List X3 := [3, 4, 5, 6, 0, 7, 8].map (coin 130) ++ (p1 {}).Pi.getD 0 []

def a0 : Addr := ⟨p.place, 0⟩
def a1 : Addr := ⟨p.place, 1⟩

/-- The book. all: with the entry by which the second part is given the first part's nine values. -/
abbrev Bk (all : Bool) : ProverCoinCounts :=
  { first := [(sender, ⟨0, 14⟩), (a0, ⟨0, 9⟩), (a1, ⟨0, 125⟩)], shared := [], second := []
    ahead :=
      [⟨carriedName sender 0 a0, sender, ⟨0, 0⟩, ⟨0, 7⟩, a0, false⟩,
       ⟨carriedName sender 1 a0, sender, ⟨0, 7⟩, ⟨0, 7⟩, a0, false⟩,
       ⟨carriedName sender 0 a1, sender, ⟨0, 0⟩, ⟨0, 7⟩, a1, false⟩,
       ⟨carriedName sender 1 a1, sender, ⟨0, 7⟩, ⟨0, 7⟩, a1, false⟩] ++
      (if all then [⟨carriedName a0 0 a1, a0, ⟨0, 0⟩, ⟨0, 9⟩, a1, false⟩] else [])
    cuts := [(p.place, [5, 8])] }

def coinsT (all : Bool) (upO : Option ℕ) : Coins (Bk all) :=
  ⟨(csOf 14 senderList none, (csOf 9 ownList upO, (csOf 125 restList none, ()))), (), ()⟩

def half : Placed Unit ℕ Unit := proverSideOfProximityTest J

/-! ## 3 The play -/

def lent (all : Bool) (c : Coins (Bk all)) :=
  lendRow (Bk all) ((Bk all).rowsOf 0) (c.look 0) p.place half.parts 0

/-- The play of the test's rounds from the written state in front of it. The toy stands where no
column is handed: the state's field `opened` is `none`. -/
def played (c : Coins (Bk true)) (ds : List Fmt.Drawn) : Except String (List Played) :=
  match lent true c with
  | .error e => .error e
  | .ok h =>
    match play (half.steps blk (some ()) h) ds [] ⟨⟨0, front, ()⟩, front, seenFront, none⟩ with
    | .error e => .error e.words
    | .ok y => .ok y.1

structure Got where
  rs : List Fmt.RoundView
  t0 : ℕ → List UInt64
  t1 : ℕ → List UInt64
  t2 : ℕ → List UInt64

def gotOf (c : Coins (Bk true)) (ds : List Fmt.Drawn) : Got :=
  let l := (played c ds).toOption.getD []
  ⟨roundsOf l, tableAt l 1, tableAt l 5, tableAt l 9⟩

/-- What precedes the test in these plays. No column is handed in them: `Seen.bare`. -/
def fr : Front Unit := ⟨front, (), Seen.bare seenFront⟩

/-- The column of the sending's tree, computed by the job's `rows₀` and `trees₀`. -/
def col0 : ℕ → List UInt64 :=
  let S := stretchOf (csOf 14 senderList none)
  let mem : ℕ → Stretch := fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩
  ((J.trees₀ 0 fr mem (J.rows₀ 0 fr mem)).headD (0, fun _ => [])).2

def groups (G : Got) (ds : List Fmt.Drawn) : List (List (ℕ × List UInt64)) :=
  [groupAt 4 (possAt ds 6) col0, groupAt 4 (possAt ds 6) G.t0, groupAt 5 (possAt ds 10) G.t1,
    groupAt 7 (possAt ds 12) G.t2]

def verdict (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) : String :=
  if !roundsFit blk.rounds rs then "the rounds"
  else word (blk.decide (J.rec₀ 0 fr) (rs.map noDigest) gs)

def G₁ : Got := gotOf (coinsT true none) list₁
def G₂ : Got := gotOf (coinsT true none) list₂

def printLines : List String :=
  G₁.rs.zipIdx.map fun r => s!"round {r.2}: " ++ toString (r.1.vals.filterMap fun v =>
    match v with
    | .e x => some x
    | .answer x => some x
    | _ => none)

/-- The two parts of the same job with the parameters and the state on entry of Toy.lean, whose
`ownMask` is false: the table was sent before the test. -/
def halfBad : Placed Unit ℕ Unit := proverSideOfProximityTest { J with p := Toy.p, rec₀ := Toy.J.rec₀ }

/-- The play of `halfBad` from the written state. Here too no column is handed: the state's field
`opened` is `none`. -/
def playedBad : Except String (List Played) :=
  match lendRow (Bk true) ((Bk true).rowsOf 0) ((coinsT true none).look 0) p.place halfBad.parts
      0 with
  | .error e => .error e
  | .ok h =>
    match play (halfBad.steps Toy.blk (some ()) h) list₁ []
        ⟨⟨0, front, ()⟩, front, Toy.seenFront, none⟩ with
    | .error e => .error e.words
    | .ok y => .ok y.1

/-! ## 4 The tests -/

#guard p.nums.ownMask && p.early && blk.planOk && J.freshFits
#guard (J.rec₀ 0 fr).mask.isNone
#guard (blk.rounds.map (·.entry.roots)) == [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
#guard (blk.rounds.map (·.opens.length)) == [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 1]
#guard half.parts.map (·.takes) == [⟨0, 9⟩, ⟨0, 125⟩] && senderList.length == 14
#guard half.parts.map (·.moves.length) == [5, 8] && partsCut blk == [5, 8]
#guard strays blocks [half] == [] && roundsInFront blocks p.place == some 5
#guard word (played (coinsT true none) list₁) == "ok" && G₁.rs.length == 13
#guard word (played (coinsT true none) list₂) == "ok" && G₂.rs.length == 13
-- the block's `decide` accepts, at both lists
#guard verdict G₁.rs (groups G₁ list₁) == "ok"
#guard verdict G₂.rs (groups G₂ list₂) == "ok"
-- the sent elements are the other program's, for which the table was sent before the test
#guard G₁.rs.map (·.vals) == [] :: (testRounds {}).map (·.vals)
-- Negative tests. A word of an opened column of each of the four trees made one larger: rejected
#guard (let G := G₁; let gs := groups G list₁
  (List.range 4).all fun g => verdict G.rs (upCol g gs) != "ok")
-- each of the first part's nine random values made one larger in its own table alone: rejected
#guard (let G := G₁
  (List.range 9).all fun i =>
    verdict G.rs (groups { G with t0 := (gotOf (coinsT true (some i)) list₁).t0 } list₁) != "ok")
-- the job's `fresh` against `ownMask` of Toy.lean's parameters: `freshFits` is false, and `play`
-- returns its error on a message's shape
#guard !({ J with p := Toy.p } : TestJob ℕ Unit).freshFits
#guard word playedBad ==
  "the proximity test (chain 1, piece 6): the message has another shape than the " ++
    "sub-protocol states"
-- the book without the entry from the first part to the second: `lendRow` returns an error
#guard word (lent false (coinsT false none)) ==
  "part 1: it is typed at another number of entries than the book hands it"

end ProofFile.Honest.K12.ToyOwn

#print axioms ProofFile.Honest.K12.ToyOwn.P'
#print axioms ProofFile.Honest.K12.ToyOwn.blocks
#print axioms ProofFile.Honest.K12.ToyOwn.p
#print axioms ProofFile.Honest.K12.ToyOwn.blk
#print axioms ProofFile.Honest.K12.ToyOwn.frontRun
#print axioms ProofFile.Honest.K12.ToyOwn.ans
#print axioms ProofFile.Honest.K12.ToyOwn.seenFront
#print axioms ProofFile.Honest.K12.ToyOwn.J
#print axioms ProofFile.Honest.K12.ToyOwn.senderList
#print axioms ProofFile.Honest.K12.ToyOwn.ownList
#print axioms ProofFile.Honest.K12.ToyOwn.a0
#print axioms ProofFile.Honest.K12.ToyOwn.a1
#print axioms ProofFile.Honest.K12.ToyOwn.Bk
#print axioms ProofFile.Honest.K12.ToyOwn.coinsT
#print axioms ProofFile.Honest.K12.ToyOwn.half
#print axioms ProofFile.Honest.K12.ToyOwn.lent
#print axioms ProofFile.Honest.K12.ToyOwn.played
#print axioms ProofFile.Honest.K12.ToyOwn.Got
#print axioms ProofFile.Honest.K12.ToyOwn.gotOf
#print axioms ProofFile.Honest.K12.ToyOwn.fr
#print axioms ProofFile.Honest.K12.ToyOwn.col0
#print axioms ProofFile.Honest.K12.ToyOwn.groups
#print axioms ProofFile.Honest.K12.ToyOwn.verdict
#print axioms ProofFile.Honest.K12.ToyOwn.G₁
#print axioms ProofFile.Honest.K12.ToyOwn.G₂
#print axioms ProofFile.Honest.K12.ToyOwn.printLines
#print axioms ProofFile.Honest.K12.ToyOwn.halfBad
#print axioms ProofFile.Honest.K12.ToyOwn.playedBad
