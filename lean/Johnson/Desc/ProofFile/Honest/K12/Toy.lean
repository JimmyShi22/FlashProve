-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Toy.lean: tests (`#guard`) of `proverSideOfProximityTest` (Parts.lean), the two
parts of a proximity test's prover, at one small synthetic example. `lendRow` gives the parts their
random values, `Placed.steps` and `play` run them (all three:
Johnson/Desc/ProofFile/Honest/Frame.lean), and the test's block (`proximityTestKind guardedProximityTestParts p`,
Johnson/Desc/K12/) decides on what they send. Computable definitions and evaluations; no theorem.
Synthetic numbers alone: no model, no weights.

The example: the proximity test in the small synthetic link of Johnson/Prover/Link/ToyLink.lean,
which is a chain of blocks (`blocksT`). Three stages, (k, h) = (3, 0), (1, 1), (0, 0); 13 rounds, of
which the first part has 5 and the second 8. Five rounds of the chain precede the test. The group
has two members of three rows each, sent in one tree with the first fold's fresh table.

By what.
- What precedes the test: ToyLink.lean's five rounds (`frontRounds`) and stored columns (`colT`),
  unchanged.
- The job (`J`). The state on entry to the test (`rec₀`) is computed by `foldBlocks`
  (Johnson/Desc/Block.lean) over the chain's first six blocks, on the rounds shown before the test
  and on the stored columns at the positions that were sampled there, and then by `Desc.K15.enter`.
  The rows (`rows₀`) are the folds of ToyLink.lean's two tables at the element that the chain's
  first round sampled, with the pad and the tails taken from the members' random values. The
  prover's input is a number that is added to entry 0 of member 0.
- The random values: 23 of the sender's and 125 of the second part's, chosen to be those of another
  program: `Fmt.M1.Own.go`, which computes the proximity test in the prover of Fmt/M1Own.lean (in
  that file's words an honest prover for a toy of its own), in the call that ToyLink.lean makes
  (`out`).
- The book (`Bk`). A `ProverCoinCounts` (Frame.lean) is public data: how many random values each part has of its
  own, which stretches of them another part is given too (its entries), and how many rounds of a
  block each part has. Here it has two rows, six entries and the one list [5, 8], written by hand.

The order of the random values is tested in this way. The 125 values are listed by hand (`restList`)
in the order that the head of Coins.lean states, each written as `coin` (ToyLink.lean) at the tag
and index at which the other program reads it. If `coinsOf` read them in another order, the rounds
or the columns would differ from that program's. The same tests compare the two packings of a fresh
table, `packedN` (Johnson/Prover/Link/BodyPack.lean) and `freshRow` (Fmt/M1Fold.lean; see the head
of Test.lean), at the shapes (k, h) = (3, 0) and (1, 1).

What is checked.
- The counts of random values. The two parts' numbers of rounds, against `partsCut` of the block
  (Johnson/Desc/ProofFile/Honest/BookOf.lean). `lendRow` returns. The play returns at two lists of
  challenges; `play` itself checks that every message has the shape that the block declares.
- The block's `decide` accepts the played rounds with the columns of the played tables, at both
  lists.
- At the first list what the thirteen played rounds send is, word for word, what the other program
  sends ("BAT", which is not among that program's rounds, sends nothing), and so are the two played
  trees' columns at positions 0 to 15.
- Negative tests, each change alone. The first word of each sent element made one larger: rejected.
  A word of an opened column of each tree made one larger: rejected. The input made one larger:
  rejected. The book's count for the second part made one larger: `lendRow` returns an error. A
  random value of each kind made one larger in the trees' columns alone, with the rounds as played:
  rejected.

Limits.
- One example, two lists of challenges, one set of random values. No sampled element is 0 or 1.
- The first fold's fresh table was sent before the test, and one tree holds the first stage's rows.
  The other case, with two trees at the first opening, is played in ToyOwn.lean.
- The rows are over the extension field.
- The first tree's columns are computed by this file (`col0`, from the job's `trees₀`), not by the
  part that sends that tree.
- Of the three checks of a block's step (`Block.step`, Johnson/Desc/Block.lean) two are evaluated:
  the check on the rounds' form (`roundsFit`) and the block's `decide`. The check on the columns'
  keys, positions and widths is not.
- The lists of opened columns are built by this file (`groups`), at written depths and rounds, from
  the played tables. The lists that `testAll` computes are not given to the block here.
- The checks on a book (`ProverCoinCounts.clauses`, Frame.lean) are not evaluated at the book written here.
- A test (`#guard`) is run by Lean's evaluator (compiled code, outside the kernel) while the file
  compiles; it leaves no theorem.
- That the block accepts is a test at one example. Nothing on completeness, on soundness or on what
  any sent value shows or does not show.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Prover.Link.ToyParts
import Johnson.Desc.ProofFile.Honest.BookOf

set_option autoImplicit false

namespace ProofFile.Honest.K12.Toy
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS BOut groupAt mainSym freshSym wordsOf)
open Johnson.Prover.Link.Toy (tinyP tinyCodes blocksT keyOfT msgOfT tlOfT colT sortU dr eN coin
  gamma seedZ seedB qs phi theta0 vsT frontRounds ansOf tailOfMem rowOfMem p1 testRounds out X3)
open H2K.Pub (sgOf)

/-! ## 1 The example and the job -/

def p : P12 := Johnson.Prover.Link.Toy.p12
def stages : List Fmt.M1.Stage := p.nums.stages
def s0 : Sg := sgOf (stages.headD default)
def blk : Block T12 Unit := proximityTestKind guardedProximityTestParts p
def sender : Addr := ⟨⟨1, none, 2, .K1⟩, 0⟩

/-- The fold of two numbers at a sampled element. -/
def foldAt (g : List E) (l : ℕ → UInt64) : GE :=
  readE (((List.range 2).map fun b =>
    mulE ((eqTable g).getD b zeroE) (OnBytes.ofF (l b))).foldl addE zeroE)

/-- Entry n of member t: entries 0 to 7 are the folded message, 8 and 9 the folded tail, 10 is a
synthetic free entry, and from 11 on it is the pad. The input w is added to entry 0 of member 0. -/
def entry (w : ℕ) (g : List E) (mem : ℕ → Stretch) (t n : ℕ) : GE :=
  if n < 8 then
    foldAt g (fun b => (msgOfT {} t b).getD n 0) + (if t = 0 ∧ n = 0 then (w : GE) else 0)
  else if n < 10 then foldAt g fun b => (tlOfT t b).getD (n - 8) 0
  else if n = 10 then readE (eN (70 + t) 1 1)
  else (mem t).e 6

/-- The stored columns at sampled positions. -/
def storedAt (q : List ℕ) : List (ℕ × ℕ × List UInt64) :=
  (sortU (q.take 2)).map (fun x => (Fmt.storedKey 0, x, colT {} 0 x)) ++
    (sortU (q.drop 2)).map fun x => (Fmt.storedKey 1, x, colT {} 1 x)

def noRec : T12 :=
  { st := default, book := default, roots := 0, g := 0, pass := .nothing, mask := none }

def J : TestJob ℕ Unit where
  p := p
  members := [(sender, 0, ⟨0, 7⟩), (sender, 1, ⟨0, 7⟩)]
  fresh := some (sender, 2)
  rec₀ := fun _ fr =>
    match foldBlocks 0 (blocksT.take 6) (_root_.Desc.K15.first tinyCodes (keyOfT {} 0, keyOfT {} 1))
        fr.seen.rounds (storedAt ((fr.heard.getD 3 ⟨[], [], [], none⟩).poss)) with
    | .ok x => (_root_.Desc.K15.enter x.1).toOption.getD noRec
    | .error _ => noRec
  rows₀ := fun w fr mem =>
    let g := (fr.heard.getD 0 ⟨[], [], [], none⟩).elems.map E.ofTriple
    { tabM := fun i =>
        if i % 8 % 4 < 3 ∧ i / 8 < 4 then entry w g mem (i % 8 / 4) (i % 8 % 4 * 4 + i / 8) else 0
      tabZ := fun _ => 0
      tM := fun b q => if b % 4 < 3 then (mem (b / 4)).e (b % 4 * 2 + q) else 0
      tZ := fun _ _ => 0, fM := fun _ _ => 0, fT := fun _ _ => 0, sM := fun _ => 0
      sT := fun _ => 0 }
  trees₀ := fun _ _ _ P =>
    [(4, fun x => wordsOf ([0, 1, 2, 4, 5, 6].map (fun b => ofE (mainSym s0 P.tabM P.tM x b)) ++
      [ofE (freshSym s0 P.fM P.fT x 0)]))]

/-! ## 2 The random values and the book -/

/-- The sender's 23 random values: for each member its three rows' tails and its pad; then the fresh
table's seven coefficients, in the order in which `hideAt` (Coins.lean) reads them, and its row's
tail. -/
def senderList : List X3 :=
  (List.range 2).flatMap (fun t =>
    (List.range 3).flatMap (tailOfMem t) ++ [(rowOfMem {} t 2).getD 3 Fmt.Fld.zeroE]) ++
  [3, 4, 5, 6, 0, 7, 8].map (coin 130) ++ (p1 {}).Pi.getD 0 []

def cs (tag n : ℕ) : List X3 := (List.range n).map (coin tag)

/-- The second part's 125 random values, each written as `coin` at the tag and index at which the
other program (`Fmt.M1.Own.go`) reads it. -/
def restList : List X3 :=
  cs 200 2 ++ cs 201 2 ++ cs 250 9 ++ [coin 251 0] ++ cs 220 2 ++ cs 221 2 ++
    [0, 3, 4].map (coin 230) ++ cs 240 2 ++ cs 241 2 ++
  cs 300 2 ++ cs 350 25 ++ [coin 351 0] ++ cs 320 2 ++ cs 362 2 ++ cs 360 2 ++ cs 361 64 ++ cs 363 2

def a0 : Addr := ⟨p.place, 0⟩
def a1 : Addr := ⟨p.place, 1⟩

abbrev Bk (more : ℕ) : ProverCoinCounts :=
  { first := [(sender, ⟨0, 23⟩), (a1, ⟨0, 125 + more⟩)], shared := [], second := []
    ahead :=
      [⟨runName foldMaskRun a0 "fold", sender, ⟨0, 14⟩, ⟨0, 7⟩, a0, true⟩,
       ⟨carriedName sender 0 a0, sender, ⟨0, 0⟩, ⟨0, 7⟩, a0, false⟩,
       ⟨carriedName sender 1 a0, sender, ⟨0, 7⟩, ⟨0, 7⟩, a0, false⟩,
       ⟨carriedName sender 0 a1, sender, ⟨0, 0⟩, ⟨0, 7⟩, a1, false⟩,
       ⟨carriedName sender 1 a1, sender, ⟨0, 7⟩, ⟨0, 7⟩, a1, false⟩,
       ⟨carriedName sender 2 a1, sender, ⟨0, 14⟩, ⟨0, 9⟩, a1, false⟩]
    cuts := [(p.place, [5, 8])] }

/-- A list as n random values of the extension field, 0 beyond the list's end. The value number
`up`, if any, is made one larger. -/
def csOf (n : ℕ) (l : List X3) (up : Option ℕ) : Cs ⟨0, n⟩ :=
  ⟨fun i => i.elim0, fun i => toE (l.getD i.val Fmt.Fld.zeroE) + if up == some i.val then 1 else 0⟩

/-- The random values of a play. upS, upR: the number of one of the sender's values, and of one of
the second part's, that is made one larger. -/
def coinsT (upS upR : Option ℕ) : Coins (Bk 0) :=
  ⟨(csOf 23 senderList upS, (csOf 125 restList upR, ())), (), ()⟩

def half : Placed Unit ℕ Unit := proverSideOfProximityTest J

/-! ## 3 The challenges -/

def front : List Fmt.Drawn := [dr gamma, dr (seedZ ++ [seedB]), dr [], dr [] (qs {}), dr phi]
def seenFront : List Fmt.RoundView := frontRounds {} (ansOf {} 0) (ansOf {} 1)

def list₁ : List Fmt.Drawn :=
  dr [theta0] :: (vsT {}).map fun v => ⟨v.els, v.poss, [], none⟩
/-- The second list: every sampled element differs from that of `list₁`, and each list of positions
holds one position twice. -/
def list₂ : List Fmt.Drawn :=
  dr [eN 8 1 5] :: (vsT { alt := true }).map fun v =>
    ⟨v.els.map fun x => (x.1 + 100, x.2.1 + 7, x.2.2 + 3), v.poss, [], none⟩

/-! ## 4 The play -/

/-- The play of the test's rounds from the written state in front of it. The toy stands where no
column is handed: the state's field `opened` is `none`. -/
def played (w : ℕ) (c : Coins (Bk 0)) (ds : List Fmt.Drawn) : Except String (List Played) :=
  match lendRow (Bk 0) ((Bk 0).rowsOf 0) (c.look 0) p.place half.parts 0 with
  | .error e => .error e
  | .ok h =>
    match play (half.steps blk (some ()) h) ds [] ⟨⟨w, front, ()⟩, front, seenFront, none⟩ with
    | .error e => .error e.words
    | .ok y => .ok y.1

def word {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => e

/-- What the tests read of a play: the rounds, and the columns of the two trees sent in the test. -/
structure Got where
  rs : List Fmt.RoundView
  t1 : ℕ → List UInt64
  t2 : ℕ → List UInt64

def tableAt (l : List Played) (i : ℕ) (x : ℕ) : List UInt64 :=
  (((l[i]?).bind fun q => q.tables.head?.join).map fun t => t.col x).getD []

def gotOf (w : ℕ) (c : Coins (Bk 0)) (ds : List Fmt.Drawn) : Got :=
  let l := (played w c ds).toOption.getD []
  ⟨roundsOf l, tableAt l 5, tableAt l 9⟩

/-- What precedes the test, as `moveAt` (Parts.lean) passes it on in these plays. No column is
handed in them: `Seen.bare`. -/
def fr : Front Unit := ⟨front, (), Seen.bare seenFront⟩

/-- The first tree's column, computed by the job's `first` and `trees₀` at the input w and the
sender's random values. upS: as in `coinsT`. -/
def col0 (w : ℕ) (upS : Option ℕ) : ℕ → List UInt64 :=
  let S := stretchOf (csOf 23 senderList upS)
  let C : TestCoins :=
    ⟨fun i => S.e (14 + i), fun _ q => S.e (21 + q),
      fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩, fun _ => 0⟩
  ((J.trees₀ w fr C.mem (J.first w fr C)).headD (0, fun _ => [])).2

def possAt (ds : List Fmt.Drawn) (i : ℕ) : List ℕ := (ds.getD i ⟨[], [], [], none⟩).poss

/-- The opened columns, one list for each tree, in the order of the openings. The depths 4, 5, 7 and
the rounds 6, 10, 12 are written by hand. -/
def groups (c0 t1 t2 : ℕ → List UInt64) (ds : List Fmt.Drawn) : List (List (ℕ × List UInt64)) :=
  [groupAt 4 (possAt ds 6) c0, groupAt 5 (possAt ds 10) t1, groupAt 7 (possAt ds 12) t2]

/-- **The block's decision**, as text: "the rounds" where `roundsFit` fails; otherwise "ok" or the
error of the block's `decide` at the state `J.rec₀ 0 fr`. -/
def verdict (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) : String :=
  if !roundsFit blk.rounds rs then "the rounds"
  else word (blk.decide (J.rec₀ 0 fr) (rs.map noDigest) gs)

def G₁ : Got := gotOf 0 (coinsT none none) list₁
def G₂ : Got := gotOf 0 (coinsT none none) list₂

def saysAt (G : Got) (ds : List Fmt.Drawn) : String :=
  verdict G.rs (groups (col0 0 none) G.t1 G.t2 ds)

/-- The elements and answers sent in the play at `list₁`, round by round, as text. -/
def printLines : List String :=
  G₁.rs.zipIdx.map fun r => s!"round {r.2}: " ++ toString (r.1.vals.filterMap fun v =>
    match v with
    | .e x => some x
    | .answer x => some x
    | _ => none)

/-! ## 5 Changes for the negative tests -/

/-- Item j of round i with its first word made one larger, if it is an element or an answer. -/
def upVal (i j : ℕ) (rs : List Fmt.RoundView) : List Fmt.RoundView :=
  rs.modify i fun r => { r with vals := r.vals.modify j Johnson.Prover.Link.Toy.up }

/-- Word 0 of the first column of list number g made one larger. -/
def upCol (g : ℕ) (gs : List (List (ℕ × List UInt64))) : List (List (ℕ × List UInt64)) :=
  gs.modify g fun l => l.modify 0 fun x => (x.1, x.2.modify 0 (· + 1))

/-- All (round, item) of a list of rounds. -/
def items (rs : List Fmt.RoundView) : List (ℕ × ℕ) :=
  rs.zipIdx.flatMap fun r => (List.range r.1.vals.length).map fun j => (r.2, j)

/-- `testAll` at a whole list of sampled challenges, the input 0 and the example's random values. -/
def whole (ds : List Fmt.Drawn) : BOut :=
  let S := stretchOf (csOf 23 senderList none)
  testAll J 0 fr
    ⟨fun i => S.e (14 + i), fun _ q => S.e (21 + q),
      fun t => ⟨fun _ => 0, fun i => S.e (7 * t + i)⟩, (stretchOf (csOf 125 restList none)).e⟩
    fun r => ds.getD r ⟨[], [], [], none⟩

/-- The number of one random value of each kind among the second part's: for each switch a main
row's tail, a free entry, the pad, a mask row's tail; the next fold's three coefficients and a tail
of its table; the masking word's main tail, main message, mask message, mask tail. -/
def sorts : List ℕ := [0, 4, 13, 14, 18, 19, 20, 21, 25, 27, 52, 53, 55, 57, 59, 123]

/-! ## 6 The tests -/

-- the counts: 25 + 100; 2 * (3 * 2 + 1) + (7 + 2)
#guard dueRest stages == 125 && restList.length == 125 && senderList.length == 23
#guard (marksAt stages 0).free == 4 && (marksAt stages 0).ride == 18 &&
  (marksAt stages 1).main == 25
-- the two parts have 5 and 8 rounds, as `partsCut` gives for the block and `cutsIn` for the chain
-- (the book's `cuts` is the same written list; no test here reads it); the pair's place is that of
-- a block of the chain
#guard half.parts.map (·.moves.length) == [5, 8] && partsCut blk == [5, 8]
#guard strays blocksT [half] == [] && (cutsIn blocksT).lookup p.place == some [5, 8]
-- the job reads two of the challenges before the test, by number: 0, the chain's first round, and
-- 3, the round that samples the stored tables' positions
#guard ((blocksT.flatMap (·.rounds)).map (·.entry.name)).take 6 ==
  ["LINK point", "SEND seed", "SEND answer", "LINK", "LINK phi", "BAT"]
#guard roundsInFront blocksT p.place == some 5
#guard blk.planOk && J.freshFits
-- a job whose `fresh` is none (the fold sends its own table), at these parameters: `freshFits` is
-- false (what `play` then does: Johnson/Desc/ProofFile/Honest/K12/ToyOwn.lean)
#guard !({ J with fresh := none } : TestJob ℕ Unit).freshFits
-- the play returns, thirteen rounds, at both lists
#guard word (played 0 (coinsT none none) list₁) == "ok" && G₁.rs.length == 13
#guard word (played 0 (coinsT none none) list₂) == "ok" && G₂.rs.length == 13
-- the block's `decide` accepts, at both lists
#guard saysAt G₁ list₁ == "ok"
#guard saysAt G₂ list₂ == "ok"
-- the two lists give different sent items
#guard G₁.rs.map (·.vals) != G₂.rs.map (·.vals)
-- at the first list the sent items and the columns are the other program's, word for word
#guard G₁.rs.map (·.vals) == [] :: (testRounds {}).map (·.vals)
#guard (List.range 16).all fun x => col0 0 none x == Johnson.Prover.Link.Toy.col0 {} x
#guard (List.range 16).all fun x =>
  G₁.t1 x == ((out {}).cols.getD 1 fun _ => []) x && G₁.t2 x == ((out {}).cols.getD 2 fun _ => []) x
-- what the rounds send when played one by one is what `testAll` gives at the whole list, at both
-- lists
#guard G₁.rs.map (·.vals) == (whole list₁).rs.map (·.vals)
#guard G₂.rs.map (·.vals) == (whole list₂).rs.map (·.vals)
-- Negative tests. The first word of each sent element made one larger, each alone: rejected. There
-- are 7 + 1 + 3 + 1 + 1 + 70 such elements
#guard (items G₁.rs).length == 83
#guard (let G := G₁; let gs := groups (col0 0 none) G.t1 G.t2 list₁
  (items G.rs).all fun x => verdict (upVal x.1 x.2 G.rs) gs != "ok")
-- a word of an opened column of each tree made one larger: rejected
#guard (let G := G₁; let gs := groups (col0 0 none) G.t1 G.t2 list₁
  (List.range 3).all fun g => verdict G.rs (upCol g gs) != "ok")
-- the last round left out: "the rounds"
#guard verdict G₁.rs.dropLast (groups (col0 0 none) G₁.t1 G₁.t2 list₁) == "the rounds"
-- the input made one larger, with the rounds and all columns computed from it: rejected
#guard (let G := gotOf 1 (coinsT none none) list₁
  verdict G.rs (groups (col0 1 none) G.t1 G.t2 list₁) != "ok")
-- each of the sender's 23 random values made one larger in the first tree alone: rejected
#guard (let G := G₁
  (List.range 23).all fun i => verdict G.rs (groups (col0 0 (some i)) G.t1 G.t2 list₁) != "ok")
-- a random value of each kind of the second part's made one larger in the two trees alone, with the
-- rounds as played: rejected
#guard (let G := G₁
  sorts.all fun i =>
    let H := gotOf 0 (coinsT none (some i)) list₁
    verdict G.rs (groups (col0 0 none) H.t1 H.t2 list₁) != "ok")
-- with the rounds and the two trees all computed from the changed value: accepted
#guard sorts.all fun i => saysAt (gotOf 0 (coinsT none (some i)) list₁) list₁ == "ok"
-- a book that has one value more for the second part: `lendRow` returns an error
#guard word (lendRow (Bk 1) ((Bk 1).rowsOf 0)
    ((⟨(csOf 23 senderList none, (csOf 126 restList none, ())), (), ()⟩ : Coins (Bk 1)).look 0)
    p.place half.parts 0) == "part 1: it takes more or fewer coins than the book has for it"

end ProofFile.Honest.K12.Toy

#print axioms ProofFile.Honest.K12.Toy.p
#print axioms ProofFile.Honest.K12.Toy.stages
#print axioms ProofFile.Honest.K12.Toy.s0
#print axioms ProofFile.Honest.K12.Toy.blk
#print axioms ProofFile.Honest.K12.Toy.sender
#print axioms ProofFile.Honest.K12.Toy.foldAt
#print axioms ProofFile.Honest.K12.Toy.entry
#print axioms ProofFile.Honest.K12.Toy.storedAt
#print axioms ProofFile.Honest.K12.Toy.noRec
#print axioms ProofFile.Honest.K12.Toy.J
#print axioms ProofFile.Honest.K12.Toy.senderList
#print axioms ProofFile.Honest.K12.Toy.cs
#print axioms ProofFile.Honest.K12.Toy.restList
#print axioms ProofFile.Honest.K12.Toy.a0
#print axioms ProofFile.Honest.K12.Toy.a1
#print axioms ProofFile.Honest.K12.Toy.Bk
#print axioms ProofFile.Honest.K12.Toy.csOf
#print axioms ProofFile.Honest.K12.Toy.coinsT
#print axioms ProofFile.Honest.K12.Toy.half
#print axioms ProofFile.Honest.K12.Toy.front
#print axioms ProofFile.Honest.K12.Toy.seenFront
#print axioms ProofFile.Honest.K12.Toy.list₁
#print axioms ProofFile.Honest.K12.Toy.list₂
#print axioms ProofFile.Honest.K12.Toy.played
#print axioms ProofFile.Honest.K12.Toy.word
#print axioms ProofFile.Honest.K12.Toy.Got
#print axioms ProofFile.Honest.K12.Toy.tableAt
#print axioms ProofFile.Honest.K12.Toy.gotOf
#print axioms ProofFile.Honest.K12.Toy.fr
#print axioms ProofFile.Honest.K12.Toy.col0
#print axioms ProofFile.Honest.K12.Toy.possAt
#print axioms ProofFile.Honest.K12.Toy.groups
#print axioms ProofFile.Honest.K12.Toy.verdict
#print axioms ProofFile.Honest.K12.Toy.G₁
#print axioms ProofFile.Honest.K12.Toy.G₂
#print axioms ProofFile.Honest.K12.Toy.saysAt
#print axioms ProofFile.Honest.K12.Toy.printLines
#print axioms ProofFile.Honest.K12.Toy.upVal
#print axioms ProofFile.Honest.K12.Toy.upCol
#print axioms ProofFile.Honest.K12.Toy.items
#print axioms ProofFile.Honest.K12.Toy.whole
#print axioms ProofFile.Honest.K12.Toy.sorts
