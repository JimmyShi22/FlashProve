-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Three/Data.lean: the three chains of one file (a key file, a proof file) as one piece of
plain data.

From the rounds that three dry runs of the verifier's blocks state, to three lists of rounds' data
with a list of trees a round, every tree named by one number over the whole file, and one table of
the trees. No wire, no typed round, no protocol: numbers, lists and the format's own records.
Definitions alone.

Why. Run/PlanQTypes.lean's `rds` turns one chain's description into rounds' data, for a chain that
stands alone: it has one tree a round, gives a tree that its own chain never opens a stand-in shape,
drops the openings of trees that a chain takes over from an earlier one, and counts trees from 0 in
each chain. Laid behind each other, the three chains of a file have none of these troubles: a tree
that is taken over is a tree that an earlier chain has sent.

Main definitions.
  `tagRoot`, `tagRun`, `tagChain`: made-up names for the trees of the first two chains. A
    description is fixed before any root is, so the third chain's dry run is made at names that say
    which tree is meant: the root is n + 1 zero bytes, the start the one byte c.
  `named`, `wholeNo`: which tree a name stands for (chain, number in the chain); its number over
    the whole file.
  `RDL`: a round's data: the plan's entry, the kind, the items, the shapes of the trees whose roots
    the round sends, the trees opened at its draws by their numbers over the whole file, the stored
    tables opened behind it.
  `Tree`: a row of the one table: which chain sends the tree, in which round, at which place among
    that round's roots; its shape, with the number that the format writes into its leaves' labels;
    where it is opened.
  `Whole`, `Whole.of`: the three lists and the table, from three lists of rounds.
  `Whole.stretch₁`, `Whole.seal₁`: the first chain without its sealing round, and that round.
  `Whole.fits`: the limits of the map, as a test.
  `dry3`: the three lists of rounds of a file, from the blocks' dry runs.

Two numbers of a tree are not one: its number over the whole file (the place in the table) and the
number in its leaves' labels (`Fmt.Shape.tree`). The third chain's j-th own tree has t₁ + t₂ + j in
the whole and t₁ + 1 + j in its leaves; two trees of the table can bear one label's number. A leaf's
start is the run's value of the chain that sent the tree (`Tree.chain`), also where a later chain
opens it.

What is not said. That the rounds by which the verifier's reader goes (made at the file's own roots)
are these rounds with each made-up name replaced. Nothing on seams, seals, the slot, the first calls
of the three chains. Nothing on soundness.


-/
import OnBytes.Proof.Tail

set_option autoImplicit false

namespace OnBytes.Three

open OnBytes.Params (Rounds)

/-! ## Made-up names -/

/-- The made-up root of the tree number n: n + 1 zero bytes. -/
def tagRoot (n : Nat) : ByteArray := ⟨Array.replicate (n + 1) 0⟩

/-- The made-up start of the trees of the chain c: the one byte c. -/
def tagRun (c : UInt8) : ByteArray := ⟨#[c]⟩

/-- A stand-in for a chain as read whose N trees have made-up names. -/
def tagChain (c : UInt8) (N : Nat) : ChainRead where
  out :=
    { pd := .empty, run := some (tagRun c), rho0 := .empty, rho := .empty, seen := []
      rounds := #[{ msg := .empty, vals := (List.range N).map fun n => .root (tagRoot n), nonce := 0
                    drawn := ⟨[], [], [], none⟩, list := [], opens := [] }] }
  view := ⟨[], []⟩
  next := 0

/-- Which tree a name stands for: the chain (0, 1, 2) that sent it and its number in that chain.
here: the chain in which the name is met. Nothing for a name that is neither the
chain's own nor made up. -/
def named (here : Nat) : Fmt.Src → Option (Nat × Nat)
  | .own n => some (here, n)
  | .given r s =>
    if r.size = 0 then none
    else if s == tagRun 1 then some (0, r.size - 1)
    else if s == tagRun 2 then some (1, r.size - 1)
    else none

/-- The number over the whole file. t₁, t₂: the numbers of trees that the first and the second
chain send. -/
def wholeNo (t₁ t₂ : Nat) (x : Nat × Nat) : Nat :=
  (match x.1 with
    | 0 => 0
    | 1 => t₁
    | _ => t₁ + t₂) + x.2

/-! ## Rounds -/

/-- A round's data, with a list of trees. -/
structure RDL where
  entry : Fmt.Entry
  kind : Fmt.Kind
  items : List Fmt.Item
  /-- the shapes of the trees whose roots this round sends, in the order of sending -/
  trees : List Fmt.Shape
  /-- the trees that are opened at this round's drawn positions, by their numbers over the whole
  file, in the file's order -/
  opens : List Nat
  /-- the stored tables that are opened behind it -/
  stored : List Fmt.Stored

/-- The number of roots that a list of rounds sends. -/
def rootsIn (R : Rounds) : Nat := (R.map fun r => r.1.items.countP (· == .root)).sum

/-- All openings of a chain: the tree's number over the whole file, the shape, the round. An
opening under a name that stands for no tree is left out (Whole.fits says no of it). -/
def opensOf (t₁ t₂ here : Nat) (R : Rounds) : List (Nat × Fmt.Shape × Nat × Nat) :=
  R.zipIdx.flatMap fun r => r.1.1.opens.filterMap fun o =>
    (named here o.2).map fun x => (wholeNo t₁ t₂ x, o.1, here, r.2)

/-- The shape under which tree j is opened, or dflt if no round opens it. -/
def shapeAt (all : List (Nat × Fmt.Shape × Nat × Nat)) (j : Nat) (dflt : Fmt.Shape) : Fmt.Shape :=
  ((all.find? (·.1 == j)).map (·.2.1)).getD dflt

/-- The shape that stands in for a tree that no round of the file opens: depth 0, one word a
column, under the tree's own number in the labels. (Run/PlanQTypes.lean's bareShape, said again so
that nothing of
Run/ lies below this file.) -/
def bareShape (first n : Nat) : Fmt.Shape := ⟨0, 1, false, first + n⟩

/-- For each round the number of trees that the chain has sent before it. (By a fold and not by
recursion over the list: a chain of the full size has some 48,000 rounds.) -/
def sentBefore (R : Rounds) : List Nat :=
  (R.foldl (fun (a : Nat × Array Nat) r => (a.1 + r.1.items.countP (· == .root), a.2.push a.1))
    (0, #[])).2.toList

/-- One round's data. sent: the number of trees that the chain has sent before it. -/
def rdOf (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (r : Fmt.Round × List Fmt.Stored) (sent : Nat) : RDL :=
  ⟨r.1.entry, r.1.kind, r.1.items,
    (List.range (r.1.items.countP (· == .root))).map fun i =>
      shapeAt all (base + sent + i) (bareShape first (sent + i)),
    r.1.opens.filterMap fun o => (named here o.2).map (wholeNo t₁ t₂), r.2⟩

/-- The rounds' data of one chain. all: the openings of all three chains. base: the number of trees
that the earlier chains send. first: the number in the label of the chain's first own
tree. -/
def rdsFromL (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat) (R : Rounds) :
    List RDL :=
  List.zipWith (rdOf all t₁ t₂ here base first) R (sentBefore R)

/-! ## The one table of the trees -/

/-- A tree of the file. -/
structure Tree where
  /-- the chain that sends its root: 0, 1, 2; the run's value of that chain is the start of its
  leaves' hashes -/
  chain : Nat
  /-- the round of that chain whose message holds the root -/
  round : Nat
  /-- the root's place among that message's roots -/
  k : Nat
  /-- depth, width, and the number in the leaves' labels -/
  shape : Fmt.Shape
  /-- where it is opened: (chain, round), in the file's order -/
  openedAt : List (Nat × Nat)

def treesOfChain (all : List (Nat × Fmt.Shape × Nat × Nat)) (here base : Nat) (ds : List RDL) :
    List Tree :=
  let rows := ds.zipIdx.flatMap fun d => d.1.trees.zipIdx.map fun s => (d.2, s.2, s.1)
  rows.zipIdx.map fun x =>
    ⟨here, x.1.1, x.1.2.1, x.1.2.2, (all.filter (·.1 == base + x.2)).map (·.2.2)⟩

/-! ## The whole -/

/-- The three chains of one file as plain data. -/
structure Whole where
  ds₁ : List RDL
  ds₂ : List RDL
  ds₃ : List RDL
  /-- the trees; a tree's number over the whole file is its place here -/
  table : List Tree
  /-- the numbers of trees that the three chains send -/
  t₁ : Nat
  t₂ : Nat
  t₃ : Nat
  /-- all openings: the tree's number, the shape under which it is opened, the chain, the round -/
  opens : List (Nat × Fmt.Shape × Nat × Nat)

/-- The number in the label of the third chain's first own tree: behind the first chain's trees and
the one tree that is taken over from the second chain
(OnBytes/Proof/Tail.lean, secondFirstTree). -/
def first₃ (t₁ : Nat) : Nat := t₁ + 1

/-- From three lists of rounds. -/
def Whole.of (R₁ R₂ R₃ : Rounds) : Whole :=
  let t₁ := rootsIn R₁
  let t₂ := rootsIn R₂
  let all := opensOf t₁ t₂ 0 R₁ ++ (opensOf t₁ t₂ 1 R₂ ++ opensOf t₁ t₂ 2 R₃)
  let ds₁ := rdsFromL all t₁ t₂ 0 0 0 R₁
  let ds₂ := rdsFromL all t₁ t₂ 1 t₁ 0 R₂
  let ds₃ := rdsFromL all t₁ t₂ 2 (t₁ + t₂) (first₃ t₁) R₃
  ⟨ds₁, ds₂, ds₃,
    treesOfChain all 0 0 ds₁ ++ (treesOfChain all 1 t₁ ds₂ ++ treesOfChain all 2 (t₁ + t₂) ds₃),
    t₁, t₂, rootsIn R₃, all⟩

namespace Whole
variable (W : Whole)

/-- A chain's rounds. -/
def ds : Nat → List RDL
  | 0 => W.ds₁
  | 1 => W.ds₂
  | _ => W.ds₃

/-- The first chain's rounds WITHOUT ITS LAST, the round in which the chain is sealed: in a
protocol of three stretches (local, shared, local) that round is no written round of the first
stretch: it is the joining
round. The second chain's sealing round stays the last written round of the second stretch. -/
def stretch₁ : List RDL := W.ds₁.dropLast

/-- The round in which the first chain is sealed. -/
def seal₁ : Option RDL := W.ds₁.getLast?

/-- (chain, round) before (chain, round), in the file's order; a tree may be opened in the round
that sends it. -/
def notLater (a b : Nat × Nat) : Bool := decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- In view c the key of a tree is the number in its label less the number in the label of the
chain's first own tree, cut off at 0, as the program has it
(OnBytes/Iop/Ground.lean, Blk.takeColumns). -/
def key (c j : Nat) : Nat :=
  ((W.table[j]?).map (·.shape.tree)).getD 0 - (if c = 2 then first₃ W.t₁ else 0)

end Whole

/-- The limits of the map, as a test. maxRt: the most roots in one message. (1) no message has
more roots than maxRt, and an entry counts its message's roots; (2) every name of an
opening stands for a tree; the first two chains name their own trees alone; (3) every opened tree
is in the table and was sent no later than it is opened; (4) a tree that is opened more
than once has one shape; (5) the number in an own tree's label is as the format has it; (6) the
first and the second chain end in a round of the kind "sealed", which has no item, sends no root,
opens nothing, asks for no work and draws no element, position or matrix entry, and no other round
of the file is of that kind. -/
def Whole.fits (R₁ R₂ R₃ : Rounds) (maxRt : Nat) : Bool :=
  let W := Whole.of R₁ R₂ R₃
  let Rs := [(0, R₁), (1, R₂), (2, R₃)]
  (Rs.all fun x => x.2.all fun r =>
    decide (r.1.items.countP (· == .root) ≤ maxRt) && r.1.items.countP (· == .root) ==
    r.1.entry.roots) &&
  (Rs.all fun x => x.2.all fun r => r.1.opens.all fun o =>
    match named x.1 o.2 with
    | none => false
    | some y => (x.1 == 2 || y.1 == x.1) && decide (y.1 ≤ x.1)) &&
  (W.opens.all fun o =>
    match W.table[o.1]? with
    | none => false
    | some t => Whole.notLater (t.chain, t.round) o.2.2 && t.shape == o.2.1) &&
  (W.table.zipIdx.all fun t =>
    t.1.openedAt.isEmpty ||
      t.1.shape.tree == (match t.1.chain with
        | 0 => t.2
        | 1 => t.2 - W.t₁
        | _ => first₃ W.t₁ + (t.2 - (W.t₁ + W.t₂)))) &&
  ([R₁, R₂].all fun R => match R.getLast? with
    | some r => r.1.kind == .sealed && r.1.opens.isEmpty && r.1.entry.roots == 0 && r.2.isEmpty &&
        r.1.items.isEmpty && r.1.entry.work == 0 && r.1.entry.drawE == 0 && r.1.entry.drawNZ == 0 &&
        r.1.entry.poss == 0 && r.1.entry.trits == 0
    | none => false) &&
  ([R₁.dropLast, R₂.dropLast, R₃].all fun R => R.all fun r => r.1.kind != .sealed)

/-! ## The program's three dry runs -/

open OnBytes.Proof (TailPublic FirstEnd sharedBlock secondBlock sharedStart secondStart)

/-- The three lists of rounds of a file, the third at the made-up names. x₁: what the dry run
of the first chain's block has returned. -/
def dry3 (p : TailPublic) (key : TableKey) (x₁ : Rounds × FirstEnd) :
    Option (Rounds × Rounds × Rounds) := do
  let x₂ ← (sharedBlock p.lin key).dryRun (sharedStart p)
  let R₃ ← (secondBlock p.lin x₁.2.lin (x₂.2.goesOn (tagChain 2 (rootsIn x₂.1)))).rounds
    (secondStart p x₁.2 (tagChain 1 (rootsIn x₁.1)))
  pure (x₁.1, x₂.1, R₃)

end OnBytes.Three
