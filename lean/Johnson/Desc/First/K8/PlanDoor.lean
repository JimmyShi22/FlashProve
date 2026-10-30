-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PlanDoor.lean: THE SMALLNESS TEST: THREE PUBLIC TESTS WITH CODE ON A FILE'S
DESCRIPTION ALONE: the tests of Johnson/Desc/First/K8/PlanNames.lean in a form that takes no number
of a place from outside: what they need of a place they read off the description's own entries.
DEFINITIONS. NO THEOREM HERE. NO SOUNDNESS IS CLAIMED.

Why. `namesB F p iM iR` takes the place's numbers p and two indices as letters. A test that a
verifier is to ask of its description has the description alone. The entry of the kind K8 carries
its place's two lists itself: its field `before` is `(p.matsIn ++ p.readsIn).map fun n => (1, n)`
(Johnson/Desc/First/K8/Hear.lean).

  `drawIxs F`: the indices, in the first chain's flat list, of the entries whose place is of the
    kind K8.
  `sentBy F i`: the numbers of the trees that entry i's own declared rounds send: from
    `treesFrom F i` on, as many as these rounds send; the empty list where there is no entry i.
  `namesDoorAt F i`: of the entry i: every tree that the entry four in front of it sends, and every
    tree that the entry right in front of it sends, is named in its field `before`, as a tree of
    chain 1; and each of these two entries sends a tree. No where i < 4 or there is no entry i.
  `namesDoorB F`: THE TEST: `namesDoorAt` at every index of `drawIxs F`.
  `drawRounds ds`: the numbers of the declared rounds that draw entries of a matrix.
  `drawsDoorB F`: THE TEST: the first chain's declared rounds that draw entries of a matrix are
    just the first rounds of the entries of the kind K8, in order. It asks what
    `drawsB F (drawIxs F)` asks, in one walk over the declared rounds: `drawsB` looks each round up
    by its number in a list.
  `noDrawElseB F` is Johnson/Desc/First/K8/PlanNames.lean's, as it lies.
What a yes gives is Johnson/Desc/First/K8/LawPlanDoor.lean's.
WHAT THESE TESTS LEAN ON. They read `F.roundsDeclaredByBlocks`: THE DESCRIPTION'S OWN BLOCKS' ROUNDS in a row
(Johnson/Desc/Block.lean: `FileDescription.roundsDeclaredByBlocks`), not the field `F.plans`. That the two are one is a
clause of the description's own test on the plan: `F.roundsDeclaredByBlocks.1 == F.plans.1`, and the like for the
other two chains (`FileDescription.planOkCore`, beneath `FileDescription.planOk`). Where the proof file's value is
laid (Johnson/Desc/Laid/ProofFull.lean: `proofDataAndDecisionOfDescription`) a refusal "where its tests on the plan say no"
(`F.planWord`) stands in front of the list of tests that the laws ask. WITHOUT THAT CLAUSE THESE
THREE CAN PASS IDLY: a description with no entry of the kind K8 and no round that draws entries of a
matrix passes all three.
Limits. THE DISTANCES 4 AND 1 ARE WRITTEN NUMBERS: in the proof file's description the link's first
sending stands four entries, and the sending of the reads one entry, in front of the draw, at all
three sorts of link: seen in a print over the public files of two stored sets; that the entries
there ARE these sendings no test here asks: it asks only that they send a tree. The test says that
the sent trees are AMONG the named ones; that no other tree is named it does not say.

-/
import Johnson.Desc.First.K8.PlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- The indices of the entries of the kind K8 in the first chain's flat list. -/
def drawIxs {Xi : Type} (F : FileDescription Xi) : List Nat :=
  (F.first.blocksInOrder.zipIdx.filter fun x => x.1.place.kind == KindName.K8).map (·.2)

/-- The trees that entry i's own declared rounds send. -/
def sentBy {Xi : Type} (F : FileDescription Xi) (i : Nat) : List Nat :=
  match F.first.blocksInOrder[i]? with
  | some b => List.range' (treesFrom F i) (rootsOfRounds b.rounds)
  | none => []

/-- The test at one entry. -/
def namesDoorAt {Xi : Type} (F : FileDescription Xi) (i : Nat) : Bool :=
  match F.first.blocksInOrder[i]? with
  | some b =>
    decide (4 ≤ i) && !(sentBy F (i - 4)).isEmpty && !(sentBy F (i - 1)).isEmpty &&
      (sentBy F (i - 4) ++ sentBy F (i - 1)).all fun j => b.before.contains (1, j)
  | none => false

/-- **The test on the names.** -/
def namesDoorB {Xi : Type} (F : FileDescription Xi) : Bool := (drawIxs F).all (namesDoorAt F)

/-- The numbers of the declared rounds that draw entries of a matrix. One walk over the list. -/
def drawRounds (ds : List Fmt.DeclaredRound) : List Nat :=
  (ds.zipIdx.filter fun x => x.1.entry.trits != 0).map (·.2)

/-- **The test on the draws.** -/
def drawsDoorB {Xi : Type} (F : FileDescription Xi) : Bool :=
  drawRounds F.roundsDeclaredByBlocks.1 == (drawIxs F).map fun i => roundsOfBlocks (F.first.blocksInOrder.take i)

end VerifiableInference.Desc.First.K8
