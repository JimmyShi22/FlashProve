-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PlanNames.lean: THE SMALLNESS TEST: "THE PLACE NAMES JUST THE TREES OF THE
LINK'S TWO SENDINGS": A PUBLIC TEST WITH CODE. DEFINITIONS. NO THEOREM HERE. NO SOUNDNESS IS
CLAIMED.

  `rootsOfRounds ds`: the number of trees that a list of declared rounds sends.
  `roundsOfBlocks l`: the number of declared rounds of a list of blocks.
  `treesFrom F i`: the number of trees that the first chain's declared rounds of the entries in
    front of entry i of the flat list send.
  `namesB F p iM iR`: THE TEST: the place's list for the matrices is just the numbers of the trees
    that entry iM's own declared rounds send, in order: from `treesFrom F iM` on, as many as these
    rounds send; and the like for its list for the reads at entry iR.
  `drawsB F ixs`: A TEST: ARE THESE ALL THE DRAWS? the numbers of the first chain's declared rounds
    that draw entries of a matrix are just, in order, the numbers of the rounds that stand right
    behind the rounds of the entries in front of the entries ixs.
  `noDrawElseB F`: A TEST: no declared round of the file's two other chains draws such entries.
What a yes gives is Johnson/Desc/First/K8/LawPlanNames.lean's.

-/
import Johnson.Desc.First.K8.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- The number of trees that a list of declared rounds sends. -/
def rootsOfRounds (ds : List Fmt.DeclaredRound) : Nat := (ds.map (·.entry.roots)).sum

/-- The number of declared rounds of a list of blocks. -/
def roundsOfBlocks {S Cl : Type} (l : List (Block S Cl)) : Nat :=
  (l.map fun b => b.rounds.length).sum

/-- The trees that the rounds of the entries in front of entry i send. -/
def treesFrom {Xi : Type} (F : FileDescription Xi) (i : Nat) : Nat :=
  rootsOfRounds (F.roundsDeclaredByBlocks.1.take (roundsOfBlocks (F.first.blocksInOrder.take i)))

/-- **The test.** -/
def namesB {Xi : Type} (F : FileDescription Xi) (p : Par) (iM iR : Nat) : Bool :=
  match F.first.blocksInOrder[iM]?, F.first.blocksInOrder[iR]? with
  | some bM, some bR =>
    p.matsIn == List.range' (treesFrom F iM) (rootsOfRounds bM.rounds) &&
      p.readsIn == List.range' (treesFrom F iR) (rootsOfRounds bR.rounds)
  | _, _ => false

/-- **Are these all the draws?** The first chain's declared rounds that draw entries of a matrix are
as many as the list of entries is long, and each stands right behind the rounds of the entries in
front of one of them. -/
def drawsB {Xi : Type} (F : FileDescription Xi) (ixs : List Nat) : Bool :=
  (((List.range F.roundsDeclaredByBlocks.1.length).filter fun j =>
      ((F.roundsDeclaredByBlocks.1[j]?).map fun d => d.entry.trits != 0).getD false) ==
    ixs.map fun i => roundsOfBlocks (F.first.blocksInOrder.take i))

/-- No declared round of the file's two other chains draws entries of a matrix. -/
def noDrawElseB {Xi : Type} (F : FileDescription Xi) : Bool :=
  (F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2).all fun d => d.entry.trits == 0

end VerifiableInference.Desc.First.K8
