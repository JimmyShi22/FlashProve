-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/FixedBefore.lean: a test on the plan alone, for the proximity test's block: every
tree that a stage of the test opens was sent in front of the first draw of the stage that spends it.
Definitions only, all computable; nothing is proved here.

Why. A word without an out-of-domain sample is read beyond half its code's distance in the code
switches and the base case. The library's proved blocks take as a premise that such a word is fixed
before the block. This test is the kind's share of that premise. Block.lean's `beforeAt` holds that
what `before` names was sent in time. Nothing there holds that `before` names all that the block
opens, nor anything on the trees that the test sends itself. This test does.

  `sentIn N rds i`  the chain's own trees sent in front of the test's round number i: those in front
                    of the test, and one for each root of the rounds before i.
  `fixedAt`         of a tree that is opened. An own tree sent in front of the test, or a tree taken
                    from another chain: it stands in `before`. An own tree that the test sends: its
                    number is below `sentIn` at the round handed in.
  `sliceOk`         every tree that the rounds of a slice open is fixed in front of the round `fix`.
  `fixedFrom`       the stages, cut as Frame.lean's `stagesFrom` cuts them: a fold's 1 + k rounds, a
                    switch's 2, the base case's 2. What a stage's switch opens must be fixed in
                    front of that stage's fold's first draw, not only of the switch's first round:
                    the mask that a switch opens is the fold's mask, and the library's block is the
                    fold and the switch together. A round's own message stands in front of its draw:
                    so `fix` is the fold's first round + 1 (a fold that sends its own mask sends it
                    there).
  `fixedOk p`       the whole test: the batching's round, then the stages.

Limits. It reads `free` (the count of the chain's trees in front of the test) and the declared
rounds off one and the same `p`: a wrong `free` moves both alike and is not seen here; the
description's test of the blocks' declared rounds against the plan's sees it. That what `before`
names was sent in time is `beforeAt`'s. Which of a tree's tenants is sampled is not looked at: the
test covers every opened tree. Nothing on the error; nothing on soundness. The namespace is
H2K.FixedBefore, under which the files that stand on this one name it.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Frame

set_option autoImplicit false
namespace H2K.FixedBefore
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The chain's own trees that have been sent in front of the test's round number i. -/
def sentIn (N : H2U.TestNums) (rds : List Fmt.DeclaredRound) (i : Nat) : Nat :=
  N.free + ((rds.take i).map (·.entry.roots)).sum

/-- start: the round in front of which the tree must have been sent. chain: 1, 2 or 3. -/
def fixedAt (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (start : Nat) (o : Fmt.Shape × Fmt.TreeSource) : Bool :=
  match o.2 with
  | .own n => if n < N.free then before.contains (chain, n) else decide (n < sentIn N rds start)
  | .taken c n => before.contains (c + 1, n)

/-- The len rounds from number start on: what they open is fixed in front of the round number fix.
-/
def sliceOk (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (start len fix : Nat) : Bool :=
  ((rds.drop start).take len).all fun r => r.opens.all (fixedAt chain before N rds fix)

/-- The stages from the round number i on, cut as stagesFrom cuts them. -/
def fixedFrom (chain : Nat) (before : List (Nat × Nat)) (N : H2U.TestNums)
    (rds : List Fmt.DeclaredRound) : Nat → Fmt.M1.Stage → List Fmt.M1.Stage → Bool
  | i, _, [] => sliceOk chain before N rds i 2 i
  | i, cur, next :: rest =>
    sliceOk chain before N rds i (1 + cur.k) i &&
      sliceOk chain before N rds (i + 1 + cur.k) 2 (i + 1) &&
      fixedFrom chain before N rds (i + cur.k + 3) next rest

/-- **Every tree that a stage of the test opens was sent in front of the first draw of the stage
that spends it.** -/
def fixedOk (p : P12) : Bool :=
  match p.nums.stages, H2U.roundsOfNums p.nums with
  | first :: rest, some rds =>
    sliceOk p.place.chain p.before p.nums rds 0 1 0 &&
      fixedFrom p.place.chain p.before p.nums rds 1 first rest
  | _, _ => false

end H2K.FixedBefore
