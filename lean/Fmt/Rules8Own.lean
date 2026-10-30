-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8Own.lean: the writer's side of a proof file: a driver that strings an honest prover's
steps along the chain and writes the file.

For tests and example provers. No verifier calls anything here. Fmt/Rules8.lean reads a proof file
(a chain of rounds). Here the same description of a chain (`Spec`) drives the other side. A
protocol's prover is given without any hash, as a function of the verifier's messages so far.
The chain is the hash chain from which each round's verifier message (the challenges) is drawn.

Sources. The format page (docs/format/FORMAT.md); this file has not been held against the page as
it ships, and may differ from it, for instance at R8.7 of the rules cited below. No Mathlib.




1. What the file contains.
   `OwnTree`: a tree's content: the column and the salt at each position.
   `Strat`: the prover: from what was drawn in the rounds before (oldest first) to the next
     message's items without its roots, in their order, and the content of the trees whose roots
     this message sends, in the order of their numbers.
   `spellGot`: an item's bytes (R1.3, R1.4, R1.1).
   `layItems`: the message's bytes. The description's cut into items (`Round.items`) is gone
     through.
   `runOwn S rnd bound P`: the driver, round by round (R8.7's order): the trees are built (leaves
     under this chain's run's value, the tree's number and position; vertices from the
     configuration's digest); the message; the least nonce below "bound" that has the round's
     work; the round's query and its draws; the listed positions, if the plan lists them; the
     openings that the description names, each at its list (R7.15 for a shallower tree). Only trees
     of the chain's own are opened (`Src.own`). The random bytes stand in the file (case (a) of
     R4.5) or are given (case (b)).
   It answers "none" if the description is not in order; the prover's items do not fit the cut;
     there is no nonce below the bound; a tree that is sent has no shape (no round opens it); or a
     tree from outside is to be opened.

2. What is checked when the file compiles. Seven tests (#guard). The page's known answer of a
   chain in a file comes out byte for byte, in both fields. So does the honest file of a small
   example of this library's own (Fmt/Toy1.lean: `Toy1.spec`; Fmt/Toy1Files.lean: `Toy1.honest`),
   which another program made (by the head of Fmt/Toy1Files.lean: the format page's reference
   program; not held against the page as it ships). The draws that the driver hands on are the
   known answer's (the test compares the
   positions alone, `Drawn.poss`, and at `Fld.two` alone). The least nonce is found (none below a
   bound that is one too small). Items that do not fit the cut are refused.

3. Theorems. None.

4. What is not claimed. Nothing on hiding: salts and random bytes are given from outside, and an
   example's are patterns.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules8
import Fmt.Toy1

namespace Fmt

/-- a tree's content -/
structure OwnTree where
  col  : Nat → List UInt64
  salt : Nat → ByteArray

/-- A prover without any hash. -/
abbrev Strat : Type := List Drawn → List ItemValue × List OwnTree

def spellGot : ItemValue → ByteArray
  | .f x => u64 x
  | .e x => ext x
  | .word x => u64 x
  | .root d => d
  | .answer x => ext x

/-- the item is of the kind that the cut names -/
def ItemValue.isOf : ItemValue → Item → Bool
  | .f _, .f => true
  | .e _, .e => true
  | .word _, .word => true
  | .answer _, .answer => true
  | _, _ => false

/-- A message's bytes, from the cut, the prover's items and the roots; all items and all roots are
used up. -/
def layItems : List Item → List ItemValue → List ByteArray → Option ByteArray
  | [], [], [] => some ByteArray.empty
  | [], _, _ => none
  | .root :: ts, gs, r :: rs => (layItems ts gs rs).map fun b => r ++ b
  | .root :: _, _, [] => none
  | t :: ts, g :: gs, rs => if g.isOf t then (layItems ts gs rs).map fun b => spellGot g ++ b else none
  | _ :: _, [], _ => none

/-- n low bytes of a number, the lowest first -/
def lowBytes (n x : Nat) : ByteArray := (u64n x).extract 0 n

/-- a tree that was built: its shape, its content, all its values -/
structure Built where
  shape  : Shape
  tree   : OwnTree
  values : List (List ByteArray)

def buildOwn (cfg run : ByteArray) (sh : Shape) (t : OwnTree) : Built :=
  ⟨sh, t,
    build cfg sh.a
      ((List.range (2 ^ sh.a)).map fun x =>
        leaf (leafNo sh.stored) sh.tree sh.a x run (t.col x) (t.salt x))⟩

/-- the trees of one message, built; the n-th tree of the chain takes its shape from the
description -/
def buildAll (S : Spec) (run : ByteArray) : Nat → List OwnTree → Option (List Built)
  | _, [] => some []
  | n, t :: ts =>
    match S.shapeOf n with
    | none => none
    | some sh => (buildAll S run (n + 1) ts).map fun l => buildOwn S.cfg run sh t :: l

/-- the openings behind one draw -/
def openAll (trees : Array Built) (poss : List Nat) : List (Shape × Src) → Option ByteArray
  | [] => some ByteArray.empty
  | (sh, .own n) :: os =>
    match trees[n]? with
    | none => none
    | some t =>
      (openAll trees poss os).map fun b =>
        openingBytes sh.a t.tree.col t.tree.salt t.values (listOf (poss.map (· % 2 ^ sh.a))) ++ b
  | (_, .given _ _) :: _ => none

/-- the driver's state -/
structure OwnSt where
  chain : Chain
  drawn : List Drawn
  trees : Array Built
  file  : ByteArray

/-- One round. -/
def ownStep (S : Spec) (run : ByteArray) (bound : Nat) (P : Strat) (s : OwnSt) (r : Round) :
    Option OwnSt := do
  let (gs, ts) := P s.drawn
  let bs ← buildAll S run s.trees.size ts
  let msg ← layItems r.items gs (bs.map fun b => rootOf b.values)
  let K := blocksFor (wordsAtMost r.entry r.kind)
  let nonce ← if r.entry.work == 0 then some 0
  else leastNonce s.chain.label s.chain.rho (s.chain.round + 1) msg r.kind r.entry.work bound
  let (c, vb) ← s.chain.query msg r.kind r.entry.work nonce K
  let d := drawRound S.plan.field r.entry r.kind (rowOf vb)
  let trees := s.trees ++ bs.toArray
  let ops ← openAll trees d.poss r.opens
  let nb := if r.entry.work == 0 then ByteArray.empty else lowBytes S.plan.nonce nonce
  let lb := if S.plan.posB == 0 || r.entry.poss == 0 then ByteArray.empty
    else cat ((listOf d.poss).map (lowBytes S.plan.posB))
  pure ⟨c, s.drawn ++ [d], trees, s.file ++ msg ++ nb ++ lb ++ ops⟩

def ownFold (S : Spec) (run : ByteArray) (bound : Nat) (P : Strat) :
    List Round → OwnSt → Option OwnSt
  | [], s => some s
  | r :: rs, s => (ownStep S run bound P s r).bind (ownFold S run bound P rs)

/-- The driver: the file, and what was drawn round by round. -/
def runOwn (S : Spec) (rnd : ByteArray) (bound : Nat) (P : Strat) :
    Option (ByteArray × List Drawn) :=
  if !S.ok then none
  else
    let head : Option ByteArray := match S.rand with
      | .inFile => some rnd
      | .given x => if x == rnd then some ByteArray.empty else none
      | .none => none
    head.bind fun hb =>
      (startChain S.label (paramsDigest S.params) S.statement (some rnd)).bind fun hd =>
        hd.run.bind fun run =>
          (ownFold S run bound P S.rounds ⟨⟨S.label, hd.rho0, 0⟩, [], #[], hb⟩).map
            fun s => (s.file, s.drawn)

/-! ## Tests -/

namespace Own8

/-- the prover of the page's known answer: the tree of the section on trees (its columns, its
salts) -/
def pagesProver : Strat := fun ds =>
  match ds.length with
  | 0 => ([], [⟨k7Column, k7SaltAt⟩])
  | 1 => ([.answer (9, 9, 9)], [])
  | _ => ([.e (4, 5, 6)], [])

/-- the prover of the toy of Fmt/Toy1.lean: first the tree of the row `Toy1.col`; then the claim
plus the sum of the symbols at the listed positions -/
def toyProver (c : Ext) : Strat := fun ds =>
  match ds with
  | [] => ([], [⟨Toy1.col, Toy1.saltAtX⟩])
  | d :: _ => ([.e ((Toy1.sumE .two c ((listOf d.poss).map Toy1.col)).getD (0, 0, 0))], [])

end Own8

-- the page's file, byte for byte, in both fields; the draws are the page's (the test compares
-- `poss` alone, at `Fld.two` alone)
open Own8 in
#guard ((runOwn (Known8.spec .two) (pattern 32 5 1) 4096 pagesProver).map (·.1)) = some Known8.file2
open Own8 in
#guard ((runOwn (Known8.spec .one) (pattern 32 5 1) 4096 pagesProver).map (·.1)) = some Known8.file1
open Own8 in
#guard ((runOwn (Known8.spec .two) (pattern 32 5 1) 4096 pagesProver).map fun x => x.2.map (·.poss)) = some [[], [], [1, 5, 6, 5]]
-- the honest file of the toy of Fmt/Toy1.lean, which another program made: byte for byte
open Own8 in
#guard ((runOwn (Toy1.spec Toy1.claim) (pattern 32 5 1) 4096 (toyProver Toy1.claim)).map (·.1)) = some Toy1.honest
-- what the driver writes, the reader reads
open Own8 in
#guard ((runOwn (Toy1.spec (5, 6, 7)) (pattern 32 3 3) 4096 (toyProver (5, 6, 7))).bind fun x => wholeChain (m := Id) formatHash (Toy1.spec (5, 6, 7)) x.1).isSome
-- a bound that is one too small (51, the least nonce itself: only nonces below the bound are
-- tried): nothing; at 52 the file comes
open Own8 in
#guard (runOwn (Known8.spec .two) (pattern 32 5 1) 51 pagesProver).isNone && (runOwn (Known8.spec .two) (pattern 32 5 1) 52 pagesProver).isSome
-- items that do not fit the cut: nothing
#guard (runOwn (Known8.spec .two) (pattern 32 5 1) 4096 fun _ => ([.e (4, 5, 6)], [])).isNone

end Fmt
