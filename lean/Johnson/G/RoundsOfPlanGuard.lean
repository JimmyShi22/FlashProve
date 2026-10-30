-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/RoundsOfPlanGuard.lean: the rounds that Johnson/G/RoundsOfPlan.lean computes from the
three public files, held against the written dry lists, by evaluation at the small example.

Tests of a part of D: definitions alone; nothing proved of it; D as a whole has not run on a real
file. (D: the head of Johnson/G/RoundsOfPlan.lean.)

Definitions and three `#guard`s.
  `sameEach x y`: for two pairs of three lists of written rounds: list by list, are they the same?
  `smallFiles`: the small example's three public files.
  `atAll f x`, `lessTrees x`, `lessTables x`: x with f at every round of all six chains; with the
    last tree struck from every list of opened trees; with every stored table struck.
  `writtenBoth x`: both files' declared rounds as written rounds.
  `Tests`, `testsAt`: the tests below, at three public files, two triples of lists and a depth.
  `relabel`, `lessSends`, `refusedFor`, `refusalsAt`: for the tests that a refusal comes.
  `sameDecl`, `declaredRounds`: for the comparison with a declared structure. No test of this file
    calls them: see "Outside the build".
The tests, at the small example.
  `testsAt`: the rounds of `declKOf` and `declPOf`, written out, are `dryKeySmall` and
    `dryProofSmall`: six lists, each the same, round for round and field for field. With `lessTrees`
    between, none of the six is the same. With `lessTables` between, the two shared chains' lists
    are not the same and the four others are. The stored table's depth is 23. The makers' tests
    `okAt` pass at both files' lists. `dataKAt` and `dataPAt` return data whose first chains have
    3,677 and 8,036 rounds: the lists' without the sealing round.
  `roundsOf` returns these six lists too. (`dataKOf` and `dataPOf` are `dataKAt` and `dataPAt` of
    `madeOf`, as `roundsOf` is `roundsAt` of it; the build evaluates this one of the three.)
  `refusalsAt`: with the sendings of the key's first chain changed in one place, `declKOf` refuses,
    each time for the reason meant: a label that is not known; a sending left out (a root without a
    tree); the multiplicities under another label (a round would open nothing); W under a label by
    which the second chain's rule does not look for it (a tree opened nowhere); a code switch under
    another test's label (too few lists). No such test is made on the five other chains.
Source of the values: Lean's evaluator, at the library's own copies of the three shipped public
files of prover/examples/target_small_f2_roomy (OnBytes/Model/TestRecordWork.lean,
OnBytes/Params/SmallFiles.lean). No other file is read.

Outside the build. These evaluations were made once, by Lean's evaluator, at the code of this file
and of Johnson/G/RoundsOfPlan.lean as it stands. No build runs them, and the tree holds no file from
which they can be repeated.
  At the full-size example (Johnson/G/KitFull.lean): `testsAt` and `roundsOf` as above, against
    `dryKeyFull` and `dryProofFull`; the depth is 32.
  At the small example: `declOf` is `declaredRounds` of `Params.declared`
    (OnBytes/Params/DeclaredOf.lean) at the same files: six lists, in the
    declared structure's own type, where a tree that is taken over is named and has no stand-in.
  At eleven further parameter files, with the small example's layout and scale files: `roundsOf` is
    what the dry runs `dryKey` and `dryProof` (OnBytes/Maker/Files.lean) give there, in all six
    lists. The eleven: a stage fewer in the ranges' test; a stage more in the folded row's test, in
    Omega's, in the own test; a stage fewer, and a stage more, in the last test; 1 slot; 16 slots;
    no proof of work before the positions; one file with no record, no proof of work at all, and
    other codes and another rule for the one-time groups; the proof's shared chain without a split.
    What never varied: the links (five, of the same kinds, in the same order); the model's sizes;
    the key file's shared chain, which always had a split.

Limits: evidence by evaluation; no theorem. Which trees a test's first round of positions opens was
read off the written lists that the functions are held against here: the head of
Johnson/G/RoundsOfPlan.lean says what that shows. The written lists, `Params.declared` and the dry
runs all take their openings from the verifier program's blocks; the proof file's at one made-up
request each. So these three comparisons have one source.
The first two `#guard`s would pass as well if the functions copied the written lists. That they do
not is seen from the text of Johnson/G/RoundsOfPlan.lean and from its imports, below which the two
files of written lists do not lie. `lessTrees` and `lessTables` show that the comparison sees the
opened trees and the stored tables; they do not show that one wrong tree would be seen. No control
turns an entry, a kind or an item: there the comparison is the derived equality of `Fmt.Round`,
which takes every field.

-/
import Johnson.G.RoundsOfPlan
import Johnson.G.DryProofLit
import Johnson.G.DryKeyLit
import OnBytes.Model.TestRecordWork

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G.OfPlan

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Maker
open OnBytes.Params (Rounds)

/-- Two files' written rounds: the key file's three lists, the proof file's three. -/
abbrev Six : Type := (Rounds × Rounds × Rounds) × (Rounds × Rounds × Rounds)

/-- List by list: are they the same? -/
def sameEach (x y : Six) : List Bool :=
  [decide (x.1.1 = y.1.1), decide (x.1.2.1 = y.1.2.1), decide (x.1.2.2 = y.1.2.2),
    decide (x.2.1 = y.2.1), decide (x.2.2.1 = y.2.2.1), decide (x.2.2.2 = y.2.2.2)]

/-- Two pairs of three lists of declared rounds are the same. -/
def sameDecl (x y : Decl3 × Decl3) : Bool :=
  decide (x.1.1 = y.1.1) && decide (x.1.2.1 = y.1.2.1) && decide (x.1.2.2 = y.1.2.2) &&
    decide (x.2.1 = y.2.1) && decide (x.2.2.1 = y.2.2.1) && decide (x.2.2.2 = y.2.2.2)

/-- The rounds of a declared structure's key file's and proof file's chains. -/
def declaredRounds (D : Fmt.Declared) : Decl3 × Decl3 :=
  ((D.key.first.rounds, D.key.shared.rounds, D.key.second.rounds),
    (D.proof.first.rounds, D.proof.shared.rounds, D.proof.second.rounds))

/-- The small example's three public files: policy, layout, scales. -/
def smallFiles : ByteArray × ByteArray × ByteArray :=
  (TestRecordWork.policyOf TestRecordWork.smallHead, Params.SmallFiles.layout,
    Params.SmallFiles.scales)

/-- A function on declared rounds, at every round of all six chains. -/
def atAll (f : Fmt.DeclaredRound → Fmt.DeclaredRound) (x : Decl3 × Decl3) : Decl3 × Decl3 :=
  ((x.1.1.map f, x.1.2.1.map f, x.1.2.2.map f), (x.2.1.map f, x.2.2.1.map f, x.2.2.2.map f))

/-- With the last tree struck from every list of opened trees. -/
def lessTrees : Decl3 × Decl3 → Decl3 × Decl3 := atAll fun r => { r with opens := r.opens.dropLast }

/-- With every stored table struck. -/
def lessTables : Decl3 × Decl3 → Decl3 × Decl3 := atAll fun r => { r with stored := [] }

/-- Both files' declared rounds as written rounds. -/
def writtenBoth (x : Decl3 × Decl3) : Option Six := do
  pure (← (writtenOf "key file" x.1).toOption, ← (writtenOf "proof file" x.2).toOption)

/-- What `testsAt` returns. -/
structure Tests where
  /-- list by list: the computed rounds are the written ones -/
  same : List Bool
  /-- the same question with `lessTrees` between -/
  lessTrees : List Bool
  /-- the same question with `lessTables` between -/
  lessTables : List Bool
  /-- the stored table's depth is the one given -/
  depth : Bool
  /-- the makers' tests pass at both files' lists -/
  ok : Bool
  /-- the numbers of rounds of the first chains in `dataKAt` and `dataPAt` -/
  first : Option Nat × Option Nat
  deriving DecidableEq, Repr

/-- The tests at three public files, two triples of written lists and a depth. Nothing if a function
refuses. -/
def testsAt (f : ByteArray × ByteArray × ByteArray) (K P : Rounds × Rounds × Rounds) (a : Nat) :
    Option Tests := do
  let m ← (madeOf f.1 f.2.1 f.2.2).toOption
  let x := (← (declKOf m).toOption, ← (declPOf m).toOption)
  let y ← writtenBoth x
  pure ⟨sameEach y (K, P), sameEach (← writtenBoth (lessTrees x)) (K, P),
    sameEach (← writtenBoth (lessTables x)) (K, P), (depthOf m).toOption == some a,
    okAt a (some y.1) && okAt a (some y.2),
    ((dataKAt m).toOption.map (·.ds₁.length), (dataPAt m).toOption.map (·.ds₁.length))⟩

/-- A chain's sendings with one label changed. -/
def relabel (old new : String) (c : ChainSends) : ChainSends :=
  { c with sends := c.sends.map fun x => if x.label == old then { x with label := new } else x }

/-- A chain's sendings without the last. -/
def lessSends (c : ChainSends) : ChainSends := { c with sends := c.sends.dropLast }

/-- The function has refused, and its words hold w. -/
def refusedFor {α : Type} (x : Except String α) (w : String) : Bool :=
  match x with
  | .error e => 1 < (e.splitOn w).length
  | .ok _ => false

/-- With the key's first chain's sendings changed in one place, `declKOf` refuses for the reason
meant. Five changes. -/
def refusalsAt (f : ByteArray × ByteArray × ByteArray) : Option (List Bool) := do
  let m ← (madeOf f.1 f.2.1 f.2.2).toOption
  let at_ (g : ChainSends → ChainSends) (w : String) : Bool :=
    refusedFor (declKOf { m with key := (g m.key.1, m.key.2) }) w
  pure [at_ (relabel "W" "V") "does not know", at_ lessSends "tree(s) were found",
    at_ (relabel "the multiplicities" "W") "would open nothing",
    at_ (relabel "W" "Omega") "opened nowhere",
    at_ (relabel "the ranges' test, the code switch of stage 1"
      "the own test, the code switch of stage 1") "lists of trees were found"]

#guard testsAt smallFiles dryKeySmall dryProofSmall 23 ==
  some ⟨List.replicate 6 true, List.replicate 6 false, [true, false, true, true, false, true], true,
    true, (some 3677, some 8036)⟩

#guard ((roundsOf smallFiles.1 smallFiles.2.1 smallFiles.2.2).toOption.map fun y =>
  sameEach y (dryKeySmall, dryProofSmall)) == some (List.replicate 6 true)

#guard refusalsAt smallFiles == some (List.replicate 5 true)

end Johnson.G.OfPlan
