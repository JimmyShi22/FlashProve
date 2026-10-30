-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/Written.lean: written values of a key file's description at the full size: its
declared rounds, and the numbers of its four proximity tests' places. Definitions alone. One home
for the values at which the theorems that prove the premises r8 (the blocks' rounds against the
written list) and r4 (the tests on the plan) of `IM.keyBack_of_rows`
(Johnson/IMR/KeyBackOfRows.lean) state their own premises (`Pins`: Row.lean in this folder;
KB4/Pins.lean).

The declared rounds. `writtenOf` (Johnson/G/RoundsOfPlan.lean) lays a declared round r as
(r.round e, r.stored). At a tree that is taken over it sets two stand-ins: `tagRoot p`, which has
p + 1 bytes, for the root number p, and `tagRun (c + 1)`, one byte, for the run's value of chain c.
So a written round names its declared round, and the declared rounds want no literal of their own:
they are the written dry lists (`dryKeyFull`, Johnson/G/DryKeyLit.lean) turned back.

Main names.
  `backSrc`, `backR`: a tree's source, and a written round, turned back.
  `unrunD recs runs`: the list of declared rounds of a list of runs (as `unrunR`).
  `declRecsFull`: the distinct declared rounds. `declKeyFull`: the three lists.
  `rangesNumsFull`, `laterPlacesFull`: the places' numbers, whole.
  `rNums`, `uNums`, `oNums`, `wNums`: of each place the numbers that its test's rounds are made of.

Whence the places' numbers. Every field but start, first, free and firstTree is the maker's own
expression (`Key.rangesNumbers`, Johnson/Desc/Key/Ranges.lean; `Key.laterPlaces`,
Johnson/Desc/Key/Places.lean) at the typed sizes of a key of full size (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean) and the typed setting (`recordSet`); with one
difference: the own test's first group is counted by the maker off the ranges' stages as read back
from the parameter bytes, here off the typed sizes'. The four other fields were typed by hand, read
off the written dry lists. start: where the test's "BAT" stands. free: the roots that the chain's
rounds in front of it send. first: the trees that the test's first "CS" opens; at Omega's test
less the last of them, the first fold's own mask, which `H2U.roundsOfNums` lays itself. firstTree:
0 on the first two chains, the maker's own literal; 7 on the third: the first chain's six trees
and 1.

A near twin. Johnson/Desc/K12/Law/PlacesKeyFull.lean (`H2K.Member.piKUFull`, `piKOFull`, `piKWFull`;
not imported here) has the three later places as `P12`, made by a program off a print of Lean's
evaluator. That their `nums` are these is held by the kernel in TieK12.lean in this folder; no other
field is tied.

Limits. No theorem is here. That `writtenOf` lays `declKeyFull` as `dryKeyFull`, and that a key
file's description declares these rounds, is said in other files of this folder. That the places'
numbers are what `Key.rangesNumbers` and `Key.laterPlaces` return at any public files is not said
here: a theorem that says it can stand only in a file that imports this one. Two such theorems,
`rangesNumbers_in_scope` and `laterPlaces_in_scope` (both in the namespace `Johnson.AtFull.KeyBack`;
Johnson/AtFull/KeyBack/InScope.lean), say it of `Key.rangesNumbers m` and `Key.laterPlaces m`, under
three premises: the public files are in scope of the goals (`VerifierAndGoals.InScope`), `publicOfO` returns
on them, and m is what `Key.madeAt` then returns at the constant digest `Key.fixedDigest`. The three
premises are met at the library's written copy of the full-size public files (`VerifierAndGoals.storedPublicFiles`: three
terms written in Lean; no theorem ties them to the repository's
files): the first by `VerifierAndGoals.inScope_full` (Johnson/Goal/Files/ScopeExample.lean), the other two by
`AtFullSide.Planner.theKeyLaid_zFull_returns` (AtFullSide/Planner/KeyLaidReturns.lean), at the
format's second hash function (`OnBytes.secondHashFunction`) and the same constant digest, not the files' own,
in a side library outside the main library (one constant beneath it passes Lean's kernel only at a
larger thread stack; Lean's re-checker, leanchecker, was run on it and fails there at each shell
stack limit that was tried; the toolchain's own replay passes it at a larger thread stack; so that
constant has been checked by the kernel in the build and by that replay, and by no independent
program); no independent checker has replayed any of the closed facts beneath it, and the
full-size example's weights are synthetic. These last two theorems speak of `VerifierAndGoals.storedPublicFiles` alone,
not of other files in scope.
`backSrc` is meant for the stand-ins alone: of other bytes it makes a source that
means nothing. The limits of DryKeyLit.lean hold here. Nothing on soundness.

-/
import Johnson.G.DryKeyLit
import Johnson.Desc.Key.Desc
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open Johnson.G Johnson.G.OfPlan
open VerifiableInference.Desc.Key (LaterPlaces)
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

/-! ## The declared rounds -/

/-- A tree's source turned back: the stand-ins' lengths and byte name the chain and the root. -/
def backSrc : Fmt.Src → Fmt.TreeSource
  | .own n => .own n
  | .given r s => .taken ((s.data.getD 0 0).toNat - 1) (r.size - 1)

/-- A written round, with the stored tables that it opens, turned back into a declared round. -/
def backR (x : Fmt.Round × List Fmt.Stored) : Fmt.DeclaredRound :=
  ⟨x.1.entry, x.2, x.1.opens.map fun o => (o.1, backSrc o.2)⟩

/-- The list of declared rounds of a list of runs: how often, which distinct round. -/
def unrunD (recs : List Fmt.DeclaredRound) (runs : List (Nat × Nat)) : List Fmt.DeclaredRound :=
  runs.flatMap fun x => (recs[x.2]?).elim [] (List.replicate x.1)

/-- The distinct declared rounds of the key file at the full-size example. -/
def declRecsFull : List Fmt.DeclaredRound := dryKeyRecsFull.map backR

/-- **The key file's three lists of declared rounds at the full-size example.** -/
def declKeyFull : Decl3 :=
  (unrunD declRecsFull dryKeyRunsFull0, unrunD declRecsFull dryKeyRunsFull1,
    unrunD declRecsFull dryKeyRunsFull2)

/-! ## The four places -/

/-- The numbers of the ranges' test's place. -/
def rangesNumsFull : H2U.PlaceNums :=
  { chain := 1, start := 18805
    nums :=
      { rows := Wf.rowsBatched keyFull.ranges.x keyFull.ranges.matrix
        work := recordSet.workOf .query .once
        stages := keyFull.ranges.test.stages.map H2U.stageNums
        ownMask := !keyFull.ranges.x.choice.masksRide
        first := [(⟨22, 77, false, 1⟩, .own 1)], free := 2, firstTree := 0 }
    idx := keyFull.ranges.x.stages.map fun s => (s.code, s.maskCode), firstGroup := 1
    answers := recordSet.samples, early := keyFull.ranges.x.choice.masksRide }

/-- The scope of the shared chain's two tests. -/
def scopeShared : Scope := if keyFull.once.lines.oneTime then .once else .shared

/-- The numbers of the three later places. -/
def laterPlacesFull : LaterPlaces :=
  let S := keyFull.once.shape
  let a := recordSet.samples
  { U :=
      { chain := 2, start := 8
        nums :=
          { rows := S.fold.index.answers + S.fold.columns + 1 + 2 * a
            work := recordSet.workOf .query scopeShared
            stages := keyFull.once.folded.stages.map H2U.stageNums, ownMask := !S.masksAhead
            first := [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)]
            free := 3, firstTree := 0 }
        idx := S.testU.map fun s => (s.code, s.maskCode), firstGroup := 2, answers := a
        early := S.choice.masksRide }
    O := some
      { chain := 2, start := 43
        nums :=
          { rows := 1 + 2 * a, work := recordSet.workOf .query scopeShared
            stages := keyFull.once.omega.stages.map H2U.stageNums, ownMask := true
            first := [(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)]
            free := 7, firstTree := 0 }
        idx := S.testOmega.map fun s => (s.code, s.maskCode)
        firstGroup := 2 + (S.testU.length - 1), answers := a, early := S.choice.masksRide }
    W :=
      { chain := 3, start := 0
        nums :=
          { rows := 2 + 3 * a
            work := recordSet.workOf .query
              (if keyFull.once.lines.oneTime then .once else .request)
            stages := keyFull.once.own.stages.map H2U.stageNums, ownMask := !S.masksAhead
            first := [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 12, false, 5⟩, .taken 0 5),
              (⟨22, 36, false, 1⟩, .taken 1 1)]
            free := 0, firstTree := 7 }
        idx := S.testOwn.map fun s => (s.code, s.maskCode)
        firstGroup := keyFull.ranges.x.stages.length + 1, answers := a
        early := S.choice.masksRide } }

/-- What the rounds of the test on the ranges' group are made of. -/
def rNums : H2U.TestNums := rangesNumsFull.nums

/-- The like for the test on the folded row's group. -/
def uNums : H2U.TestNums := laterPlacesFull.U.nums

/-- The like for the test on Omega's group. `laterPlacesFull.O` is `some`: the value behind `getD`
is there for the type alone and is never reached. -/
def oNums : H2U.TestNums := (laterPlacesFull.O.map (·.nums)).getD rNums

/-- The like for the test on the own group. -/
def wNums : H2U.TestNums := laterPlacesFull.W.nums

end Johnson.KB8
