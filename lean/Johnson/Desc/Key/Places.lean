-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Places.lean: the numbers of the places of the three proximity tests of a key file's
shared and third chain, off the plan. Definitions with code; public data only. No theorem.

A proximity test's block is made of its place's numbers (`H2U.PlaceNums`,
Johnson/Desc/K12/Plan/PlaceOfPlan.lean): where in the chain's plan its rounds begin, its stages,
which trees it opens first, how many rows it batches. That file makes them for a proof file. Here
the same rules are read at the key file's records: no rule is new. Line for line it is that file's
text, with the sized proof's set, codes and batch replaced by the sized key's set, codes and
one-time values; the proof's plans and sendings by the key's; the three chains of the proof by the
key's one-time, shared and second chain; and, among the first chain's trees, what rides at the start
by the index-mask message (as `declKOf` has it, Johnson/G/RoundsOfPlan.lean).

Main names.
  `TestFirsts`, `testFirsts`: for each of the three places the trees that its first opening reads,
  and the number of its first tree.
  `keyTestCut`, `keyBatchRounds`: a test's rounds, cut out of the plan of one of the key's chains;
  the plan's batching rounds.
  `LaterPlaces`, `laterPlaces`: the three places' numbers: U, the test on the folded row's group; O,
  the test on Omega's group, where the shape splits; W, the test on the own group.

Limits. The first chain's own test (on the ranges' group) is not here. `firstGroup` feeds the
tenants' groups alone: 2 at U; at O 2 and the number of code switches of the test at U; at W it is
reckoned, not run: the ranges' group, the groups of its test's switches, and the own group: the
number of the ranges' stages and 1. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K12.Plan.PlaceOfPlan

set_option autoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params Johnson.G.OfPlan H2U

/-- What the three places' first openings read, each with the number of its first tree. -/
structure TestFirsts where
  U : FirstAt
  O : Option FirstAt
  W : FirstAt

/-- These, of the planner's answer and the sendings. -/
def testFirsts (m : Made) : Except String TestFirsts := do
  let S := m.p.chains.made.sized.key.once.shape
  let P0 := m.p.chains.key.oneTime.given.plan
  let P1 := m.p.chains.key.shared.given.plan
  let P2 := m.p.chains.key.second.given.plan
  let t0 ← treesSent "key file, first chain" m.key.1 P0 []
  let t1 ← treesSent "key file, shared chain" m.key.2.1 P1 (ownMasks m.key.2.1.codes S P1.rounds)
  let t2 ← treesSent "key file, second chain" m.key.2.2 P2 []
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some a => pure a
    | none => throw ("testFirsts: the rule has no list for " ++ what)
  let sh := sharedOpens S t1
  let u ← get "the folded row's test" (sh[1]?)
  let o := if S.sharedSplitNeeded then (sh[2 + (switchOpens 0 .folded t1).length]?).map fun x =>
      (x.1.dropLast, 0) else none
  let w ← get "the own test" (secondOpens S (fun t => t.tag == .indexMask) t0 t1 t2).head?
  pure { U := (u.1, 0), O := o, W := (w, t0.length + 1) }

/-- The cut at the place i of the key file's chain number ch (from 0). -/
def keyTestCut (C : Configured) (ch i : Nat) (st : List IoppStage) : Option TestCut := do
  let P ← C.key[ch]?
  let es := P.rounds.map (·.entry)
  let cut := (es.drop i).take (1 + towerLen st)
  if st.length < 2 || cut.map (·.name) != "BAT" :: towerNames st then none
  pure ⟨ch, i, cut, ((es.take i).map (·.roots)).foldl (· + ·) 0, st⟩

/-- The numbers of the batching rounds in the plan of the key file's chain number ch (from 0). -/
def keyBatchRounds (C : Configured) (ch : Nat) : Option (List Nat) :=
  (C.key[ch]?).map fun P => batPlaces (P.rounds.map (·.entry))

/-- The numbers of the three places. O: nothing where the shape does not split. -/
structure LaterPlaces where
  U : PlaceNums
  O : Option PlaceNums
  W : PlaceNums

/-- **The three places.** -/
def laterPlaces (m : Made) : Except String LaterPlaces := do
  let Fs ← testFirsts m
  let C := m.p.chains.made
  let z := C.sized.key
  let a := C.sized.set.samples
  let S := z.once.shape
  let once := z.once.lines.oneTime
  let w := fun (c : Scope) => C.sized.set.workOf .query c
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some v => pure v
    | none => throw ("laterPlaces: no cut at " ++ what)
  let mk (chain : Nat) (st : List StageSize) (rows : Nat) (work : Nat) (own : Bool) (t : TestCut)
      (fa : FirstAt)
      (g0 : Nat) (early : Bool) : PlaceNums :=
    { chain := chain, start := t.start
      nums := { rows := rows, work := work, stages := st.map stageNums, ownMask := own,
                first := fa.1, free := t.roots, firstTree := fa.2 }
      idx := t.stages.map fun s => (s.code, s.maskCode), firstGroup := g0, answers := a, early :=
          early }
  let tU ← get "the folded row's test" (do keyTestCut C 1 (← (← keyBatchRounds C 1)[0]?) S.testU)
  let tW ← get "the own test" (do keyTestCut C 2 (← (← keyBatchRounds C 2)[0]?) S.testOwn)
  let tO : Option TestCut := do keyTestCut C 1 (← (← keyBatchRounds C 1)[1]?) S.testOmega
  let rB := S.choice.masksRide
  pure
    { U := mk 2 z.once.folded.stages (S.fold.index.answers + S.fold.columns + 1 + 2 * a) (w
        (if once then .once else .shared)) (!S.masksAhead) tU Fs.U 2 rB
      O := match tO, Fs.O with
        | some tO, some fO => some (mk 2 z.once.omega.stages (1 + 2 * a) (w
            (if once then .once else .shared)) true tO fO (2 + (tU.stages.length - 1)) rB)
        | _, _ => none
      W := mk 3 z.once.own.stages (2 + 3 * a) (w (if once then .once else .request))
          (!S.masksAhead) tW Fs.W
        (m.p.chains.key.oneTime.ranges.stages.length + 1) rB }

end VerifiableInference.Desc.Key
