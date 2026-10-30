-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Plan/PlaceOfPlan.lean: all the numbers of a proximity test's place, off the plan:
for each of a proof file's four tests, and for the three tests on a key file's two later chains:
what the kind's parameter `P12` and the block's fields want. From `Johnson.G.OfPlan.Made`: what the
planner and `sendsOf` make of the three public files (Johnson/G/RoundsOfPlan.lean, `madeOf`).
Definitions only, all computable; nothing is proved here.

The numbers (`PlaceNums`).
  nums        `TestNums`. The stages: off the planner's sized records (`StageSize`: the two codes'
              logN, ell, r; k; h; t). rows, work, ownMask: by the arguments of the planner's own
              calls of `planIopp`; at the first chain's last test the rows are `rowsAtLast`. first,
              firstTree: by the rule (Plan/NumsOfPlan.lean). free: the roots of the made
              plan's entries in front of the test.
  idx         for each stage the numbers of its two codes in the record's lists of codes.
  chain       1, 2 or 3. start: the number of the test's first round in its chain.
  firstGroup  the number of the first group that the test makes in the running record, counted from
              the plan. The first chain: a group a link and the last test's. The shared chain: the
              folded row's group and Omega's: 2; behind the folded row's test its switches' groups
              more. The last chain starts from the first chain's record: all its groups, then the
              own group. It feeds the tenants' `groups` (TestOracles.lean), which BookPlan.lean
              reads.
  answers     the answers to a sample. early: whether the masks ride.

One text for both files. `placesLater (A : LaterArgs)` gives the three places on a file's two later
chains as a function of the setting, the sized batch record, the three plans, the three sendings,
the two later chains' entries, `input` and the first chain's number of groups. `laterOfProof` and
`laterOfKey` are the two files' arguments. `placesOfMade m` is the first chain's last test, and
`placesLater` at the proof file's arguments.

Why `Made`, and not the plan's entries. t (the positions of a stage) and the bits of work stand in
the planner's sized records and its setting. To take them off the entries would make the
description's test of a block's rounds against the plan idle.

Limits. No number that the description's test compares with an entry comes off an entry. But free
and start (Plan/TestCut.lean; `cutOn`) and the count of the links' "LOC"s (counted here and in
Plan/NumsOfPlan.lean) do come off the made plan: to that extent a place is not independent of the
plan that it is then held against. At the key file `groupsFirst` is the caller's to say. The
namespace is H2U, under which the files that stand on this one name it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Plan.NumsOfPlan
import Johnson.Desc.K12.Plan.TestCut

set_option autoImplicit false
namespace H2U
open OnBytes OnBytes.Params Johnson.G.OfPlan

structure PlaceNums where
  chain : Nat
  start : Nat
  nums : TestNums
  idx : List (Nat × Nat)
  firstGroup : Nat
  answers : Nat
  early : Bool

structure Places4 where
  L : PlaceNums
  U : PlaceNums
  O : Option PlaceNums
  W : PlaceNums

/-- **The rows that the first chain's last test batches, off the planner's sized records**: the
planner's own reckoning in `reqPlanFrom`'s last turn (OnBytes/Params/DeriveReq.lean), by calls of
its pure functions: carried + sampleRows, where
  t           the positions of the last "LOC": `scopePositions` at the request's scope, at the
              agreement of the analysis of the group that was closed last (the links' group with the
              last link's k and h, and as many slots as the last group's kept rows ask)
  carried     1 + the kept messages' answers + t · (3 + the kept messages' main rows)
  sampleRows  the answers of the last group's members: the switch's target, the kept messages, the
              fold's mask (none)
Nothing where the request has no link (then no switch leads into the last group). The planner's two
refusals on the way (a bad analysis; t = 0) are not asked here: this is a reckoning over a plan that
was made. -/
def rowsAtLast (z : ProofSized) : Option Nat := do
  let gs := (reqGroups z.request).toList
  let g ← gs.getLast?
  let before ← gs.dropLast.getLast?
  let kept := keptOf g
  let keptRows := sumT (kept.map (·.shape.mainRows))
  let keptAnswers := sumT (kept.map (·.shape.answers))
  let closed : GroupSize :=
    { z.link.group with k := before.k, h := before.h, slots := 2 ^ clog2 (1 + keptRows) }
  let t := scopePositions z.set .request (analysis z.set closed).mainAt.agree
  let members : List OracleNotice :=
    [⟨g.target.shape, g.target.leafClass⟩] ++ kept.map (fun k => ⟨k.shape, k.leafClass⟩) ++
      [foldMaskNotice (ioppFoldShape ⟨z.request.code, z.request.maskCode, g.k, g.h⟩ {})]
  pure ((1 + keptAnswers + t * (3 + keptRows)) + sumT (members.map (·.shape.answers)))

def stageNums (y : StageSize) : Fmt.M1.Stage :=
  ⟨⟨y.g.main.logN, y.g.main.ell, y.g.main.r⟩, ⟨y.g.mask.logN, y.g.mask.ell, y.g.mask.r⟩, y.g.k,
    y.g.h, y.t⟩

/-- **What the places on a file's two later chains are made of**: cut as the rule's own
`fileOf` is cut (Johnson/G/RoundsOfPlan.lean), so that the key file and the proof file have one
text.
-/
structure LaterArgs where
  /-- for the words of a refusal -/
  file : String
  set : Setting
  /-- the sized batch record: the folded row's, Omega's and the own test's stages; its shape; its
  lines -/
  batch : LinSized
  /-- the three chains' plans and sendings -/
  P0 : Fmt.Plan
  P1 : Fmt.Plan
  P2 : Fmt.Plan
  c0 : Johnson.G.ChainSends
  c1 : Johnson.G.ChainSends
  c2 : Johnson.G.ChainSends
  /-- the made plans' entries of the shared and of the last chain, out of which the tests' stretches
  are cut -/
  es1 : List Fmt.Entry
  es2 : List Fmt.Entry
  /-- which of the first chain's trees the own test takes over (fileOf's last argument) -/
  input : Sent → Bool
  /-- how many groups the first chain's record holds at its end (it feeds SymbolComponent.groups alone) -/
  groupsFirst : Nat

structure Later3 where
  U : PlaceNums
  O : Option PlaceNums
  W : PlaceNums

/-- Plan/TestCut.lean's `testCutAt`, at a list of entries. -/
def cutOn (es : List Fmt.Entry) (ch i : Nat) (st : List IoppStage) : Option TestCut :=
  let cut := (es.drop i).take (1 + towerLen st)
  if st.length < 2 || cut.map (·.name) != "BAT" :: towerNames st then none
  else some ⟨ch, i, cut, ((es.take i).map (·.roots)).foldl (· + ·) 0, st⟩

def mkPlace (answers chain : Nat) (st : List StageSize) (rows work : Nat) (own : Bool) (t : TestCut)
    (fa : FirstAt) (g0 : Nat) (early : Bool) : PlaceNums :=
  { chain := chain, start := t.start
    nums :=
      { rows := rows, work := work, stages := st.map stageNums, ownMask := own, first := fa.1,
        free := t.roots, firstTree := fa.2 }
    idx := t.stages.map fun s => (s.code, s.maskCode), firstGroup := g0, answers := answers,
    early := early }

/-- **The three places on a file's two later chains**: the folded row's test, Omega's, the own test.
rows, work, ownMask: by the arguments of the planner's own calls of `planIopp`. first, firstTree: by
calls of the rule Johnson/G/RoundsOfPlan.lean (as `firstsOfPlan`). -/
def placesLater (A : LaterArgs) : Except String Later3 := do
  let S := A.batch.shape
  let a := A.set.samples
  let once := A.batch.lines.oneTime
  let w := fun (c : Scope) => A.set.workOf .query c
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some v => pure v
    | none => throw ("placesLater: " ++ A.file ++ ": nothing at " ++ what)
  let t0 ← treesSent (A.file ++ ", first chain") A.c0 A.P0 []
  let t1 ← treesSent (A.file ++ ", shared chain") A.c1 A.P1 (ownMasks A.c1.codes S A.P1.rounds)
  let t2 ← treesSent (A.file ++ ", second chain") A.c2 A.P2 []
  let sh := sharedOpens S t1
  let fU ← get "the folded row's test's first trees" (sh[1]?)
  let fO : Option FirstAt :=
    if S.sharedSplitNeeded then
      (sh[2 + (switchOpens 0 .folded t1).length]?).map fun x => (x.1.dropLast, 0)
    else none
  let fW ← get "the own test's first trees" (secondOpens S A.input t0 t1 t2).head?
  let tU ← get "the folded row's test" ((batPlaces A.es1)[0]?.bind fun i => cutOn A.es1 1 i S.testU)
  let tO := (batPlaces A.es1)[1]?.bind fun i => cutOn A.es1 1 i S.testOmega
  let tW ← get "the own test" ((batPlaces A.es2)[0]?.bind fun i => cutOn A.es2 2 i S.testOwn)
  let rB := S.choice.masksRide
  pure
    { U := mkPlace a 2 A.batch.folded.stages (S.fold.index.answers + S.fold.columns + 1 + 2 * a)
        (w (if once then .once else .shared)) (!S.masksAhead) tU (fU.1, 0) 2 rB
      O := match tO, fO with
        | some tO, some fO =>
          some (mkPlace a 2 A.batch.omega.stages (1 + 2 * a) (w (if once then .once else .shared))
            true tO fO (2 + (tU.stages.length - 1)) rB)
        | _, _ => none
      W := mkPlace a 3 A.batch.own.stages (2 + 3 * a) (w (if once then .once else .request))
        (!S.masksAhead) tW (fW, t0.length + 1) (A.groupsFirst + 1) rB }

/-- The entries of a made plan's chain number ch. -/
def entriesOf (l : List Planned) (ch : Nat) : List Fmt.Entry :=
  ((l[ch]?).map fun P => P.rounds.map (·.entry)).getD []

/-- The proof file's arguments. groupsFirst: a group a link and the last test's, then the last
test's switches'. -/
def laterOfProof (m : Made) (groupsFirst : Nat) : LaterArgs :=
  let C := m.p.chains.made
  let riders := C.sized.proof.request.atStart.map (·.leafClass)
  { file := "proof file", set := C.sized.set, batch := C.sized.proof.batch
    P0 := m.p.chains.proof.first.given.plan, P1 := m.p.chains.proof.shared.given.plan,
    P2 := m.p.chains.proof.second.given.plan
    c0 := m.proof.1, c1 := m.proof.2.1, c2 := m.proof.2.2, es1 := entriesOf C.proof 1,
    es2 := entriesOf C.proof 2
    input := fun t => t.tag == .link 0 0 && riders.contains t.cls, groupsFirst := groupsFirst }

/-- The key file's arguments (`declKOf`'s own: Johnson/G/RoundsOfPlan.lean). groupsFirst: the
caller's to say: how many groups the one-time chain's record holds at its end. -/
def laterOfKey (m : Made) (groupsFirst : Nat) : LaterArgs :=
  let C := m.p.chains.made
  { file := "key file", set := C.sized.key.set, batch := C.sized.key.once
    P0 := m.p.chains.key.oneTime.given.plan, P1 := m.p.chains.key.shared.given.plan,
    P2 := m.p.chains.key.second.given.plan
    c0 := m.key.1, c1 := m.key.2.1, c2 := m.key.2.2, es1 := entriesOf C.key 1,
    es2 := entriesOf C.key 2
    input := fun t => t.tag == .indexMask, groupsFirst := groupsFirst }

/-- **The proof file's four places.** -/
def placesOfMade (m : Made) : Except String Places4 := do
  let Fs ← firstsOfPlan m
  let C := m.p.chains.made
  let z := C.sized.proof
  let locs := (m.p.chains.proof.first.given.plan.rounds.filter fun e => e.name == "LOC").length
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some v => pure v
    | none => throw ("placesOfMade: no cut at " ++ what)
  let tL ← get "the last test" (cutTestL C)
  let gL := locs + 1
  let X ← placesLater (laterOfProof m (gL + (tL.stages.length - 1)))
  pure
    { L := mkPlace C.sized.set.samples 1 z.last.stages
        (← get "the rows of the last test" (rowsAtLast z)) (C.sized.set.workOf .query .request)
        false tL Fs.L gL z.request.choice.masksRide
      U := X.U, O := X.O, W := X.W }

end H2U
