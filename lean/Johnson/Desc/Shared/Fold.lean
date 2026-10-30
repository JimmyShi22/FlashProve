-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Fold.lean: the fold over the shared hash chain's view: six steps, two proximity
tests and the seal. The decision on the chain is this fold at the planner's parameters: descSharedZ
in Par.lean.

Status. A proof file holds three hash chains. The files of this directory define the decision on one
of them, the shared, middle chain; nothing here decides the other two. The decision has been
evaluated, and no theorem is proved about it. It was run on one stored proof of each of two sizes,
where it said yes, and on altered inputs: the command in Main.lean runs altered views, sizes and
keys through descSharedZ. Further altered inputs (changed plans, and made-up states for single
checks) were run through descShared or through single steps, with a Dec.lean whose sched had one
clause fewer than this library's. In all these runs the sizes, the key and the view came from the
program's own planner and file-reading routines, and the altered inputs were made in memory. Nothing
is claimed on soundness, on an honest prover or on hiding.
What this comment says of the decision rests on reading and on runs; it is not machine-checked. The
words are explained in State.lean.

What the decision relies on:
  The carried state holds two records of the program whole: Statement and TreeBook (State.lean).
  The seven ground functions (callG, Ground.lean) and the two proximity tests (TestIn.run, Dec.lean)
    are calls of the program's own routines. At these places the decision checks what these routines
    check, and no theorem here says what that is.
  The table's key is an argument, which the caller must supply. Nothing here ties it to the table.

The fold by itself is not the decision.
  The plan's entries are a field of the parameters p. runShared, decideShared and descShared take p
    as an argument and hold the view against these entries only. A run has shown what that leaves
    open: with the entry for a proximity test's last round changed to count fewer positions, down to
    one, and the view cut to fit, the fold says yes. So, given a plan with fewer spot checks, the
    fold accepts a proof that is cut to match. Par.lean takes the entries from the planner instead.

What the decision does not check:
  That the stored table's opened columns, or any other opened column, lie under their roots. A view
    holds no root (Blk.recvRoot, OnBytes/Iop/Ground.lean), so this is the duty of whoever makes the
    view from the file. Of the stored columns step2 asks what Blk.readStored asks: the tree key of
    the stored table, the position, the width and the order.
  That the values drawn in the view are the hash function's. No hash is called in the fold.
  That the shared chain is connected to the other two chains.
  The further duties of a caller that the heads of Dec.lean and Par.lean list.

Checks that lack a test of their own: no input has been run on which the check is seen to be
the one that refuses.
  Untried: that the trees can be laid out when oracle messages are received (layTrees in
    Blk.receiveOracles, callG.recv). The one altered input that was made for it, mask rows of two
    lengths in one tree, was not refused. It was badly made: the second message was put beside
    Omega, which has no mask rows, and layTrees compares the lengths only where the tree already
    holds mask symbols.
  Not tested; by reading of the code, which is no proof, they cannot fail at callG because of
    how the values are built. callAt: that no message is left open (ctxAt gives the routine no
    round, and an item can be taken from a round only). sendP: that the numbers increase and that
    none of the messages is sampled yet (both are what Blk.receiveOracles has just made). step2:
    that each draw is in the list, that its column is there and that its row can be built
    (readStoredP has passed before). step5: that the row (Fold) is a plain row (linFoldRow starts
    from the empty row and only adds terms).
  Not tested; they read the codes and the shape only. step0: Codes.lengthsOk and linOk. step1: that
    linWithU gives a value and that the mask message's number is there. sendP: that some message has
    answers. Send.admit (callG.admit): that the places of the pad exist.
  Not tested in the runs of the fold: TestIn.sched (Dec.lean). No altered input was made there for
    any of its clauses. The head of Dec.lean tells what was evaluated for it.
  endStep has been tested by itself, but no chain in this directory calls it.

The end of a run. In the program a run on a view ends with six questions (Blk.runOn,
OnBytes/Iop/Ground.lean). Here sealStep asks that no entry, no round and no opened column is left
over. That the last entry counts no batched rows is asked in planOk, not in sealStep or endStep, so
a caller that starts from frontAt without planOk skips it. The state has no field for a failed test
or an open message: a check that only marks a failure and goes on in the program is a refusal at
once here (callAt, TestIn.run), and both ask that no message is open.

How the rounds are shared out. Every step and every test takes a prefix of the entries and of the
rounds that Mid still holds, the same number of each, and passes the rest on. sealStep asks that
exactly one entry and one round are left. So the pieces cover the given entries and rounds in order,
with no gap and no overlap.

The two tests. testAt gives the state and the test's own entries and rounds to TestIn.run, which
checks the schedule, adds the group's open rows a second time through Blk.addRow, and makes one call
of the program's routine ioppVerify at a context built from the state. The test must use up its
entries and rounds. What the call leaves is copied back whole. There is no step between the two
tests: what the first leaves goes to the second unchanged.

Main names:
  Mid L: the state with the plan's entries and the view's rounds that are still to come. Mid,
    Mid.step, testAt, sealStep, endStep and frontAt work for any type L of named values, so another
    chain can use them.
  fits e r: the round draws as many elements, positions and matrix entries as the plan's entry says.
  Mid.step: one step on the next k rounds, each of which must fit its entry.
  sixNames, answersMax, sixNZ, planOk: a check on the plan alone, told at planOk.
  six: the six steps in a row. They take 1, 2, 1, 2 and 1 rounds, and then 1 round, or 0 where G_u
    and Omega have the same code.
  testLen, testAt: a proximity test. It takes the rounds up to and including the first entry named
    "BASE".
  allTested: the test of every group has begun, and every sampled oracle message is in a group.
  sealStep: the last round, "SEAL", and the chain's end. endStep: the end of a chain without such a
    round.
  frontAt, front: what is asked before round 0.
  upToU: from round 0 to the last round of the first test.
  runShared: the whole chain. decideShared: the fold's yes or no.
  descShared: the fold at the program's own ground calls (callG), general in its parameters. It is
    not the decision. It takes the plan's entries from its caller, and with an entry that counts
    fewer positions and a view cut to fit it still says yes. The decision is descSharedZ (Par.lean),
    which takes no entry.
  places: the same steps by name, for a command that prints where a run ends.

What is not claimed. Nothing on soundness, on an honest prover or on hiding, as said above.

-/
import Johnson.Desc.Shared.Steps
import Johnson.Desc.Shared.Dec
import OnBytes.Maker.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

variable {L : Type}

/-- The state, with the entries and rounds that are still to come. -/
structure Mid (L : Type) where
  d : DState L
  entries : List Fmt.Entry
  rounds : List Fmt.RoundView

/-- The round draws as many elements, positions and matrix entries as the plan's entry says. -/
def fits (e : Fmt.Entry) (r : Fmt.RoundView) : Bool :=
  r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
    r.drawn.trits.length == e.trits

/-- One step on the next k rounds. Refuses unless k rounds and k entries are left and each of these
rounds fits its entry. The step f gets the k rounds; the k entries are dropped with them. -/
def Mid.step (m : Mid L) (k : Nat) (f : DState L → List Fmt.RoundView → Option (DState L)) :
    Option (Mid L) :=
  if decide (k ≤ m.rounds.length) && decide (k ≤ m.entries.length) &&
      ((m.entries.take k).zip (m.rounds.take k)).all (fun x => fits x.1 x.2) then
    (f m.d (m.rounds.take k)).map fun d' =>
      { d := d', entries := m.entries.drop k, rounds := m.rounds.drop k }
  else none

/-- The names of the rounds that the six steps take, in order. -/
def sixNames (p : Par) : List String :=
  ["LIN point", "SEND seed", "SEND answer", "LOC", "SEND seed", "SEND answer", "LIN zeta"] ++
    if p.S.sharedSplitNeeded then ["SPLIT"] else []

/-- The largest number of answers among the oracle messages of a sending. -/
def answersMax (sent : Array OracleNotice) : Nat := sent.foldl (fun a n => max a n.shape.answers) 0

/-- For each of these rounds, the number that its entry must have as drawNZ (how many of the drawn
elements must not be 0). -/
def sixNZ (p : Par) : List Nat :=
  [0, answersMax (#[(⟨p.S.fold.u, p.S.fold.leafClass⟩ : OracleNotice)] ++ (linWithU p.S).getD #[]),
   0, 0, answersMax (linMessageOmega p.S), 0, 0] ++ if p.S.sharedSplitNeeded then [0] else []

/-- A check on the plan alone. The entries for the six steps have the names of sixNames and the
numbers of sixNZ, and none of them counts batched rows. The entry "LOC" has the logN of the table's
code and counts at least one position. The plan's last entry counts no batched rows. -/
def planOk (p : Par) : Bool :=
  let es := p.entries.take (sixNames p).length
  es.map (·.name) == sixNames p && es.map (·.drawNZ) == sixNZ p && es.all (·.rows == 0) &&
    ((es[3]?).map fun e => e.logN == p.S.fold.index.code.logN && decide (0 < e.poss)).getD false &&
    (p.entries.getLast?.map (·.rows == 0)).getD false

/-- The six steps in a row. -/
def six (G : Ground Loc) (p : Par) (m : Mid Loc) : Option (Mid Loc) := do
  let m₀ ← m.step 1 (step0 G p)
  let m₁ ← m₀.step 2 (step1 G p)
  let m₂ ← m₁.step 1 (step2 G p)
  let m₃ ← m₂.step 2 (step3 G p)
  let m₄ ← m₃.step 1 (step4 p)
  m₄.step (if p.S.sharedSplitNeeded then 1 else 0) (step5 G p)

/-- How many rounds a proximity test takes: up to and including the first entry named "BASE". -/
def testLen (es : List Fmt.Entry) : Nat := (es.takeWhile (·.name != "BASE")).length + 1

/-- The proximity test on group g: TestIn.run (Dec.lean) on the state and on the test's own entries
and rounds. What it returns is copied into the state. -/
def testAt (p : Par) (g : Nat) (stages : List IoppStage) (mask : Option Nat) (m : Mid L) :
    Option (Mid L) :=
  let k := testLen m.entries
  if decide (k ≤ m.entries.length) && decide (k ≤ m.rounds.length) then
    let x : H2U.TestIn :=
      { samples := p.samples, firstTree := p.firstTree, entries := m.entries.take k,
        roots := m.d.roots, rounds := m.rounds.take k, opened := m.d.opened, st := m.d.st,
        book := m.d.book, g := g, stages := stages, choice := p.S.choice, mask := mask }
    match x.run with
    | .error _ => none
    | .ok o =>
      some { d := { m.d with st := o.st, book := o.book, roots := o.roots, opened := o.opened },
             entries := m.entries.drop k, rounds := m.rounds.drop k }
  else none

/-- The test of every group has begun, and every sampled oracle message is in a group. It follows
Blk.requireAllTested (OnBytes/Iop/Ground.lean). -/
def allTested (S : Statement) : Bool :=
  S.groups.all (·.inRun) && S.oracles.all fun x => !x.sampled || !x.groups.isEmpty

/-- The last round and the chain's end. Exactly one round and one entry are left. The entry is named
"SEAL" and its drawNZ is 0. The round fits it, holds no item and draws no element, position or
matrix entry. allTested holds, and no opened column is left. That the entry counts no batched rows
is asked in planOk, not here. -/
def sealStep (m : Mid L) : Option (DState L) :=
  match m.rounds, m.entries with
  | [r], [e] =>
    if e.name == "SEAL" && e.drawNZ == 0 && fits e r && r.vals.isEmpty && silent r &&
        allTested m.d.st &&
        m.d.opened.isEmpty then some m.d
    else none
  | _, _ => none

/-- The end of a chain that has no sealing round: no entry, round or opened column is left, and
allTested holds. That the last entry counts no batched rows is not asked here. No chain in this
directory calls it. -/
def endStep (m : Mid L) : Option (DState L) :=
  if m.rounds.isEmpty && m.entries.isEmpty && allTested m.d.st && m.d.opened.isEmpty then some m.d
  else none

/-- A chain's first state with all its entries and rounds still to come. Refuses unless every word
of a field element is below the prime in the key's seeds (Maker.okSeeds) and in the view's items and
opened columns (Maker.okView). -/
def frontAt (p : Par) (d₀ : DState L) (v : Fmt.View) : Option (Mid L) :=
  if Maker.okSeeds p.key && Maker.okView v then
    some { d := d₀, entries := p.entries, rounds := v.rounds }
  else none

/-- The shared chain before round 0: planOk, then frontAt at the state start. -/
def front (p : Par) (codes : Codes) (v : Fmt.View) : Option (Mid Loc) :=
  if planOk p then frontAt p (start codes v.opened) v else none

/-- From round 0 to the last round of the test on G_u's group. -/
def upToU (G : Ground Loc) (p : Par) (codes : Codes) (v : Fmt.View) : Option (Mid Loc) := do
  let m ← front p codes v
  let m₅ ← six G p m
  testAt p m₅.d.loc.gU p.S.testU m₅.d.loc.mask m₅

/-- The whole chain: the state at its end, or a refusal. -/
def runShared (G : Ground Loc) (p : Par) (codes : Codes) (v : Fmt.View) :
    Option (DState Loc) := do
  let mU ← upToU G p codes v
  let mO ← if p.S.sharedSplitNeeded then testAt p mU.d.loc.gO p.S.testOmega none mU else some mU
  sealStep mO

/-- The chain's steps in order, by name: the same steps as in runShared, so that a command can print
where a run ends. It is no part of the decision. -/
def places (G : Ground Loc) (p : Par) : List (String × (Mid Loc → Option (Mid Loc))) :=
  [("step0", (·.step 1 (step0 G p))), ("step1", (·.step 2 (step1 G p))),
   ("step2", (·.step 1 (step2 G p))), ("step3", (·.step 2 (step3 G p))),
   ("step4", (·.step 1 (step4 p))),
   ("step5", (·.step (if p.S.sharedSplitNeeded then 1 else 0) (step5 G p))),
   ("testU", fun m => testAt p m.d.loc.gU p.S.testU m.d.loc.mask m),
   ("testOmega", fun m =>
     if p.S.sharedSplitNeeded then testAt p m.d.loc.gO p.S.testOmega none m else some m),
   ("seal", fun m => (sealStep m).map fun d => { d := d, entries := [], rounds := [] })]

/-- The fold's yes or no. -/
def decideShared (G : Ground Loc) (p : Par) (codes : Codes) (v : Fmt.View) : Bool :=
  (runShared G p codes v).isSome

/-- The fold at the program's own ground calls, general in its parameters. It is not the decision.
It takes the plan's entries from its caller, and with an entry that counts fewer positions and a
view cut to fit it still says yes. The decision is descSharedZ (Par.lean), which takes no entry. -/
def descShared (p : Par) (codes : Codes) (v : Fmt.View) : Bool := decideShared callG p codes v

end Desc.Shared
