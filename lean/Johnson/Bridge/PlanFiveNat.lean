-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanFiveNat.lean: FIVE OF A CONFIGURATION's SEVEN PLANS, EACH WHOLE, AS A TEST THAT A
VERIFIER CAN RUN: `fiveOk M`: comparisons of natural numbers, over the planner's records and the
plans' own entries. IT RUNS: it imports Johnson/Bridge/PlanRulesNat.lean, and through it
PlanOkNat.lean, the planner and the format: no Mathlib, Cb or ThirdParty module.
Johnson/Bridge/PlanFiveNatEq.lean [not in this library] says what a yes gives.

What it asks. Of the shared chain and the second chain of a proof file and of a key file, and of the
entry file's chain: that the plan has as many entries as the records ask, and that each entry, in
the plan's order, passes at its slot (`slotOk`): the name; what is drawn; the bits of work; the
rows; it stands for one round; and the slot's count is at most 2^-128 of all the round's challenges,
the work counted in. So no entry of another name or form stands in these five plans. The rows of
slots, and the test, are those of Johnson/Bridge/PlanShared.lean, PlanChains.lean and
PlanEntry.lean: proved, for every record, in Johnson/Bridge/PlanFiveNatTie.lean. [None of these four
files is in this library.]

This file holds numbers of coding theory as bare arithmetic; it uses no statement on codes and
proves nothing. What its numbers are called leans on theorems of other files, and the count of bad
fold points on the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Main names, in the namespace `Johnson.Bridge.OkNat`:
  `zeroSlot`, `sendSlot`, `headSlots`: the rounds of the test on a stored table in front of its
    proximity tests: «LIN point» (eK + N eO, N the records' number of requests), the two sendings
    with their answers, «LOC», «LIN zeta».
  `withRows`, `linRows`, `linTests`: «SPLIT» and two tests, or one, as the planner lays them; each
    «BAT» of these tests has the rows that the planner reckons off the records.
  `sharedSlots`, `keySharedSlots`, `proofSecondSlots`, `keySecondSlots`, `entrySlots`: the five
    rows.
  `Point.bears x m`: the shared point's comparison with the sampler's term taken m times: a number
    and no more.
  `recordRule`: a rule (Johnson/Bridge/PlanRulesNat.lean) for an entry «RECORD» in another plan.
  `fiveOk M`: THE TEST: `planOk M`, the link's table's place good, `rowsOk` at the five plans, and
    `bears` at N + 1 at the proof file's shared point.

The counts, and whose they are. A BLOCK's BY A STATEMENT, at written rounds that are the format's:
«FOLD epsilon», «FOLD round», «CS» with its «SEND seed», «BASE lambda», «BASE»
(Johnson/Bridge/PlanWhole.lean's head; at the first «FOLD epsilon» of a test on Omega, in whose
message a root rides: Johnson/Bridge/FoldRoot.lean) [neither file is in this library]; under five
hypotheses: «LIN point». BY READING
of the library's definitions: «LOC», «LIN zeta» (Cb/Ld/LdLin.lean), «LINK point», «LINK», «LINK phi»
(Cb/Ld/LdLink.lean), «BAT». A COARSE CAP: the seeds of the sendings and «RECORD». 0 where nothing is
drawn.

Limits. A YES SAYS NOTHING OF A BLOCK: it holds counts. NO THEOREM SAYS YES AT ANY PLAN: files of
evaluations, not named here, have evaluated it at stored sets. NOT HERE: the first chain of a proof
file and of a key file. Who makes M is not asked: spend it with `configure l x cfg bits = .ok M`
beside it (Johnson/Desc/Ok/FormRules.lean's head names the theorems). WHICH KIND A DESCRIPTION GIVES
A ROUND is not read: the theorems ask seeds where a seed is drawn, else neither seeds nor sealed.
«RECORD» IS NO ROUND OF A CHAIN: of which written round its clause is said is open. THE LINK's TABLE
IS READ AT THE PROOF FILE's TABLE's RADIUS, both of its tables at that one; `good` holds that radius
at the link's own table. THE ROOM IS SMALL AT «LINK point»: by arithmetic outside Lean 128.154 bits
at the stored full size, 128.008 at the small sizes. WHERE THE FOLDED ROW's CODE AND OMEGA's ARE
ONE, the planner lays one test; `planOk` asks nine tests' rounds: so `fiveOk` says no to every such
configuration, and the «else» of `linTests` is never reached under it. More than one sample, or a
record with more than one answer, is refused. The key file's shared and second chains are read at
the key's setting; the planner makes them at the records' own (`configure_plans`): where the two
part, the test says no. PART OF THE 128 BITS ARE WORK at «LOC», «LINK», «CS», «BASE»; at «LOC» and
«LINK» the entry's work is held against the setting's; AT A TEST's «CS» AND «BASE» IT IS THE «BASE»
ENTRY's OWN, capped at 62: `fiveOk` alone does not hold it against the setting: `setWorkOk`
(Johnson/Bridge/PlanOkNat.lean) does, which `everyOk` (Johnson/Desc/Ok/FormRules.lean) asks beside
it; they count only for a carriage that reads a written message whose test of work fails as nothing
(`chalTo`, OnBytes/Slice/Draws.lean): a law that carries every written message loses them; what work
is worth is proved nowhere here. THE COST: `planOk`, which caps the work of every entry, stands
first; `slotOk` holds an entry's numbers before a power of them is taken; the records' own sizes
reach a power before anything holds them. The limits of Johnson/Bridge/PlanOkNat.lean hold. No sum
over rounds.

-/
import Johnson.Bridge.PlanRulesNat

set_option autoImplicit false

namespace Johnson.Bridge.OkNat
open OnBytes OnBytes.Params

/-- A round in which nothing is drawn; the count 0. -/
def zeroSlot (name : String) : Slot := ⟨name, false, 0, 0, 0, 0, 0, 0, fun _ => 0, fun _ => 0⟩

/-- The coarse count of a seed for m messages with lists of at most L, at a point of lg
coordinates. -/
def seedCount (lg m L : Nat) : Nat := m * (L * (L - 1) / 2 * clashSeeds lg)

/-- A seed: a point of lg coordinates and one element other than 0. -/
def seedSlot (name : String) (lg m L : Nat) : Slot :=
  ⟨name, true, lg + 1, 1, 0, 0, 0, 0, fun _ => 0, fun _ => seedCount lg m L⟩

/-- The seed of the sample of the oracle messages o of one prover's message. Each oracle message is
read as a function on a cube of `cubeBits` variables; one point serves all: it has the coordinates
of the largest cube. As many messages as o has. -/
def sendSlot (o : List SampleSize) (L : Nat) : Slot :=
  seedSlot "SEND seed" (o.foldl (fun c x => max c x.cubeBits) 0) o.length L

/-- A round that draws a point of m coordinates and nothing else; the count: m q^(m - 1), the
library's `errZeta` and `errPhi`: a bound on the zeros of a polynomial in m variables, of degree at
most one in each, that is not 0. -/
def pointSlot (name : String) (m : Nat) : Slot :=
  ⟨name, false, m, 0, 0, 0, 0, 0, fun _ => 0, fun _ => m * q ^ (m - 1)⟩

/-- The seven rounds of the test on a stored table in front of its proximity tests: «LIN point»; the
sending of the folded row: its seed, its answers; «LOC»: `cols` positions, the shape's number of
columns, that all miss the rT + 1 or more places where a word is off; the sending of Omega and what
rides beside it; «LIN zeta». w: the bits of work of a round of positions on the chain. -/
def headSlots (rT L cols w : Nat) (x : Point) (Y : LinSize) : List Slot :=
  [⟨"LIN point", false, x.T.v + x.klo, 0, 0, 0, 0, 0, fun _ => 0, fun _ => x.cnt⟩,
    sendSlot [Y.u] L,
    zeroSlot "SEND answer",
    ⟨"LOC", false, 0, 0, cols, x.T.code.logN, 0, w, fun _ => 0,
      fun _ => (2 ^ x.T.code.logN - rT - 1) ^ cols⟩,
    sendSlot (Y.omega :: Y.besideOmega) L,
    zeroSlot "SEND answer",
    pointSlot "LIN zeta" Y.rowsLog]

/-- A test's slots with the number of rows of its batching asked. -/
def withRows (n : Nat) : List Slot → List Slot
  | x :: r => { x with rows := fun _ => n } :: r
  | [] => []

/-- The numbers of rows that are batched in front of the test on the folded row, and in front of the
test on Omega: THE PLANNER's OWN TWO SUMS, term for term (`linPlanShared`,
OnBytes/Params/DeriveLin.lean): the index's answers + the opened columns + 1 + 2 samples; 1 + 2
samples. What each term stands for the planner's text does not say, and this file does not either.
-/
def linRows (s : Setting) (X : LinSized) : Nat × Nat :=
  (X.shape.fold.index.answers + X.shape.fold.columns + 1 + 2 * s.samples, 1 + 2 * s.samples)

/-- The proximity tests behind the test on a stored table, as the planner lays them: where the
folded row's code and Omega's differ, «SPLIT» and two tests; else one (never reached under `planOk`:
the head's Limits). -/
def linTests (s : Setting) (X : LinSized) (ts : List Test) : List Slot :=
  if X.shape.sharedSplitNeeded then
    zeroSlot "SPLIT" :: ((ts.take 1).flatMap fun T => withRows (linRows s X).1 T.slots) ++
      ((ts.drop 1).take 1).flatMap fun T => withRows (linRows s X).2 T.slots
  else (ts.take 1).flatMap fun T => withRows (linRows s X).1 T.slots

/-- The entries of the plan number i of a list of plans. -/
def entriesAt (l : List Planned) (i : Nat) : List Fmt.Entry :=
  ((l.drop i).take 1).flatMap fun P => P.plan.entries

/-- A chain with the test on a stored table: the point number i of `planPoints` (0: the proof
file's; 1: the key file's); the tests from number j of the nine on (`nineTests`: the proof file's
last, folded, Omega, own: 0 to 3; the key file's ranges, folded, Omega, own: 4 to 7; the entry's:
8); «SEAL». -/
def linSlots (rT L : Nat) (M : Configured) (i j : Nat) (s : Setting) (codes : Codes) (X : LinSized)
    (scope : Scope) : List Slot :=
  ((((planPoints rT M).drop i).take 1).map (·.2)).zip (linSizeOf codes X).toList |>.flatMap
      (fun p => headSlots rT L X.shape.fold.columns (s.workOf .query scope) p.1 p.2) |>.append
    (linTests s X ((planTests M).drop j) ++ [zeroSlot "SEAL"])

/-- The proof file's shared chain. -/
def sharedSlots (rT L : Nat) (M : Configured) : List Slot :=
  linSlots rT L M 0 1 M.sized.proof.set M.sized.proof.codes M.sized.proof.batch .shared

/-- The key file's shared chain: a one-time chain's bits of work. -/
def keySharedSlots (rT L : Nat) (M : Configured) : List Slot :=
  linSlots rT L M 1 5 M.sized.key.set M.sized.key.codes M.sized.key.once .once

/-- A proof file's second chain: the request's own test; the rows of its batching: the planner's own
sum, 2 + 3 samples (`linPlanSecond`, OnBytes/Params/DeriveLin.lean). -/
def proofSecondSlots (M : Configured) : List Slot :=
  (((planTests M).drop 3).take 1).flatMap fun T =>
    withRows (2 + 3 * M.sized.proof.set.samples) T.slots

/-- A key file's second chain: the committer's own test. -/
def keySecondSlots (M : Configured) : List Slot :=
  (((planTests M).drop 7).take 1).flatMap fun T =>
    withRows (2 + 3 * M.sized.key.set.samples) T.slots

/-- The link's table at a radius. -/
def linkPoint (rT : Nat) (M : Configured) : Point := ⟨M.sized.link.table, rT, 0, 0⟩

/-- The rounds of a link between the first table and a further copy, in front of its proximity test.
«RECORD»: the seed of the table's record, where it has one. «LINK point»: one fold point for both
tables: a bound on the bad fold points of each (`top`, twice) and a field term. The sending of the
two folded rows: one seed for two messages; the answers. «LINK»: two lists of columns, one for each
table: the larger of the two counts «all of one list miss». «LINK phi»: a point. -/
def entryHead (rT L w cube : Nat) (x : Point) (S : LinkShape) : List Slot :=
  [seedSlot "RECORD" (clog2 x.T.code.ell) 1 (listMax x.n (x.n - x.k) rT)] ++
  [⟨"LINK point", false, x.T.v, 0, 0, 0, 0, 0, fun _ => 0,
      fun _ => x.top + x.top + x.T.v * q ^ (x.T.v - 1)⟩,
    seedSlot "SEND seed" cube 2 L,
    zeroSlot "SEND answer",
    ⟨"LINK", false, 0, 0, S.columnsFirst + S.columnsFurther, x.T.code.logN, 0, w, fun _ => 0,
      fun _ => max ((x.n - rT - 1) ^ S.columnsFirst * x.n ^ S.columnsFurther)
        (x.n ^ S.columnsFirst * (x.n - rT - 1) ^ S.columnsFurther)⟩,
    pointSlot "LINK phi" (clog2 x.T.code.ell)]

/-- The entry file's chain: the link, then the ninth test; the rows of its batching: the planner's
own sum, term for term: twice the answers of the tables' shape + the opened columns of the first
table + those of the further one + 1 + 2 samples (`linkPlan`, OnBytes/Params/Derive.lean). -/
def entrySlots (rT L : Nat) (M : Configured) : List Slot :=
  entryHead rT L (M.sized.set.workOf .query .once)
      (clog2 M.sized.link.shape.rows + clog2 M.sized.link.linked.group.main.ell)
      (linkPoint rT M) M.sized.link.shape ++
    (((planTests M).drop 8).take 1).flatMap fun T =>
      withRows (2 * M.sized.link.shape.table.answers + M.sized.link.shape.columnsFirst +
        M.sized.link.shape.columnsFurther + 1 + 2 * M.sized.set.samples) T.slots

/-- A stored table's record's seed: the coarse count for one message,
at the Johnson bound's list of the table's code at the place's radius. -/
def recordRule (x : Point) : Rule :=
  ⟨"RECORD", fun _ => true,
    fun _ => seedSlot "RECORD" (clog2 x.T.code.ell) 1 (listMax x.n (x.n - x.k) x.e)⟩

/-- The comparison at the shared point, with the sampler's term taken m times. Why N + 1 is asked:
the count has a part that hangs on the key alone and one part for each of N requests; were these N +
1 sets carried apart, each with the sampler's term of its own, the comparison would be this one at m
= N + 1 (Johnson/Bridge/PlanShared.lean's head). A number and no more: no theorem spends it but
`PointPlace.priced_of_bears`. [That file, and with it that theorem, is not in this library.] -/
def Point.bears (x : Point) (m : Nat) : Bool :=
  decide (x.cnt * 2 ^ 193 + 3 * (x.T.v + x.klo + 0) * x.all * m ≤ x.all * 2 ^ (0 + 65))

/-- The proof file's shared point bears the sampler's term once for each request and once more. -/
def bearsAt (rT : Nat) (M : Configured) : Bool :=
  (((planPoints rT M).take 1).map (·.2)).all fun x => x.bears (x.N + 1)

/-- The five plans, at two letters: rT, the radius at which the stored tables are read; L, a bound
on the lists of the messages under a sending's seed. `fiveOk` sets them to the planner's. -/
def fiveAt (rT L : Nat) (M : Configured) : Bool :=
  (linkPoint rT M).good &&
    rowsOk (entriesAt M.proof 1) (sharedSlots rT L M) &&
    rowsOk (entriesAt M.proof 2) (proofSecondSlots M) &&
    rowsOk (entriesAt M.key 1) (keySharedSlots rT L M) &&
    rowsOk (entriesAt M.key 2) (keySecondSlots M) &&
    rowsOk M.entry.plan.entries (entrySlots rT L M)

/-- **THE TEST**: `planOk`; the five plans; the shared point bears N + 1 times the sampler's term.
-/
def fiveOk (M : Configured) : Bool :=
  planOk M && fiveAt (tableRad M) (listTop M) M && bearsAt (tableRad M) M

end Johnson.Bridge.OkNat
