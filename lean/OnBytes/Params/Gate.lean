-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Gate.lean: conditions that the programs ask of the public files before they admit
them.

Committer, prover and verifier refuse public files whose numbers miss one of a list of conditions
(blocks/frame/hiding_conditions.h). The conditions compare public numbers. A list is the positions
that one round draws. Draws are counted with their repeats, and the lists at which one encoding of a
row is opened add up.
 - A row has at least as many random entries as there are draws of positions at which it is opened.
 - A mask row has at least 2 k + 1 - h entries, for a fold over k row variables, h of them shared
   with the mask rows.
 - A message from which blocks take mask entries has at least as many entries as are taken.
 - An oracle message of the test on the table has room, beside its data, for one entry for each
   answer to its sample. With a record, a row of the table has three more places for each answer.
 - Oracle messages of one prover's message that share a class of leaves are read at the same lists.
 - A stored table's rows have at least as many random entries as columns are drawn of it in one
   one-time test, or in its own link, and in all the batches that it covers. Links from the first
   table to further copies are not counted, nor how often anything was in fact begun: that is no
   fact of the public files.
 - A leaf's salt has at least 40 bytes.
 - The test on the table is sized for as many requests as a batch may hold.
 - A bound on the chance that an honest range check fails, summed over all requests that a key can
   serve, is at most 2 ^ -target.
The C++ verifier refuses under the name parameters-not-admitted when one fails. This file renders
the conditions so that the same public files are refused here. The part on the key's proof of the
ranges is in OnBytes/Plan/RangesGate.lean. `configure` (OnBytes/Params/Configure.lean) asks all
parts.

The numbers that are tested were derived elsewhere. This file computes what they must cover a second
time, by another route, to catch a slip in the sizing. It does not call the sizing's routines again:
it takes how often a row is opened from the finished plans, and which rows a list reads from the
shapes.

Main definitions: `listsOf`, `scalarsOf`, `RangeCheck`, `rangeCheckBits`, `missedInTest`,
`missedInTheTablesLeaves`, `TableGate`, `missedOnTheTable`, `missedInTheLinks`,
`missedInTheChecks`.
What is not claimed: anything on what these conditions achieve.
-/
import OnBytes.Params.DeriveReq
import OnBytes.Params.Names

namespace OnBytes.Params

/-- For each round of a chain's plan that draws positions, in the order of the rounds: how many it
draws. -/
def listsOf (p : Planned) : List Nat :=
  (p.rounds.filter fun r => kindOf r.entry.name == some .positions).map (·.entry.poss)

/-- The elements of the extension field, other than sample answers, that a routine's messages
hold. Messages that no round has taken in yet count too. -/
def scalarsOf (s : Setting) (x : Planning Unit) : Except String Nat :=
  match x { set := s } with
  | .error e => .error e
  | .ok (_, p) =>
    let bytes := fun (msg roots answers : Nat) => msg - 32 * roots - 24 * answers
    .ok ((p.rounds.foldl (fun n r => n + bytes r.entry.msg r.entry.roots r.entry.answers) 0 +
      bytes p.openBytes p.openRoots p.openAnswers) / 24)

/-- One range check of a request. `rows` and `columns` are those of the matrix of whole numbers, the
unpacked cells, not of the oracle message's rows. Every cell is below `bound` in absolute value, at
the worst cells that a client's request can bring about. There are `combinations` combinations of
each row's cells, with coefficients 0 (probability 1/2), 1 and -1 (1/4 each). A combination must lie
from -range to range - 1, which its two digits, of `digitBits` bits, must represent exactly. -/
structure RangeCheck where
  rows : Nat
  columns : Nat
  combinations : Nat
  bound : Nat
  range : Nat
  digitBits : Nat × Nat
  deriving DecidableEq, Repr, Inhabited

/-- A lower bound on minus the binary logarithm of the chance that an honest prover fails the
check: range ^ 2 * 1.4426 / (columns * (bound - 1) ^ 2), rounded down, less 1 and less the
rounded-up logarithms of the rows and of the combinations; 2 ^ 30 if the quotient reaches that. It
is a tail bound for one combination and a union over rows and combinations. The derivation is given
above range_check_bits in blocks/frame/hiding_conditions.h and is not proved here. None if the
numbers are out of range, or if the digits do not represent the range: the bound would then not be
about what is tested. -/
def rangeCheckBits (c : RangeCheck) : Option Int :=
  let digits := c.digitBits.1 + c.digitBits.2
  if c.rows == 0 || c.columns == 0 || c.combinations == 0 || c.bound < 2 || c.range == 0 then none
  else if 2 ^ 40 ≤ c.range || 2 ^ 32 ≤ c.bound || 2 ^ 32 ≤ c.columns || 2 ^ 40 ≤ c.rows ||
      2 ^ 16 ≤ c.combinations then none
  else if 41 < digits || 2 ^ digits != 2 * c.range then none
  else
    let bits := c.range * c.range * 14426 / (c.columns * (c.bound - 1) * (c.bound - 1) * 10000)
    if 2 ^ 30 ≤ bits then some (2 ^ 30)
    else some ((bits : Int) - 1 - (clog2 c.rows : Int) - (clog2 c.combinations : Int))

/-- The code of a number in a list; a code without entries if the number names none. -/
def codeAt (l : Array Code) (i : Nat) : Code := l.getD i default

/-- One proximity test: its i-th list reads the rows of its i-th stage and nothing else. True if a
stage's main or mask rows have fewer random entries than draws, if a mask row has fewer than
2 k + 1 - h entries (k, h: the stage's row variables, of main and of mask rows), or if a stage has
no list. `moreMain` and `moreMask` are further draws on the first stage's rows. The difference is
one of natural numbers, exact for h ≤ 2 k + 1. The caller owes h ≤ k: `configure` asks this test
after it has planned every stage, and a plan refuses a group with h > k (`shapeFault`). -/
def missedInTest (codes : Codes) : List IoppStage → List Nat → Nat → Nat → Bool
  | [], _, _, _ => false
  | _ :: _, [], _, _ => true
  | x :: xs, t :: ts, moreMain, moreMask =>
    let main := codeAt codes.base x.code
    let mask := codeAt codes.mask x.maskCode
    main.r < t + moreMain || mask.r < t + moreMask || mask.ell < 2 * x.k + 1 - x.h ||
      missedInTest codes xs ts 0 0

/-- What shares a class of leaves in one prover's message shares a tree and its leaves. True if two
such oracle messages are read at different sets of lists. -/
def missedInLeaves : List (OracleNotice × Nat) → Bool
  | [] => false
  | x :: xs => (xs.any fun y => y.1.leafClass == x.1.leafClass && y.2 != x.2) || missedInLeaves xs

/-- True if `missedInLeaves` is true of one of the three prover's messages with oracle messages of
the test on the table. Each oracle message goes with the set of its lists, one bit for each: 1 the
folded row's test, 2 Omega's, 4 a request's own. True too if W and Omega differ in code
(`ownSplitNeeded`), which is not handled here, or if U's or W's message cannot be formed. -/
def missedInTheTablesLeaves (S : LinShape) : Bool :=
  let split := S.sharedSplitNeeded
  let second := (linMessageOmega S).toList
  let omega := zipT (List.range second.length) second |>.map fun x =>
    (x.2, if x.1 == 0 then (if split then 2 else 1) + 4
      else if split && x.1 == 1 then 3 else if split then 2 else 1)
  match linMessageU S, linMessageW S with
  | some u, some w =>
    S.ownSplitNeeded || missedInLeaves (u.toList.map (·, 1)) || missedInLeaves omega ||
      missedInLeaves (w.toList.map (·, 4))
  | _, _ => true

/-- What the gate reads of one test on the table: in a batch, or the committer's own. -/
structure TableGate where
  sized : LinSized
  codes : Codes
  shared : Planned
  second : Planned
  /-- the rows on the table that are pending before the test -/
  pending : Nat
  /-- in a key: the parts of all lookups of the ranges' proof; else 0 -/
  parts : Nat

/-- The part on one test on the table. True if a condition is missed. `need`, the entries taken of
the message of masks for the pending rows: one for each pending row; 1 + 2 * kCol for the batching,
if there are several rows; the pad. In a key the rows come from the proof of the ranges, one for
each part of each lookup, and each takes a second entry. The further draws: Omega is read by the
batch's test and by every request's own; the message of masks that splits a row between two groups
is read at both groups' lists. -/
def missedInOneTest (l : Lines) (g : TableGate) : Bool :=
  let x := g.sized
  let S := x.shape
  let codes := g.codes
  let once := x.lines.oneTime
  let requests := if once then 1 else l.slots
  let shared := listsOf g.shared
  let own := listsOf g.second
  let split := S.sharedSplitNeeded
  let ellOf := fun (o : OracleShape) => (codeAt codes.base o.code).ell
  let inARow := l.tableData + l.tableRandom
  let columns := 2 ^ S.kCol
  let need := g.pending + (if once then g.parts else 0) +
    (if 1 < g.pending then 1 + 2 * S.kCol else 0) + l.answers
  let tU := shared.getD 1 0
  let tOmega := if split then shared.getD (1 + S.testU.length) 0 else tU
  let tOwn := own.headD 0
  x.lines.requests != requests ||
  shared.length != 1 + S.testU.length + (if split then S.testOmega.length else 0) ||
  own.length != S.testOwn.length || own.isEmpty ||
  l.tableData < S.matrixRows * 2 ^ S.kLo + 3 * l.answers ||
  S.fold.u.mainRows * ellOf S.fold.u < inARow + l.answers ||
  S.omega.mainRows * ellOf S.omega < S.matrixRows + l.answers ||
  S.w.mainRows * ellOf S.w < columns + (if S.w.maskRows != 0 then 0 else l.answers) ||
  x.input.shape.maskRows * (codeAt codes.mask x.input.shape.maskCode).ell < need ||
  (split && S.sharedSplit.maskRows * (codeAt codes.mask S.sharedSplit.maskCode).ell
    < 1 + l.answers) ||
  missedInTest codes S.testU (shared.drop 1) (if split then 0 else requests * tOwn)
    (if split then tOmega else 0) ||
  (split && missedInTest codes S.testOmega (shared.drop (1 + S.testU.length)) (requests * tOwn)
    tU) ||
  missedInTest codes S.testOwn own (tOmega + (requests - 1) * tOwn) 0

/-- The part on the table: the salt, the leaves, the tests on the table in a batch and once, the
link, and the table's own random entries. These must cover the columns of one one-time test (the
first table) or of the copy's own link, begun once (a further copy), and of `batches` batches. Links
from the first table to further copies are not counted, nor how often anything was in fact begun:
that is no fact of the public files. True if a condition is missed. -/
def missedOnTheTable (l : Lines) (batch once : TableGate) (link : LinkSized) (linkCodes : Codes)
    (entry : Planned) : Bool :=
  let lists := listsOf entry
  let test := link.shape.test
  let aBatch := (listsOf batch.shared).headD 0
  let oneTime := (listsOf once.shared).headD 0
  l.salt < 40 || missedInTheTablesLeaves batch.sized.shape ||
  missedInTheTablesLeaves once.sized.shape || missedInOneTest l batch || missedInOneTest l once ||
  lists.length != 1 + test.length || missedInTest linkCodes test (lists.drop 1) 0 0 ||
  lists.headD 0 != link.shape.columnsFirst + link.shape.columnsFurther ||
  l.tableRandom < max oneTime link.shape.columnsFurther + batch.sized.batches * aBatch

/-- True if a condition is missed in a link from number i on. Each link is taken with its group and
the draws of its list; a link without a group or a list counts as missed. The entries taken of a
link's mask row: one for each scalar that its sub-proof's own plan sends, and the pad. On the
difference 2 k + 1 - h see `missedInTest`: the first chain's plan has folded every link's group. -/
def missedInLinksFrom (z : ProofSized) (sub : Subproofs) (answers : Nat) :
    Nat → List ReqLink → List ReqGroup → List Nat → Except String Bool
  | i, x :: xs, g :: gs, t :: ts => do
    let main := codeAt z.codes.base z.request.code
    let mask := codeAt z.codes.mask z.request.maskCode
    let moments := (x.messages.getLast?.map (·.moment + 1)).getD 0
    let entries ← scalarsOf z.set (forEach (List.range moments) fun m => sub.plan i m)
    if main.r < t || mask.r < t || mask.ell < 2 * g.k + 1 - g.h || mask.ell < entries + answers then
      pure true
    else missedInLinksFrom z sub answers (i + 1) xs gs ts
  | _, [], _, _ => pure false
  | _, _ :: _, _, _ => pure true

/-- The part on a request's links: the salt; that what rides at the start shares no class of leaves
with an oracle message of a link; the rows, mask rows and mask room of every link; the last test.
`first` is the plan of the first chain. True if a condition is missed. -/
def missedInTheLinks (l : Lines) (z : ProofSized) (sub : Subproofs) (first : Planned) :
    Except String Bool := do
  let lists := listsOf first
  let links := z.request.link
  let shares := z.request.atStart.any fun n =>
    links.any fun x => x.messages.any fun m => m.leafClass == n.leafClass
  if l.salt < 40 || shares || lists.length != links.length + z.request.last.length then pure true
  else if ← missedInLinksFrom z sub l.answers 0 links (reqGroups z.request).toList lists then
    pure true
  else pure (missedInTest z.codes z.request.last (lists.drop links.length) 0 0)

/-- The part on the range checks: all of one request's, times the requests that a key can serve: a
batch's, times a stored copy's batches, times the stored copies. A further copy is tied to the first
table by a link, which opens `columnsFirst` columns of the first table, so that table's random
entries bound the copies. Each factor is rounded up to a power of two by itself. `oneTime`: the
columns of the key's test on the table. True if the condition is missed, no check is named, or
`rangeCheckBits` gives nothing for one. -/
def missedInTheChecks (l : Lines) (checks : List RangeCheck) (oneTime columnsFirst batches : Nat) :
    Bool :=
  match allOf (checks.map rangeCheckBits) with
  | none => true
  | some bits =>
    let least := bits.foldl min (2 ^ 30)
    let copies := 1 + (l.tableRandom - min l.tableRandom oneTime) / max 1 columnsFirst
    checks.isEmpty ||
      least - (clog2 checks.length : Int) - (clog2 l.slots : Int) - (clog2 (max 1 batches) : Int) -
        (clog2 copies : Int) < (l.sec : Int)

end OnBytes.Params
