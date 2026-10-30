-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyStages.lean: the three stages of a call: key, leaf and request.

A stage of the C++ verifier is one run of runStage (verifier/src/cp_verify.cpp). All three begin
alike: the public part (OnBytes/Model/VerifyPublic.lean), the plans of the seven chains
(OnBytes/Model/VerifyChains.lean), the public tests on the links of a request's chain (`builtOf`),
and the commitment's ID, which is compared with the caller's (`commonOf`). Then the stage key
checks the key file, the stage leaf checks the entry file against the key's table, and the stage
request checks the proof file against the entry's table. The stages leaf and request test only the
form of the table that they rely on. What that table's own file proves about it is tested by another
stage on the same bytes, and the call passes only if all stages pass.

The common beginning is a function of the same bytes in all three stages. So the caller
(OnBytes/Model/Verify.lean) computes it once and passes it to each stage as a `Common`.

The standard parameter form is a list of conditions, most of them on the public inputs alone. A call
that misses one ends at best as not a verification (`Served`, OnBytes/Model/Stages.lean). The
weight table is the committed matrix of weights as a key file stores it.

Main definitions: `builtOf`, `Common`, `refusalName`, `Refused`, `commonOf`, `servedOf`,
`Common.oneTimeOut`, `keyStage`, `leafStage`, `Chains.twoCodes`, `Public.recordOneAnswer`,
`requestRun`, `Common.policyLines`, `subProofNames`, `proofRefusalName`, `requestStage`, and
`namesStages`, the list of the names with which this file refuses, for a program that prints no name
outside such a list.
What is not claimed: no theorem is stated here. Three limits:
 - This program reads all three chains of a proof file before it decides on any. The C++ verifier
   reads and decides step by step. So a proof file with a fault that the reader finds is refused as
   proof-refused here, also where the C++ verifier has met a sub-proof's own test first and ends
   with that test's name. If that name marks a fault of the program, the exit codes differ too: not
   checked there, a no here. Where the C++ verifier puts the sub-proof's name and a colon before a
   test's name, the layers' checks keep that prefix and the other sub-proofs' checks leave it out.
   Where it appends a further word to a test's name (a matrix, a table, an array, a segment, a
   lookup call, a field's label), the name here ends before that word.
 - The stage request covers the parameter files whose statement OnBytes/Proof/RequestItem.lean can
   form: profile 4 with routed experts and with the lines of the tables' digests. On another file
   it ends with an internal name, where the C++ verifier goes on and ends at best as not a
   verification.
 - The C++ checkers of the three files report whether their yes needs proof of work, and a stage
   compares that report with its accounting. They take it from an accounting of the file's plan
   that was stored when the plans were made. The checkers here give no such report. What a stage
   compares with its accounting is the planner's answer on the same plans (`Params.needsWork`),
   which is computed by other code than the accounting.
-/
import OnBytes.Model.VerifyChains
import OnBytes.Model.VerifyAccount
import OnBytes.Model.VerifyStatement
import OnBytes.Key.File
import OnBytes.Entry.File
import OnBytes.Proof.File
import OnBytes.Proof.RequestItem

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-! ## What all stages have in common -/

/-- What every stage has computed when it turns to its own file. -/
structure Common where
  /-- the public part -/
  X : Public
  /-- the seven chains: sizes, plans and parameter bytes -/
  chains : Chains
  /-- the links as `buildLinksH` returns them: each with the names of the arrays that it reads. The
  check in each was made without a request and is never run: `requestRun` puts the check that knows
  the request in its place -/
  built : LinksH
  /-- the key's table, read for its form alone -/
  first : Params.TableName
  /-- the commitment's ID, in lower-case hex digits -/
  idHex : String

/-- The shape of the stored tables, from the parameter bytes of the key's one-time chain. -/
def Chains.tableShape (c : Chains) : Params.IndexShape := c.key.oneTime.lin.fold.index

/-- The public tests on the links of a request's chain, under the first chain's parameter bytes as
read back. The check in each link that it returns was made without a request and is not to be
run. -/
def builtOf (X : Public) (chains : Chains) : Except String LinksH := do
  buildLinksH (← linksOf X default) X.NGr X.p4 X.layers.wsLay chains.proof.first

/-- The name with which a stage refuses when the checker of a file has refused. file: the name for
a fault of the file. internal: the name for a fault of the program. The internal name is used if the
checker refused what it was given as public input: a refusal in the part `configuration`, or with a
name that ends in -parameters. For instance the parameter bytes are not those of its kind of file,
the numbers in the parameter bytes of a key's three chains do not fit together, or the rounds that
its blocks state are not the rounds of the plan. This program makes that input itself from the
configuration files, so such a refusal is taken as its own fault and not as a verdict on a file. By
the blocks' design (blocks/frame/configure.h; cp_verify reads nothing of them before configure())
these tests depend on the content of no key, entry, request, reply or proof. This is not proved
here. If a file could cause such a refusal, the call would end as not checked where the C++ verifier
says no. -/
def refusalName (r : Refusal) (file internal : String) : String :=
  if r.stage == .configuration || r.check.endsWith "-parameters" then internal else file

/-- How a stage refuses. -/
structure Refused where
  /-- the name of the refusal -/
  name : String
  /-- if the checker of a file has refused: the name of the checker's own test that failed. The C++
  verifier has a sentence in this place -/
  why : Option String := none

/-- Turns a refusal that is only a name into a `Refused` without a why. -/
def named {α : Type} (x : Except String α) : Except Refused α :=
  x.mapError fun name => { name := name }

/-- The refusal of a stage whose file's checker has refused. The arguments are those of
`refusalName`. -/
def checkerRefused {α : Type} (r : Refusal) (file internal : String) : Except Refused α :=
  throw { name := refusalName r file internal, why := some r.check }

/-- The steps that all stages share after the plans are made. cfg: the digest of the
configuration files. key: the key file. asked: the ID that the caller named, or the empty string.

The ID is formed from the digest of the caller's configuration files and from the first bytes of the
key file. A stage compares it with the caller's before it looks at anything else of key, entry,
request or proof. It needs the table's shape, so it cannot come before the plans. -/
def commonOf (X : Public) (cfg : ByteArray) (chains : Chains) (built : LinksH) (key : ByteArray)
    (asked : String) : Except Refused Common := do
  let first ←
    match Key.readTable chains.tableShape cfg key with
    | .ok x => pure x.1
    | .error e => checkerRefused e "key-refused" "internal-key-parameters"
  let idHex := Fmt.hex (Key.commitmentId chains.tableShape cfg first)
  named (refuseIf (!asked.isEmpty && asked != idHex) "model-statement")
  pure { X := X, chains := chains, built := built, first := first, idHex := idHex }

/-- What a stage finds if no test fails: how it ends, its record of the accounting if it passes one
on, and its note on work. -/
abbrev Found : Type := StageEnd × Option Acct × Option WorkNote

/-- A stage's findings in the form in which the call takes them. -/
def stageOut (name : StageName) (idHex : String) : Except Refused Found → StageOut
  | .error x => { name := name, ending := .no x.name, idHex := idHex, why := x.why }
  | .ok (ending, acct, work) =>
    { name := name, ending := ending, idHex := idHex, acct := acct, work := work }

/-- The findings of the stage key or leaf in the form in which the call takes them. Such a stage
says that the table has a record. It says so right
after its accounting, before it looks at its file. Here only a stage that did not refuse says it: a
call in which a stage refused prints none of the lines that show it. Nor does a call on one file
alone, whatever its end. C++: oneTimeLineH, called in acctOfH. -/
def Common.oneTimeOut (C : Common) (name : StageName) (x : Except Refused Found) : StageOut :=
  { stageOut name C.idHex x with oneTimeLine := x.toOption.isSome }

/-! ## The stages key and leaf -/

/-- True if the test on the weight table runs with its split step, in a batch's proof and in the
key: two of its oracle messages, the folded row and Omega, have different codes
(LinShape.sharedSplitNeeded in OnBytes/Iop/Lin.lean). The two shapes are those that the checks of a
proof and of a key use, as read back from the parameter bytes. A condition of the standard parameter
form, which all three stages test. -/
def Chains.twoCodes (c : Chains) : Bool :=
  c.proof.first.lin.sharedSplitNeeded && c.key.oneTime.lin.sharedSplitNeeded

/-- True if every out-of-domain sample has one answer (the line answers is 1). A condition of the
standard parameter form, which all three stages test. -/
def Public.recordOneAnswer (X : Public) : Bool :=
  X.P.frame.answers == 1

/-- Of the conditions of the standard parameter form that the stages key and leaf test, those that
are missed. These stages test the conditions on how the errors of their file's rounds are counted,
and the two on the form of the table and of the test on it. -/
def Common.oneTimeForm (C : Common) : List String :=
  (if C.X.P.frame.reading == 1 then [] else [servedReading]) ++
    (if C.chains.twoCodes then [] else [servedTwoCodes]) ++
    (if C.X.recordOneAnswer then [] else [servedRecordAnswer])

/-- The accounting of one file's plan, compared with the bits that the call asks for. plans: the
plans of the file's chains. object: the stage's name. The
target is that of the setting under which the plans were made, not a second reading of the line sec.
-/
def Common.acct (C : Common) (plans : List Params.Planned) (asked : Nat) (object : String) :
    Except String FileAcct :=
  acctOfH C.chains.made.sized.set (some plans) asked object

/-- The stage key: the accounting of the key's plan, then the check of the key file. -/
def keyStage (C : Common) (asked : Nat) (key : ByteArray) : Except Refused Found := do
  let a ← named (C.acct C.chains.made.key asked "key")
  match Key.check C.chains.key key with
  | .error e => checkerRefused e "key-refused" "internal-key-parameters"
  | .ok _ =>
    named (workHeldH (Params.needsWork C.chains.made.key) a.work)
    pure (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
      lidbSealed 0, some a.acct, a.work)

/-- The stage leaf: the accounting of the entry's plan, then the check of the entry file against
the key's table. -/
def leafStage (C : Common) (asked : Nat) (entry : ByteArray) : Except Refused Found := do
  let a ← named (C.acct [C.chains.made.entry] asked "leaf")
  match Entry.check C.chains.made.entryLink C.first entry with
  | .error e => checkerRefused e "entry-refused" "internal-entry-parameters"
  | .ok _ =>
    named (workHeldH (Params.needsWork [C.chains.made.entry]) a.work)
    pure (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
      lidbSealed 0, some a.acct, a.work)

/-! ## The stage request -/

/-- The table of an entry file, read for its form alone: the header, the root and the answers of the
record, and that the table has an allowed form. p: the parameter bytes of the entry's chain, as
read back. C++: read_entry_table_unproved. -/
def entryTable (p : Params.Link) (file : ByteArray) : Except String Params.TableName :=
  let f := p.given.plan.field
  let s := p.link.table
  match Proof.readHead f .entry file with
  | .error _ => throw "entry-refused"
  | .ok i =>
    match OnBytes.readTable f (s.rows * s.answers) file i with
    | .error _ => throw "entry-refused"
    | .ok x => if Key.tableOk s p.given.cfg x.1 then pure x.1 else throw "entry-refused"

/-- True if all layers of a group have the same attention shift, or if the profile is not 4. -/
def oneShift (X : Public) : Bool :=
  !X.p4 || (List.range X.P.h.L).all fun l =>
    X.layers.sc.klSh l == X.layers.sc.klSh (l - l % X.y.Lam)

/-- True if no norm shifts right by more bits (K) than its reciprocal is scaled by (M). From K = M +
3 on a norm's output is 0 for every input. The condition rules that out; with a small M - K the
output still has only a few bits. -/
def normShifts (X : Public) : Bool :=
  let sc := X.layers.sc
  decide (X.P.h.KF ≤ X.P.h.MF) && (List.range X.P.h.L).all fun l =>
    decide (sc.kl l Layer.LK1 ≤ sc.kl l Layer.LM1) &&
      decide (sc.kl l Layer.LK2 ≤ sc.kl l Layer.LM2)

/-- The values of the conditions of the standard parameter form for a call. hasLayout: the
configuration folder holds a layout file. so, cov: the request. Below profile 4 the conditions
three-bytes, one-shift, softmax-table and rotary-table count as met (three-bytes because the line S
is then missing and reads as 0). Two conditions cannot fail here: toksrc other than 1 and S of 32 or
more are refused earlier. They stay so that the list is the C++ verifier's. Four more never show in
a result of this program: without a layout file the plans are refused, and below profile 4, without
routed experts or without the tables' digests `requestRun` ends with internal-request-item. The
conditions softmax-table and rotary-table allow the parameter values at which every entry of the C++
tables, which are computed in floating point, is far from a rounding tie. -/
def servedOf (C : Common) (o : Options) (hasLayout : Bool) (so : Head.StOwn) (cov : Head.Covered) :
    Served :=
  let X := C.X
  let P := X.P
  let h := P.h
  { attention := X.p4
    experts := decide (0 < h.NE)
    fiveLimbs := P.XL == 5
    clamps := P.rcl && P.gcl
    promptSource := h.toksrc == 1
    placementTable := hasLayout
    tableDigests := P.tblPol.size == 32
    noRangeWords := P.eg.isNone && P.smax.isNone
    threeBytes := decide (h.Sx < 32)
    ringDegree := h.D == 2048
    oneShift := oneShift X
    onePlacement := onePlacement C.built.links C.chains.proof.first.layout
    softmaxTable := !X.p4 || (h.Sx == 12 && h.rx == 8)
    rotaryTable := !X.p4 || rotaryServed h.theta0 h.dh h.lt
    normShifts := normShifts X
    readingAsPrinted := P.frame.reading == 1
    twoCodes := C.chains.twoCodes
    recordOneAnswer := C.X.recordOneAnswer
    nextToken := !o.nextToken || (so.r + 1 == X.T && so.e == X.T)
    exactMatch := o.policy.isSome || cov.hRC == 0 ||
      exactMatch h.clipC h.theta h.cap h.digSh h.tabS
    policyNamed := o.policy.all fun p => p.is h.clipC h.theta h.cap h.logS h.digSh h.tabS }

/-- The 32-bit words of a file, as UInt32. -/
def words32 (b : ByteArray) : Array UInt32 := (fileWords b).map (·.toUInt32)

/-- What the stage request has found when the proof file has been read through. -/
structure RequestRun where
  /-- the verdict on the proof file -/
  verdict : Verdict
  /-- the conditions of the standard parameter form that are missed -/
  form : List String
  /-- the record of the accounting of all three files' plans. There is none unless every round of
  them meets the target; without it a call in which no stage says no ends as not checked -/
  whole : Option Acct
  /-- the note on work of the proof's plan -/
  work : Option WorkNote

/-- The stage request up to the verdict on the proof file. r: the files of the call. entry: the
entry file. The order is that of runStage: the request's form; the entry's table, for its form
alone; the accounting of the proof's plan; the conditions of the standard parameter form; the proof
file. Two steps before the proof file are this program's own: the statement that the first chain
binds is formed from the files' bytes, and it is compared with what the sub-proofs use. -/
def requestRun (C : Common) (o : Options) (r : Read) (entry : ByteArray) :
    Except String RequestRun := do
  let X := C.X
  refuseIf (r.request.size % 4 != 0 || r.y.size % 4 != 0) "statement-required"
  let so ← Head.stFromCall (words32 r.request) (words32 r.y) X.T
  let cov ← Head.coveredOf so X.T X.P.h.V
  let made := C.chains.made
  let further ← entryTable C.chains.link entry
  let a ← C.acct made.proof o.bits "request"
  let whole := acctWhole made.sized.set (some (made.key ++ [made.entry] ++ made.proof))
  let form := servedForm (servedOf C o r.layout.isSome so cov)
  let item ←
    match Proof.requestItem r.pol r.KL r.request with
    | some w => pure w
    | none => throw "internal-request-item"
  statementHeld X item
  -- the links as built, each with the check that knows the request
  let links := C.built.links.zipWith (fun b l => { b with run := l.run }) (← linksOf X cov)
  -- one value holds the first chain's shape, layout and codes: the one whose bytes are hashed
  let c := C.chains.proof
  pure { verdict := Proof.check c further r.entry item r.request (ofNat so.y)
           (runLinksH links c.first X.layers.wsLay) r.proof,
         form := form, whole := whole, work := a.work }

/-- The lines of the acceptance policy under which the stage request judges. -/
def Common.policyLines (C : Common) : PolicyLines :=
  let h := C.X.P.h
  { C := h.clipC, theta := h.theta, cap := h.cap, s := h.logS, sh := h.digSh, sT := h.tabS,
    F := h.famF }

/-- The name of the checker's refusal that says: the proof is about another reply. -/
def replyRefusal : String := "first-chain-decision-reply"

/-- The names with which the checks of the sub-proofs and of the links refuse on a proof's first
chain, from the lists of their modules. They are meant to be the C++ verifier's names for the same
tests; a few belong to guards that only this program has (internal-h-covered is one). Where that
verifier appends a further word to a name (the name of a matrix, a table, an array, a segment or a
lookup call, or a field's label), the name here ends before it. The comment at each module's list
says to which names. -/
def subProofNames : List String :=
  linksNames ++ Rounds.names ++ tensorsNames ++ lookNames ++ Forest.names ++ Trees.names ++
    Tail.names ++ Attention.names ++ Head.names ++ Layer.names ++ Weights.names ++ Merge.names ++
    Pending.names

/-- The name with which the stage request refuses when the check of the proof file has refused. A
proof about another reply than the caller's has a name of its own. If a test of a sub-proof or of a
link has failed under its own name, that is the refusal's name, as in the C++ verifier, where such
a test ends the stage. A test on public numbers (`mustAs`) fails already in the dry run by which
the reader of the proof file learns the chain's rounds (`Blk.dryRun`, OnBytes/Iop/Ground.lean). That
run keeps no name: the stage then refuses as internal-proof-parameters. A name outside
`subProofNames` is not passed on. -/
def proofRefusalName (e : Refusal) : String :=
  if e.check == replyRefusal then "reply-differs"
  else if subProofNames.contains e.check then e.check
  else refusalName e "proof-refused" "internal-proof-parameters"

/-- The stage request: `requestRun`, and the stage's end from the verdict on the proof file. -/
def requestStage (C : Common) (o : Options) (r : Read) (entry : ByteArray) :
    Except Refused Found := do
  let x ← named (requestRun C o r entry)
  match x.verdict with
  | .refused e => throw { name := proofRefusalName e, why := some e.check }
  | .accepted =>
    named (workHeldH (Params.needsWork C.chains.made.proof) x.work)
    let set := C.X.P.settings
    pure (lastLine (!C.X.p4) (askedBelowBar o.bits) x.form set.lidb set.nminH, x.whole, x.work)

/-- The names with which this file itself refuses. -/
def namesStages : List String :=
  ["key-refused", "model-statement", "entry-refused", "statement-required",
   "internal-request-item", "proof-refused", "reply-differs", "internal-key-parameters",
   "internal-entry-parameters", "internal-proof-parameters"]

end OnBytes.Model.Verify
