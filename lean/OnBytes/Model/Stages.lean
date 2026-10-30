-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Stages.lean: how a stage ends, and how the stages' results make the result of a call.

A whole call of the C++ verifier cp_verify runs three stages on the same bytes. The stage key checks
the key file. The stage leaf checks the entry file against the key's table. The stage request checks
the proof file against the entry's table. No stage takes anything from another. (Here the part that
all three stages begin with is computed once and passed to each: OnBytes/Model/Verify.lean.) This
file holds the rules by which a stage's findings become its result, and the three results become the
last line and the exit code of the call. Where a definition mirrors a C++ routine it has that
routine's name (verifier/src/cp_verify.cpp, verifier/src/vf_common.h).

The C++ program runs each stage in a process of its own and reads its result as text. Here a
stage's result is a value, so the C++ tests that a stage's exit code and printed lines fit one
another have no counterpart.

A result is a value with typed fields. The program makes its printed lines from these fields in
OnBytes/Shell/Lines.lean (verdict, Line.text), and takes the exit code from `CallEnd.status`.
`CallEnd.lastLine` gives cp_verify's last line for the same result. Only tests use it:
OnBytes/Shell/TestWhole.lean compares it with the program's line on examples of nine of the eleven
endings.

Words. Key file, entry file, proof file, chain, round, target, proof of work, record:
lean/GLOSSARY.md. The parameter file is policy.txt. Its lines reading, answers and record
are read in OnBytes/Params/File.lean; prof, D, S and the policy's lines C to F in
OnBytes/Model/Config.lean. The docstring of `Served` says where the lines are described.

Main definitions: `endNames`, `StageName`, `WorkNote`, `StageEnd`, `Acct`, `StageOut`, `Served`,
`servedForm`, `goodEnding`, `lastLine`, `internalName`, `Covered`, `cpCovered`, `Closing`,
`CallEnd`, `CpId`, `passedWithWork`, `recordNeedsWork`, `cpStagesRun`.
What is not claimed: no theorem is stated here, and nothing is said about the stages themselves,
which are in other files. Theorems in other files state what follows of definitions of this file.
They are on this Lean program alone, not on cp_verify. The next three paragraphs also say what they
leave open.

The option -no-proof-of-work (OnBytes/Model/VerifyLawsOption.lean). `cpStagesRun_option`: if the
result of `cpStagesRun` is a yes, within limits or a passed part and `id.noProofOfWork` is set, then
`passedWithWork` and `recordNeedsWork` are false of the stages' results: no stage passed with a note
on work, and the call's record does not say that a round needs its work. That record is the record
of an accounting (`Acct`), not the record of GLOSSARY.md. `wholeCall_option` and `partCall_option`
conclude the same of the results of the stages that `wholeCall` and `partCall`
(OnBytes/Model/Verify.lean) run, with the option in the options as read. The first speaks of a call
that ends with one of these three results, and supposes that `entryNumber` returns a number on the
files without the entry. The second speaks of a call that ends as a passed part. None of them says
that the stages' notes and records are right: the notes and the record's word on work are made in
OnBytes/Model/VerifyAccount.lean, which states no theorem. None says with which other result a call
with the option ends where work is needed: that rests on rules 5 and 6 of `cpStagesRun` as they are
written and on the examples that OnBytes/Model/TestStages.lean evaluates, in which the stages'
results are written by hand. On work, none says anything of a call without the option.

The option's way in. `readFirst_option` and `readCall_option` (OnBytes/Model/VerifyLawsOption.lean):
in what `readFirst` and `readCall` (OnBytes/Model/VerifyHeads.lean) return, `id.noProofOfWork` is
the field of the options that they were given. OnBytes/Shell/AtOption.lean starts from the arguments
of the program's entry function. For a call on one file alone: the field is set if the options are
read without a refusal and the string -no-proof-of-work is among them (`partOptions_noWork`), and
`main_key_option` and `main_leaf_option` lead from the arguments of such a call that returns 3, with
the string among its options, to what `partCall_option` concludes. For a whole call that is not
proved from the command line: `main_zero_option`, which leads from the arguments of a call that
returns 0, with the string among its options, to what `wholeCall_option` concludes, supposes a fact
on that one string, which speaks of no file. The fact is tested, by a #guard behind the theorem, and
not proved: `policyNamedRead` (OnBytes/Model/Config.lean) refuses the string, that is,
policyNamedRead "-no-proof-of-work" = none. Without it the string could be the value of -policy
(`readOptions_noWork`). The converse, that the field is set only if the string is among the options,
is not stated.

A named policy. `cpStagesRun_within` and `wholeCall_within` (OnBytes/Model/VerifyLawsOption.lean):
if the result of `cpStagesRun` is within limits, `id.policyGiven` is set; if `entryNumber` returns a
number on the files without the entry and `wholeCall` on the same files with the entry ends as
within limits, the options as read hold a policy. By its head, OnBytes/Shell/AtOption.lean does not
lead from the arguments to a named policy. As the definitions are written, three tests, one after
the other, each end a call that names no policy and covers a token of the request under a policy
other than the exact match: `cpPolicyHeld` (OnBytes/Model/VerifyHeads.lean) with a no, before any
stage (its docstring and `readCall`'s say where the test is left out); the stage request's condition
exact-match (`servedOf`, OnBytes/Model/VerifyStages.lean; `servedForm`, `lastLine` and rule 6 here)
as not a verification; rule 9 of `cpStagesRun` as not checked. The two theorems speak of neither of
the first two tests.






-/
import OnBytes.Model.Config

namespace OnBytes.Model.Stages

/-- The names that this file itself writes: those with which it ends a stage or a call, and the
two, policy and model-statement, that are printed for an ending that has no name of its own. -/
def endNames : List String :=
  ["internal-last-line", "internal-sums-line", "internal-stage", "internal-covered-line",
   "internal-id-two-ways", "internal-policy-not-given", "internal-policy-kind", "policy",
   "model-statement"]

/-! ## Constants of the call -/

/-- Half the bits of a digest: by the usual convention a digest of 256 bits counts as 128. A call
that asks for more bits is refused. The comment at DIGEST_HALF_BITS in verifier/src/vf_common.h
points to a stricter count for a collision search, which no test uses. C++: DIGEST_HALF_BITS. -/
def hashLeast : Nat := 128

/-- The number of hex digits of a printed digest. C++: HEXW. -/
def hexW : Nat := 64

/-! ## The result of a stage -/

/-- The three stages of a call. -/
inductive StageName where
  /-- checks the key file -/
  | key
  /-- checks the entry file, leaf/<k>.bin. The stage keeps the C++ verifier's name; its pages call
  this file the leaf file -/
  | leaf
  /-- checks the proof file -/
  | request
  deriving DecidableEq, Repr, Inhabited

/-- A stage's name as it is printed. -/
def StageName.text : StageName → String
  | .key => "key"
  | .leaf => "leaf"
  | .request => "request"

/-- The note on a file whose rounds reach the security target only with their work credited. It
names the round with the largest error when work is left out. The bits are made for a printed line:
whether a round meets the target is decided elsewhere (OnBytes/Model/VerifyAccount.lean). -/
structure WorkNote where
  /-- that error in hundredths of a bit, rounded down -/
  centibits : Nat
  /-- the round's bits of work -/
  work : Nat
  /-- the file and the kind of round -/
  place : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- A number of hundredths with two decimals, as in "96.02". -/
def hundredths (n : Nat) : String :=
  toString (n / 100) ++ "." ++ toString (n % 100 / 10) ++ toString (n % 10)

/-- How a stage ends. -/
inductive StageEnd where
  /-- a test failed; the name of the test -/
  | no (name : String)
  /-- no test failed, but the run is not a verification; the causes, each by a short name -/
  | notVer (causes : List String)
  /-- every test passed and no cause applies -/
  | passed
  deriving DecidableEq, Repr, Inhabited

/-- The accounting of a plan's rounds, as far as the results depend on it. An error of 2^-b is given
as b bits, so the round with the largest error has the fewest bits. -/
structure Acct where
  /-- the security target, in bits, against which the rounds' errors were measured -/
  target : Nat
  /-- true if at least one round falls short of the target unless its bits of work are credited -/
  needsWork : Bool
  /-- of the round with the largest error when work is left out: that error in hundredths of a
  bit, rounded down -/
  centibits : Nat := 0
  /-- that round's bits of work -/
  work : Nat := 0
  /-- how many rounds need their bits of work credited to reach the target -/
  byWork : Nat := 0
  /-- the most bits of work that the parameter file declares for any kind of round -/
  mostWork : Nat := 0
  /-- the largest error of a round with the declared work counted, in hundredths of a bit, rounded
  down -/
  leastRound : Nat := 0
  /-- the number of rounds whose closeness term rests on a source other than the first of two. A
  closeness term (GLOSSARY.md: proximity term) is the part of a round's error that comes from
  testing that committed rows are close to codewords: the chance that a random combination of rows
  is close to the code though the rows are not jointly close (mutual correlated agreement). It is a
  count over the size of the extension field (if the line rowcost is 2, also times the number of
  rows, except at the first source). The count has one of two sources (`CountSource`,
  OnBytes/Params/Setting.lean; blocks/numbers/codes.h). Where the tested distance is below a third
  of the code's minimum distance: a lemma of the paper that this protocol builds on (see
  THIRD_PARTY.md), proved there, on paper. The lines of OnBytes/Shell/Lines.lean call it "the proved
  lemma". Beyond a third: IACR ePrint 2025/2055, Theorem 4.6, which is assumed. Nothing in
  OnBytes/Params/ proves that lemma or any other formula, and no theorem ties the planner's number
  to it -/
  closeOther : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- True if the call accepts the record. The C++ program passes a record on as text, and its reader
(acctReadH, vf_accounting_record.h) accepts one only if the record's two statements on work
agree: some round needs its work exactly if the number of such rounds is not 0. It also requires a
target of at most 512 bits and at most 64 bits of work. -/
def Acct.taken (a : Acct) : Bool :=
  (a.byWork != 0) == a.needsWork && decide (a.target ≤ 512) && decide (a.mostWork ≤ 64)

/-- What a stage passes to the call. -/
structure StageOut where
  /-- which stage it is -/
  name : StageName
  /-- how it ended -/
  ending : StageEnd
  /-- the commitment's ID as the stage formed it, in lower-case hex digits; empty if the stage
  ended before -/
  idHex : String := ""
  /-- the stage's record of its accounting. A stage that refused has none, unless it refused with
  internal-last-line (in cp_verify such a stage has none either; both calls end as not checked). The
  stage request passes on the accounting of all three files' plans, and has none if a round of these
  plans does not meet the target -/
  acct : Option Acct := none
  /-- the stage's note on work, if its own file's plan needs work -/
  work : Option WorkNote := none
  /-- if the stage refused: the name that the checker of its file gave to the failed check, if it
  gave one -/
  why : Option String := none
  /-- the stage says that the committed table has a record. In cp_verify the stages key and leaf
  print a line that begins with `accounting: one-time files: ` once their accounting has held, if
  the parameter file has the line `record 1`, and the call looks for that line in their output -/
  oneTimeLine : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A stage's result as the call reads it: a record that is not accepted counts as none. -/
def StageOut.asRead (x : StageOut) : StageOut := { x with acct := x.acct.filter Acct.taken }

/-! ## The standard parameter form -/

/-- The conditions on the public inputs that a run must meet to pass (GLOSSARY.md: standard
conditions). Three of them also depend on an
option of the call. A run that misses one still makes every test, and ends at best as not a
verification. The comments below name lines of the parameter file, policy.txt: prof, D, S, reading,
record, answers and others. verifier/docs/parameter-file.md describes every line, and its section
"The standard parameter form" lists these conditions. -/
structure Served where
  /-- the whole model with attention: profile 4. The line prof is 16 plus the profile; profile 3 is
  the model without attention -/
  attention : Bool
  /-- the model has routed experts -/
  experts : Bool
  /-- a value of the residual stream has five limbs -/
  fiveLimbs : Bool
  /-- the lines rcl and gcl are there: the router's logits and the gate table's key are clamped -/
  clamps : Bool
  /-- the model's input is the embedding of the request file's tokens -/
  promptSource : Bool
  /-- the configuration folder holds a layout file -/
  placementTable : Bool
  /-- the parameter file has the lines with the digests of the four public tables -/
  tableDigests : Bool
  /-- neither of the two optional range lines of the gate table is there -/
  noRangeWords : Bool
  /-- three bytes for a remainder of the division in attention: the parameter line S is below
  32 -/
  threeBytes : Bool
  /-- the parameter line D is 2048: a unit's rows in the committed matrix of weights are rounded
  up to a multiple of D -/
  ringDegree : Bool
  /-- all layers of a group have the same attention shift -/
  oneShift : Bool
  /-- the arrays that later sub-proofs read are placed in the same way in all groups of layers -/
  onePlacement : Bool
  /-- the two parameters of the softmax table are S = 12 and rx = 8 -/
  softmaxTable : Bool
  /-- the parameters of the rotary table: theta0 is 10000 or 500000, dh at most 128, lt at most
  10 -/
  rotaryTable : Bool
  /-- no norm shifts right by more bits than its reciprocal is scaled by -/
  normShifts : Bool
  /-- the parameter line reading is 1: the integer m of the assumed theorem is read as that theorem
  prints it (`Setting.printed`, OnBytes/Params/Setting.lean). At 2 it is read the other way, which
  gives a smaller m and count and can give shorter lists of positions -/
  readingAsPrinted : Bool
  /-- two oracle messages of the test on the committed table, the folded row and Omega
  (OnBytes/Iop/Lin.lean), are encoded with two different codes, in a batch's test and in the
  key's -/
  twoCodes : Bool
  /-- every out-of-domain sample of the committed table has one answer (the line answers is 1).
  GLOSSARY.md: record; another thing than the record of an accounting, `Acct` -/
  recordOneAnswer : Bool
  /-- tested only under the option -next-token: the proof is about the reply alone -/
  nextToken : Bool
  /-- the acceptance policy is the exact match; not tested if no token of the request is covered,
  or under the option -policy -/
  exactMatch : Bool
  /-- tested only under the option -policy: the parameter file sets the policy that is named -/
  policyNamed : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The name of the condition on the parameter line reading. All three stages test it. The reason
for this condition and the next two: whoever writes the parameter file is not the one who relies
on a proof, so where a line lets the writer choose something laxer than a plain yes means, there is
a condition. Some lines are exceptions, as in cp_verify (vf_common.h): the line record 1,
under which the key and the entry rest on the assumed theorem (a whole
call's line `commitment: ...` shows it); the lines work, whose bits count toward the target (the
line on proof of work and the line for programs show the split); and the rule of a request's own
groups, which no condition reads. That these are all such lines is not shown. -/
def servedReading : String := "reading-as-printed"

/-- The name of the condition that the folded row and Omega have two different codes. All three
stages test it. -/
def servedTwoCodes : String := "two-codes"

/-- The name of the condition on a table with a sample of its own. All three stages test it. -/
def servedRecordAnswer : String := "record-one-answer"

/-- The names of the conditions that s does not meet, in their fixed order. -/
def servedForm (s : Served) : List String :=
  ([(s.attention, "attention"), (s.experts, "routed-experts"), (s.fiveLimbs, "five-limbs"),
    (s.clamps, "both-clamps"), (s.promptSource, "prompt-source"),
    (s.placementTable, "placement-table"), (s.tableDigests, "table-digests"),
    (s.noRangeWords, "no-range-words"), (s.threeBytes, "three-bytes"),
    (s.ringDegree, "ring-degree"), (s.oneShift, "one-shift"), (s.onePlacement, "one-placement"),
    (s.softmaxTable, "softmax-table"), (s.rotaryTable, "rotary-table"),
    (s.normShifts, "norm-shifts"), (s.readingAsPrinted, servedReading),
    (s.twoCodes, servedTwoCodes), (s.recordOneAnswer, servedRecordAnswer),
    (s.nextToken, "next-token"), (s.exactMatch, "exact-match"),
    (s.policyNamed, "policy-named")].filter fun c => !c.1).map (·.2)

/-- True if a run in which no test failed may end with a passing word. The C++ routine is also false
in every test build; this library has no test build. -/
def goodEnding (lowProfile belowBar notServed : Bool) : Bool :=
  !lowProfile && !belowBar && !notServed

/-- The result of a stage in which no test has failed. It has the name of the C++ routine, which
also prints; this one returns a value and no text. `lowProfile`: the parameter file's profile is
below 4. `belowBar`: fewer bits than the threshold were asked. `form`: the conditions of the
standard parameter form that are missed. Each of the three makes the run not a verification. `lidb`,
`nminH`: the values of these two parameter lines. The result does not depend on them, except that
outside their ranges the stage ends with internal-last-line. The standard parameter form does not
decide these two lines. The C++ verifier names them in a printed note, which has no counterpart
here. The stages key and leaf use neither and pass the defaults. -/
def lastLine (lowProfile belowBar : Bool) (form : List String) (lidb nminH : Nat) : StageEnd :=
  if lidb < lidbSealed || lidb > lidbMost || nminH > nminHMost then .no "internal-last-line"
  else if goodEnding lowProfile belowBar (!form.isEmpty) then .passed
  else .notVer ((if lowProfile then ["profile-below-4"] else []) ++
    (if belowBar then ["fewer-bits-requested"] else []) ++ form)

/-! ## The result of a call -/

/-- True for the name of a refusal that is meant for a fault of the program and not of a file: it
begins with "internal-", or has that word right after a prefix of letters and digits that ends in a
colon, such as a sub-proof's "G0:". That no file can reach such a name is not shown, and in the
C++ verifier at least eight of them can also be raised by a rare value of the challenges
(verifier/docs/output.md, "Exit codes"). -/
def internalName (name : String) : Bool :=
  let l := name.toList
  let rest := l.dropWhile Char.isAlphanum
  let tail :=
    match rest with
    | ':' :: t => if rest.length < l.length then t else l
    | _ => l
  tail.take 9 == "internal-".toList

/-! ### What a whole call's answer is about -/

/-- The two kinds of acceptance policy under which a whole call can pass. -/
inductive PolicyKind where
  /-- each checked token is the model's first choice at its position -/
  | exactMatch
  /-- the checked tokens' costs, each clipped at C, stay within the policy's limits -/
  | clippedGap
  deriving DecidableEq, Repr

/-- A kind of policy as it is printed. -/
def PolicyKind.text : PolicyKind → String
  | .exactMatch => "exact-match"
  | .clippedGap => "clipped-gap"

/-- The seven lines of the parameter file that set the acceptance policy, by their names there. What
a cost is and what the lines are meant to give: the head of OnBytes/Model/VerifyHeads.lean. -/
structure PolicyLines where
  /-- the clip on a position's cost -/
  C : Nat
  /-- the bound on the average cost -/
  theta : Nat
  /-- the most positions above the clip -/
  cap : Nat
  /-- the provider's statement of the scale of the model's logits; no test compares it with the
  model -/
  s : Nat
  /-- the least cost of a token is 2^sh -/
  sh : Nat
  /-- selects the table that the head looks up -/
  sT : Nat
  /-- that table's values are scaled by 2^F -/
  F : Nat
  deriving DecidableEq, Repr, Inhabited

/-- What a whole call's answer is about: the positions that the caller's request names, and the
policy of the caller's parameter file. -/
structure Covered where
  /-- the first covered position -/
  r : Nat
  /-- the position after the last covered one -/
  e : Nat
  /-- the number of positions -/
  T : Nat
  /-- the line C -/
  C : Nat
  /-- the line theta -/
  theta : Nat
  /-- the line cap -/
  cap : Nat
  /-- the line s -/
  s : Nat
  /-- the line sh -/
  sh : Nat
  /-- the line sT, which is sh - 4 under both kinds of policy -/
  sT : Nat
  /-- the line F -/
  F : Nat
  /-- how many of the request's checked tokens may cost more than C (`aboveClip`) -/
  aboveClip : Nat
  /-- the kind of policy that the parameter file's lines set -/
  policy : PolicyKind
  deriving DecidableEq, Repr

/-- The tokens of the request itself that are checked, from the first to the last, counted from 0.
Nothing if the reply's token alone is checked. -/
def Covered.tokens (a : Covered) : Option (Nat × Nat) :=
  let last := min a.e (a.T - 1)
  if a.r + 1 ≤ last then some (a.r + 1, last) else none

/-- True if the answer is about the reply's token too. -/
def Covered.y (a : Covered) : Bool := a.e == a.T

/-- True if the answer is about the reply's token alone. -/
def Covered.nextToken (a : Covered) : Bool := a.r + 1 == a.T

/-- True if a token of the request itself is checked under a policy other than the exact match. -/
def Covered.otherKind (a : Covered) : Bool := a.tokens.isSome && a.policy != .exactMatch

/-- What a passing answer says. -/
inductive Claim where
  /-- the reply's token is the model's first choice; no other token is checked -/
  | nextToken
  /-- every checked token is the model's first choice -/
  | exactMatch
  /-- the request's checked tokens stay within the limits of the policy -/
  | policy
  deriving DecidableEq, Repr

/-- What a passing answer about these positions under this policy says. -/
def Covered.claim (a : Covered) : Claim :=
  if a.nextToken then .nextToken else if a.otherKind then .policy else .exactMatch

/-- What a whole call's answer is about. request: the words of the request file: T tokens, then r
and e. p: the policy's numbers under which the stage request has judged. Refused with
internal-covered-line unless there are at least three words and r < e ≤ T; a request stage that has
not refused has made the same test (statement-range). Refused with internal-policy-kind unless sT =
sh - 4: other values set neither of the two kinds of policy. In C++ cpCovered does not refuse there:
it marks its result, and its caller tests the mark later (see `cpStagesRun`). It also parses the
numbers out of the request stage's printed text and fails if one is not a number. Here they are
values, so that test has no counterpart. -/
def cpCovered (request : Array UInt32) (p : PolicyLines) : Except String Covered := do
  let T := request.size - 2
  let r := (request.getD T 0).toNat
  let e := (request.getD (T + 1) 0).toNat
  refuseIf (!(decide (3 ≤ request.size) && decide (r < e) && decide (e ≤ T)))
    "internal-covered-line"
  refuseIf (p.sT + 4 != p.sh) "internal-policy-kind"
  pure { r := r, e := e, T := T, C := p.C, theta := p.theta, cap := p.cap, s := p.s, sh := p.sh
         sT := p.sT, F := p.F, aboveClip := aboveClip (min e (T - 1) - r) p.C p.theta p.cap p.sh
         policy := if exactMatch p.C p.theta p.cap p.sh p.sT then .exactMatch else .clippedGap }

/-! ### The endings -/

/-- How much proof of work a call has counted. -/
structure WorkCount where
  /-- the most bits of work that the parameter file declares for any kind of round -/
  bits : Nat
  /-- the number of rounds that meet the target only with their work -/
  rounds : Nat
  /-- the largest error of a round with the declared work counted, in hundredths of a bit, rounded
  down -/
  withWork : Nat
  deriving DecidableEq, Repr

/-- What a call that has reached its end says besides its verdict. -/
structure Closing where
  /-- the commitment's ID, in lower-case hex digits. Nothing if it is not to be shown: a call that
  needs a named ID and has none does not show the files' own. cp_verify prints the ID among its
  closing lines only in a whole call -/
  idHex : Option String
  /-- the caller has named the ID, and it is equal -/
  idNamed : Bool
  /-- the digest of the parameter files, in lower-case hex digits -/
  hPar : String
  /-- the stages' notes on work, as far as they have 1 to 32 bits of work -/
  stageWork : List (StageName × WorkNote)
  /-- the work that was counted. Nothing if no round needs its work -/
  work : Option WorkCount
  /-- the largest error of a round with the declared work counted, in hundredths of a bit, rounded
  down -/
  leastRound : Nat
  /-- the largest error of a round with work left out, in hundredths of a bit, rounded down -/
  leastWithoutWork : Nat
  /-- in a whole call: the number of rounds of the key's and the entry's plans whose closeness term
  rests on a source other than the lemma within a third of the code's distance (`Acct.closeOther`).
  In a call on one file alone: 0 -/
  oneTimeAssumed : Nat
  /-- a stage has said that the committed table has a record (`StageOut.oneTimeLine`) -/
  tableRecord : Bool := false
  deriving DecidableEq, Repr

/-- Why a call is refused for its policy, before any stage. -/
inductive PolicyWhy where
  /-- the parameter file sets a kind of policy that a whole call does not take. logProbability:
  true if the kind is log-probability, false if it is another-table (policyKind,
  OnBytes/Model/Config.lean) -/
  | fileKind (logProbability : Bool)
  /-- the caller names a kind or numbers other than those that the parameter file sets -/
  | differs
  /-- a token of the request itself is covered, the file's policy is not the exact match, and the
  caller names no policy -/
  | notNamed
  /-- the named C is below 2^sh, the least cost of a token -/
  | clipBelowLeast
  /-- the named theta is below 2^sh -/
  | meanBelowLeast
  /-- the named theta is above C -/
  | meanAboveClip
  /-- theta = C and cap is not below the number of the request's checked tokens, so the policy
  rules out none of them. place: the r of a request for the reply's token alone -/
  | noneBarred (place : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The input files of a call. -/
inductive Role where
  /-- the parameter file -/
  | policy
  /-- the scale file -/
  | KL
  /-- the layout file -/
  | layout
  /-- the key file -/
  | key
  /-- the entry file -/
  | entry
  /-- the request file -/
  | request
  /-- the file with the reply's token -/
  | y
  /-- the proof file -/
  | proof
  deriving DecidableEq, Repr, Inhabited

/-- A file's role as it is printed. -/
def Role.text : Role → String
  | .policy => "policy"
  | .KL => "KL"
  | .layout => "layout"
  | .key => "key"
  | .entry => "entry"
  | .request => "request"
  | .y => "y"
  | .proof => "proof"

/-- What the file of a role is called in a sentence. -/
def Role.file : Role → String
  | .policy => "policy.txt"
  | .KL => "KL.bin"
  | .layout => "layout.txt"
  | .key => "key.bin"
  | .entry => "the entry file"
  | .request => "the request file"
  | .y => "the y file"
  | .proof => "the proof file"

/-- How a call ends. -/
inductive CallEnd where
  /-- every test of a whole call passed, under the exact match or with the reply's token alone
  covered -/
  | yes (about : Covered) (c : Closing)
  /-- every test of a whole call passed, and a token of the request itself was checked under the
  clipped-gap policy that the caller named -/
  | withinLimits (about : Covered) (c : Closing)
  /-- a call on one file alone found no fault -/
  | partPassed (s : StageName) (c : Closing)
  /-- no test that ran failed, but the call is not a verification -/
  | notVer (causes : List String) (about : Option Covered) (c : Closing)
  /-- a stage refused: the stage, the name that the checker of its file gave to the failed check,
  if any, and the name of the refusal -/
  | refusedBy (s : StageName) (why : Option String) (name : String)
  /-- the files are not those of the commitment that the caller named -/
  | wrongId
  /-- the call's policy does not fit; no stage has run -/
  | policy (why : PolicyWhy)
  /-- a test failed before any stage; its name -/
  | no (name : String)
  /-- a guard of the verifier's own failed: nothing has been verified -/
  | notChecked (name : String)
  /-- an input file is missing or cannot be read -/
  | unreadable (role : Role)
  /-- a bad command line: nothing goes to standard output. words: a short form of what cp_verify
  writes to standard error. The program verify-on-bytes does not print them: it writes one fixed
  line (finish, OnBytes/Shell/Ask.lean) -/
  | usage (words : String)
  deriving DecidableEq, Repr

/-- The default ending is not a passing one, so that a value made only because the type needs one
never reads as a yes. -/
instance : Inhabited CallEnd := ⟨.notChecked "internal-stage"⟩

/-- For tests: the last line of cp_verify for this result. For an unreadable file cp_verify adds a
colon and the system's reason, which this value does not hold. A bad command line prints no line. A
refusal's name goes into the line as it comes, listed or not. The program's own last line is made in
OnBytes/Shell/Lines.lean. -/
def CallEnd.lastLine : CallEnd → String
  | .yes _ _ => "YES"
  | .withinLimits a _ =>
    "WITHIN LIMITS: " ++ a.policy.text ++ " C=" ++ toString a.C ++ " theta=" ++ toString a.theta ++
      " cap=" ++ toString a.cap ++ " s=" ++ toString a.s ++ " sh=" ++ toString a.sh
  | .partPassed s _ => "PART PASSED: " ++ s.text
  | .notVer _ _ _ => "NOT-A-VERIFICATION"
  | .refusedBy _ _ name => "NO: " ++ name
  | .wrongId => "NO: model-statement"
  | .policy _ => "NO: policy"
  | .no name => "NO: " ++ name
  | .notChecked name => "NOT CHECKED: " ++ name
  | .unreadable role => "input-unreadable-" ++ role.text ++ ": " ++ role.file ++ " cannot be read"
  | .usage _ => ""

/-- The exit code of cp_verify for this result. The tables of results: verifier/README.md, and for
this program lean/OnBytes/README.md, "Results". -/
def CallEnd.status : CallEnd → UInt32
  | .yes _ _ => 0
  | .withinLimits _ _ => 0
  | .partPassed _ _ => 3
  | .notVer _ _ _ => 14
  | .refusedBy _ _ _ => 1
  | .wrongId => 1
  | .policy _ => 1
  | .no _ => 1
  | .notChecked _ => 5
  | .unreadable _ => 2
  | .usage _ => 2

/-- What the call knows of the commitment's ID and of its own options. -/
structure CpId where
  /-- the ID that the caller named, in lower-case hex digits; empty if none -/
  asked : String := ""
  /-- the call named an ID -/
  named : Bool := false
  /-- without a named ID the call is not a verification: a yes would be about a key that nobody has
  named -/
  needed : Bool := true
  /-- the call named a policy -/
  policyGiven : Bool := false
  /-- the digest of the parameter files, in lower-case hex digits -/
  hPar : String := ""
  /-- -no-proof-of-work (C++: noWork): no pass if a round meets the target only with its work -/
  noProofOfWork : Bool := false
  deriving DecidableEq, Repr

/-- Written by hand: a derived instance would set `needed` to false. This one takes each field's own
default, so a named ID is needed. -/
instance : Inhabited CpId := ⟨{}⟩

/-- The first stage that refused with a name that is neither internal nor empty, and that name. -/
def firstNo : List StageOut → Option (StageOut × String)
  | [] => none
  | x :: xs =>
    match x.ending with
    | .no name => if internalName name || name.isEmpty then firstNo xs else some (x, name)
    | _ => firstNo xs

/-- The fault of the program that one stage's result shows, if any. `asked`: the bits asked of the
call. `own`: the stage's record is that of its own file, which is so for every stage but the last
of a whole call. The faults, in the order in which they are looked for:
 1. the record's target is below the bits asked: internal-sums-line;
 2. the stage passed, the record is its own file's, and the two disagree on whether work is needed:
    internal-sums-line;
 3. the stage refused: its own name if that is internal, else internal-stage;
 4. the stage passed with a note on work that has not 1 to 32 bits of work: internal-stage;
 5. the stage passed without a record: internal-sums-line. -/
def stageFault (asked : Nat) (own : Bool) (x : StageOut) : Option String :=
  let record : Option String :=
    match x.acct with
    | none => none
    | some a =>
      if a.target < asked then some "internal-sums-line"
      else if own && x.ending == .passed && a.needsWork != x.work.isSome then
        some "internal-sums-line"
      else none
  match record with
  | some n => some n
  | none =>
    match x.ending with
    | .no name => if internalName name then some name else some "internal-stage"
    | .notVer _ => none
    | .passed =>
      if x.work.any fun w => w.work < 1 || w.work > workMost then some "internal-stage"
      else if x.acct.isNone then some "internal-sums-line"
      else none

/-- The first fault of the program that the stages' results show. `asked`: the bits asked of the
call. `single`: the call has one stage, so that the last stage's record is its own file's too. -/
def firstFault (asked : Nat) (single : Bool) : List StageOut → Option String
  | [] => none
  | [x] => stageFault asked single x
  | x :: xs =>
    match stageFault asked true x with
    | some n => some n
    | none => firstFault asked single xs

/-- Of the stages' notes on work the one with the fewest centibits; of equals, the first. -/
def leastWork : List StageOut → Option WorkNote
  | [] => none
  | x :: xs =>
    match x.work, leastWork xs with
    | some w, some v => if v.centibits < w.centibits then some v else some w
    | some w, none => some w
    | none, r => r

/-- The causes for which stages ended as not a verification, each after its stage's name. A stage
that ended so and names no cause still gives a line. -/
def stageCauses (l : List StageOut) : List String :=
  l.flatMap fun x =>
    match x.ending with
    | .notVer [] => ["stage " ++ x.name.text ++ ": no cause printed"]
    | .notVer causes => causes.map fun c => "stage " ++ x.name.text ++ ": " ++ c
    | _ => []

/-- True if the stages' least note on work fits the call's record. The two agree on whether work is
needed. If it is, the bits differ by at most a hundredth and the bits of work are equal. (cp_verify
cuts the two numbers to different lengths on their way; here both are whole hundredths, and the same
allowance is kept.) Without a record nothing fits. -/
def workFits (work : Option WorkNote) (record : Option Acct) : Bool :=
  match work, record with
  | none, some a => !a.needsWork
  | none, none => false
  | some w, some a =>
    a.needsWork && decide (w.centibits ≤ a.centibits + 1) &&
      decide (a.centibits ≤ w.centibits + 1) && w.work == a.work
  | some _, none => false

/-- True if a stage passed with a note on work. In cp_verify such a stage ends with the words STAGE
PASSED WITH WORK. -/
def passedWithWork (stages : List StageOut) : Bool :=
  stages.any fun x => x.ending == .passed && x.work.isSome

/-- True if the call's record, which is the last stage's, says that some round meets the target only
with its work. -/
def recordNeedsWork (stages : List StageOut) : Bool :=
  (stages.getLast?.bind (·.acct)).any (·.needsWork)

/-- The stages that a call runs, in their order: the one stage of a call on one file alone, or all
three. There is no call on a proof file alone. -/
def stagesDue : Option StageName → Option (List StageName)
  | some .request => none
  | some s => some [s]
  | none => some [.key, .leaf, .request]

/-- What a call that has reached its end says besides its verdict. idHex: the ID that the stages
have formed. The numbers on work are those of the call's record, which is the last stage's. -/
def closingOf (stages : List StageOut) (id : CpId) (idHex : String) : Closing :=
  let record := (stages.getLast?.bind (·.acct)).getD { target := 0, needsWork := false }
  { idHex := if id.needed && !id.named then none else some idHex
    idNamed := id.named
    hPar := id.hPar
    stageWork := stages.filterMap fun x =>
      (x.work.filter fun w => decide (1 ≤ w.work) && decide (w.work ≤ workMost)).map fun w =>
        (x.name, w)
    work :=
      if record.needsWork then some ⟨record.mostWork, record.byWork, record.leastRound⟩ else none
    leastRound := record.leastRound
    leastWithoutWork := record.centibits
    -- The record of every stage but the last is that of the stage's own file.
    oneTimeAssumed := (stages.dropLast.filterMap (·.acct)).foldl (fun s a => s + a.closeOther) 0
    tableRecord := stages.any (·.oneTimeLine) }

/-- The result of a call from the results of its stages. The first rule that applies decides.
 1. A stage refused with a name neither internal nor empty: refused by the first such stage. If the
    name is model-statement, the files are not those of the commitment that the caller named.
 2. The stages are not those that the call runs (`stagesDue`), or a stage's result shows a fault of
    the program (`stageFault`): not checked.
 3. In a whole call, `about` is missing or `cpCovered` refuses it (what the answer is about could
    not be said): not checked.
 4. A stage gives no record of its accounting: not checked. No round's error is compared here: each
    stage has compared its own file's rounds with the target.
 5. Three conditions, tested in this order; each ends the call as not checked. The first stage's ID
    has not 64 digits, or the stages formed different IDs: internal-id-two-ways. The call had
    -no-proof-of-work, no stage ended as not a verification, and `passedWithWork` differs from
    `recordNeedsWork`: internal-sums-line; without the option rule 7 tests that, after rule 6. The
    stages formed another ID than the caller's, or the two fields of `id` on the caller's ID
    contradict each other: internal-id-two-ways. A caller's wrong ID does not get here: each stage
    compares its ID with the caller's and refuses with model-statement, which rule 1 takes.
 6. A stage ended as not a verification, a needed ID was not named, the call had -no-proof-of-work
    and `passedWithWork` or `recordNeedsWork` holds, or `belowBar` is set: not a verification.
 7. The stages' notes on work do not fit the call's record, which is the last stage's: not checked.
 8. A call on one file alone: the part has passed.
 9. A token of the request itself was checked under a policy other than the exact match: not
    checked if the caller named no policy, else within limits.
 10. Otherwise: yes.
`part`: the call is on one file alone. `asked`: the bits asked of the call. `belowBar`: these are
fewer than the threshold (`bar`, OnBytes/Model/Frame.lean). As in cp_verify it is not computed from
`asked` here: the caller passes askedBelowBar of the same number. `id`: what the call knows of the
commitment's ID and of its options. `about`: for a whole call the words of the request file and the
policy's lines under which the stage request has judged; a call on one file alone passes nothing.
The stages' records are taken as the call reads them (`StageOut.asRead`). The test on the stages'
names has no counterpart in cp_verify, where each call writes the list of its stages and its passing
words side by side. cp_verify tests the kind of policy, which is a part of rule 3 here, after the
first half of rule 9 and just before either passing word of a whole call. So where rule 3 decides
because sT + 4 ≠ sh, this function ends as not checked with internal-policy-kind, and cp_verify goes
on. The first of rules 4 to 7 and the first half of rule 9 that applies ends it: rule 6 as not a
verification, the others as not checked with internal-sums-line, internal-id-two-ways or
internal-policy-not-given. If none applies, it ends with internal-policy-kind, as this function
does. cpPolicyHeld (OnBytes/Model/VerifyHeads.lean) refuses such a file before any stage. -/
def cpStagesRun (stages : List StageOut) (part : Option StageName) (belowBar : Bool)
    (asked : Nat) (id : CpId) (about : Option (Array UInt32 × PolicyLines)) : CallEnd :=
  let stages := stages.map StageOut.asRead
  match firstNo stages with
  | some (x, name) =>
    if name == "model-statement" then .wrongId else .refusedBy x.name x.why name
  | none =>
  if some (stages.map (·.name)) != stagesDue part then .notChecked "internal-stage" else
  match firstFault asked part.isSome stages with
  | some name => .notChecked name
  | none =>
  let said : Except String (StageName ⊕ Covered) :=
    match part, about with
    | some s, _ => .ok (.inl s)
    | none, some a => (cpCovered a.1 a.2).map .inr
    | none, none => .error "internal-covered-line"
  match said with
  | .error name => .notChecked name
  | .ok who =>
  if stages.any (·.acct.isNone) then .notChecked "internal-sums-line" else
  let idHex := (stages.head?.map (·.idHex)).getD ""
  if idHex.length != hexW || stages.any (fun x => x.idHex != idHex) then
    .notChecked "internal-id-two-ways"
  else
  if id.noProofOfWork && (stageCauses stages).isEmpty &&
      passedWithWork stages != recordNeedsWork stages then
    .notChecked "internal-sums-line"
  else
  if (id.named == id.asked.isEmpty) || (id.named && id.asked != idHex) then
    .notChecked "internal-id-two-ways"
  else
  let c := closingOf stages id idHex
  let causes := stageCauses stages ++ (if id.needed && !id.named then ["id-named"] else []) ++
    (if id.noProofOfWork && (passedWithWork stages || recordNeedsWork stages) then
      ["no-proof-of-work"] else [])
  if !causes.isEmpty || belowBar then
    .notVer causes (match who with | .inl _ => none | .inr a => some a) c
  else
  if !workFits (leastWork stages) (stages.getLast?.bind (·.acct)) then
    .notChecked "internal-sums-line"
  else
  match who with
  | .inl s => .partPassed s c
  | .inr a =>
    if !a.otherKind then .yes a c
    else if !id.policyGiven then .notChecked "internal-policy-not-given"
    else .withinLimits a c

end OnBytes.Model.Stages
