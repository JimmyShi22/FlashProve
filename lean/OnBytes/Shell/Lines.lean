-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Lines.lean: every line that the program prints on standard output.

A line is a value of the type `Line`, and only this file makes its text. What the checks return goes
into a line as typed fields. A number is printed in decimal if it is below 10^18. A check's name, or
the stage and name of a round, is printed only if it is in a fixed list and holds no line feed. A
digest is printed only if it is 64 lower-case hex digits. So these fields are all that reaches the
output of what was read from the files (`call_says`, OnBytes/Shell/AtCall.lean). That no line's text
holds a line feed is not proved in this file.

The lines of a whole call and of a call on one file alone are closing lines of the C++ verifier
cp_verify (verifier/src/cp_verify.cpp), character for character, with these exceptions:
- In a stage's note on proof of work the round is named more briefly: `key: CS`, where cp_verify
  has `key: CS (folded row, stage #)`. Round and figures can differ (OnBytes/LIMITS.md, point 17).
- After `refused by the stage <s>: ` comes the Lean checker's name for the failed check, where
  cp_verify repeats its checker's sentence.
- The line that begins with `result-v1` ends in `build=lean-verify-on-bytes`, where cp_verify has
  the digest that its build stamps into it.
- Why a file cannot be read: the GNU C library's text for seven error codes and one text of this
  program's own for every other (`Unread.text`), where cp_verify has its C library's text.
- This program's own words: `out-of-range`, `not-a-digest`, `unlisted-check`, `unlisted-place` for
  a field that cannot be printed, and the names of `shellNames` (OnBytes/Shell/Names.lean).
- After `NO: ` and `NOT CHECKED: ` comes the Lean checks' name for the failed check. The names are
  meant to be cp_verify's; some are this program's own (`internal-policy-empty`,
  OnBytes/Model/VerifyHeads.lean), and on one input the two programs can stop at different checks.
Of the causes of a NOT-A-VERIFICATION the program prints the call's own (`CallCause`). It does not
print those that cp_verify repeats from its stages, one line for each stage that ended so. So the
causes that are printed need not be all. Without `-no-proof-of-work`, a call that names an ID, asks
for fewer than 128 bits and fails no check ends with `NOT-A-VERIFICATION` and prints no cause. A
whole call that also names no ID prints the cause id-named alone.
The program prints none of cp_verify's other lines: the stages' reports, the accounting, and the
heading and the sentence on what failed before a line `NOT CHECKED: <name>`.

Main definitions: `Lists`, `Unread`, `Note`, `ChainIx`, `CallCause`, `Line`, `Line.text`, `Fields`,
`before`, `verdict`. What is not claimed: no theorem is stated here. That lines equal cp_verify's is
not proved.
-/
import OnBytes.Shell.Names
import OnBytes.Model.Stages

namespace OnBytes.Shell

open OnBytes.Model.Stages

/-- The fixed lists by which strings are printed. -/
structure Lists where
  /-- the names of checks -/
  names : List String
  /-- the places of rounds: a stage's name and a round's name, as in `key: CS` -/
  places : List String

/-- True if the string s is in the list l and holds no line feed. -/
def inList (l : List String) (s : String) : Bool := l.contains s && !s.toList.contains '\n'

/-- The string s if it is in the list l and holds no line feed, and `other` if not. -/
def shown (l : List String) (other s : String) : String := if inList l s then s else other

/-- A number in decimal, if it is below 10^18. -/
def num (n : Nat) : String := if n < 1000000000000000000 then toString n else "out-of-range"

/-- A number of hundredths with two decimals, as in `96.02`, if it is below 10^18. -/
def cents (n : Nat) : String :=
  if n < 1000000000000000000 then hundredths n else "out-of-range"

/-- True for a hex digit in lower case. -/
def isLowHex (c : Char) : Bool := c.isDigit || (decide ('a' ≤ c) && decide (c ≤ 'f'))

/-- A digest: 64 hex digits in lower case, or the word `not-a-digest`. -/
def hex64 (s : String) : String :=
  if s.length == 64 && s.toList.all isLowHex then s else "not-a-digest"

/-- yes or no. -/
def yesNo (b : Bool) : String := if b then "yes" else "no"

/-- Why a file could not be read. -/
inductive Unread where
  /-- no file at the path; so also if the path is a link that leads nowhere -/
  | noSuch
  /-- no permission -/
  | denied
  /-- a part of the path that should be a folder is not one -/
  | notDirectory
  /-- too many links one after the other -/
  | loop
  /-- the path or a part of it is too long -/
  | nameTooLong
  /-- the process may open no further file -/
  | tooManyOpen
  /-- the device reports an error -/
  | device
  /-- the path is not a regular file -/
  | notRegular
  /-- every other reason -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- The reason as it is printed. cp_verify prints the text that the C library has for the system's
error code (strerror), or a sentence of its own if there is no code. The first seven texts here are
the GNU C library's, the eighth is that sentence of cp_verify's, the last is this program's own. -/
def Unread.text : Unread → String
  | .noSuch => "No such file or directory"
  | .denied => "Permission denied"
  | .notDirectory => "Not a directory"
  | .loop => "Too many levels of symbolic links"
  | .nameTooLong => "File name too long"
  | .tooManyOpen => "Too many open files"
  | .device => "Input/output error"
  | .notRegular => "it is not a regular file, or the read came up short"
  | .other => "the system reports another error"

/-- The reason for an error code of Linux. Lean's library hands some codes on with a minus sign, as
a word of 32 bits; both spellings are taken. -/
def Unread.ofCode (code : UInt32) : Unread :=
  let c := if code < 2147483648 then code else 0 - code
  if c == 2 then .noSuch else if c == 13 then .denied else if c == 20 then .notDirectory
  else if c == 40 then .loop else if c == 36 then .nameTooLong else if c == 24 then .tooManyOpen
  else if c == 5 then .device else .other

/-- What a call on the files of a test protocol says before its last line. -/
inductive Note where
  /-- fewer than 128 bits are asked of every round -/
  | bits (n : Nat)
  /-- the key file is read only for the first table's root and the answers of its record -/
  | keyFile
  /-- the key file or entry file is read only for the table's root and the answers of its record -/
  | tableFile

/-- The line that is printed for a note. -/
def Note.text : Note → String
  | .bits n => "the bits asked in this call: " ++ num n
  | .keyFile => "not checked in this call: the key file's own proofs"
  | .tableFile => "not checked in this call: the file that names the table"

/-- The seven chains of a configuration, in the order in which a planning call prints them. -/
inductive ChainIx where
  | keyOneTime | keyShared | keySecond | entry | first | shared | second
  deriving DecidableEq, Repr, Inhabited

/-- A chain's name. -/
def ChainIx.text : ChainIx → String
  | .keyOneTime => "key.one-time"
  | .keyShared => "key.shared"
  | .keySecond => "key.second"
  | .entry => "entry"
  | .first => "first"
  | .shared => "shared"
  | .second => "second"

/-- A reason that lies in the call itself, not in a stage, for which the call ends as not a
verification. -/
inductive CallCause where
  /-- a whole call named no ID; the name is cp_verify's for the condition that is not met -/
  | idNamed
  /-- the call had `-no-proof-of-work`. rounds: the count, from the call's record, of rounds that
  fall short of the parameter file's target when their work is left uncredited -/
  | noProofOfWork (rounds : Nat)
  deriving DecidableEq, Repr

/-- The line that cp_verify prints for the cause (cpStagesRun, verifier/src/cp_verify.cpp). -/
def CallCause.text : CallCause → String
  | .idNamed =>
    "the call: not the standard parameter form: id-named (the call named no ID: add -id with " ++
    "the commitment ID)"
  | .noProofOfWork rounds =>
    "the call: not the standard parameter form: no-proof-of-work (the call had " ++
    "-no-proof-of-work, and " ++ num rounds ++
    (if rounds == 1 then " round meets" else " rounds meet") ++
    " the parameter file's target only with proof of work counted)"

/-- The call's own causes among the short names that a result carries (`cpStagesRun`,
OnBytes/Model/Stages.lean), in the order in which cp_verify prints them. A stage's cause begins
there with `stage ` and is left out. c: the result's closing values, for the number of rounds that
need their work. It is 0 if no work is counted: a stage passed with work, another ended as not a
verification, and the call's record counts none. cp_verify prints 0 there too. -/
def callCauses (causes : List String) (c : Closing) : List CallCause :=
  (if causes.contains "id-named" then [.idNamed] else []) ++
  (if causes.contains "no-proof-of-work" then [.noProofOfWork ((c.work.map (·.rounds)).getD 0)]
   else [])

/-- A line of standard output. -/
inductive Line where
  /-- the commitment's ID, or nothing if the call named none -/
  | commitmentId (hex : Option String)
  /-- whether the caller's ID was compared -/
  | idCompared (named : Bool)
  /-- the digest of the configuration files -/
  | hPar (hex : String)
  /-- a call on an entry file alone does not check the key -/
  | keyNotChecked
  /-- no call checks that the weights are hidden -/
  | weightHiding
  /-- what the result is about -/
  | covered (a : Covered)
  /-- a stage's note on work -/
  | stageWork (s : StageName) (w : WorkNote)
  /-- the proof of work that the result counts, with the weakest round's error when it is counted;
  the weakest round's error without work. Both in hundredths of a bit -/
  | work (w : Option WorkCount) (least : Nat)
  /-- how many closeness rounds of the key's and the entry's plans rest on another source than the
  proved lemma (`Acct.closeOther`, OnBytes/Model/Stages.lean). The line ends with a clause on the
  table's record; record is `Closing.tableRecord`, which no text of the line reads -/
  | commitment (n : Nat) (record : Bool)
  /-- the line for programs: the exit code, the bits that the call asked, the entry's number, and
  the fields of the result -/
  | result (status bits leaf : Nat) (a : Covered) (c : Closing)
  /-- the heading of the closing lines -/
  | theCall
  /-- a reason in the call itself for which it ends as not a verification -/
  | callCause (c : CallCause)
  /-- which stage rejected, and under which name of its checker -/
  | refusedBy (s : StageName) (why : Option String)
  /-- the first of two lines for a call that named another ID than the files have -/
  | otherId1
  /-- the second of them -/
  | otherId2
  /-- why the policy does not fit -/
  | policyWhy (why : PolicyWhy)
  /-- a note of a call on test files -/
  | note (n : Note)
  /-- a chain's digest in a planning call -/
  | planLine (c : ChainIx) (hex : String)
  /-- a chain whose parameter bytes are not derived -/
  | noPlan (c : ChainIx)
  /-- an input that cannot be read: no verdict -/
  | unreadable (role : Role) (u : Unread)
  /-- the verdict yes -/
  | yes
  /-- the verdict under a policy that the caller named -/
  | withinLimits (a : Covered)
  /-- a call on one file alone found no fault -/
  | partPassed (s : StageName)
  /-- no check failed, but the call is not a verification -/
  | notVer
  /-- a rejection -/
  | no (name : String)
  /-- nothing was verified -/
  | notChecked (name : String)
  /-- a call on test files found no fault -/
  | testPassed
  /-- a planning call checked no proof -/
  | planOnly

/-- The request's own tokens that are checked. -/
def tokensText (a : Covered) : String :=
  match a.tokens with
  | some (x, y) => num x ++ ".." ++ num y
  | none => "none"

/-- What a passing answer says, as it stands in the line for programs. -/
def claimText : Claim → String
  | .nextToken => "next-token"
  | .exactMatch => "exact-match"
  | .policy => "policy"

/-- Why the policy does not fit, as a sentence. -/
def whyText : PolicyWhy → String
  | .fileKind lp =>
    "the parameter file sets the kind of policy " ++
    (if lp then "log-probability" else "another-table") ++
    "; this program takes exact-match and clipped-gap"
  | .differs =>
    "the option -policy names another kind of policy or another C, theta, cap, s or sh than the " ++
    "parameter file sets"
  | .notNamed =>
    "the request covers more than the output token, the parameter file sets another policy than " ++
    "exact-match, and the call has no -policy"
  | .clipBelowLeast =>
    "a result under the named policy would mean nothing: C is below 2^sh, the least cost of a " ++
    "token, so no cost is read"
  | .meanBelowLeast =>
    "a result under the named policy would mean nothing: theta is below 2^sh, the least cost of " ++
    "a token, so no request can meet it"
  | .meanAboveClip =>
    "a result under the named policy would mean nothing: theta is above C, which no parameter " ++
    "file may set"
  | .noneBarred place =>
    "a result under the named policy would mean nothing: theta = C and cap is not below the " ++
    "number of the request's tokens that are checked, so none of them is barred; for the output " ++
    "token alone send a request with r = " ++ num place

/-- The sentence at the end of the line on what a result is about. -/
def coveredSentence : String :=
  " (places in the request, counted from 0; y=yes: the answer is about y too; it is about " ++
  "nothing else; above-clip: so many of the tokens named by tokens= may cost more than C, and " ++
  "such a token may be any token. It is no limit on the tokens that may be any token: one that " ++
  "costs C or less may be any token too where the committed model's logits lie close together, " ++
  "and no verifier sees that. All costs, each counted as at most C, add up to at most theta " ++
  "times the number of these tokens)"

/-- What ends the line on the commitment. cp_verify's text
(RECORDCLAUSE, verifier/src/vf_common.h). -/
def recordClause : String :=
  "; the table has a record: the binding of the weights rests on the theorem on codes " ++
    "(ePrint 2025/2055, Theorem 4.6), taken as given"

/-- The text of a line under the lists L. -/
def Line.text (L : Lists) : Line → String
  | .commitmentId (some h) => "commitment ID: " ++ hex64 h
  | .commitmentId none => "commitment ID: not-shown-without-id"
  | .idCompared true => "id: named by the caller and equal"
  | .idCompared false => "id: not compared: the call named none"
  | .hPar h => "h_par=" ++ hex64 h
  | .keyNotChecked =>
    "key: NOT CHECKED BY THIS CALL (its table was taken on its form alone; the part-call -key " ++
    "or a whole call checks it)"
  | .weightHiding =>
    "weight hiding: NOT CHECKED BY THIS CALL (it rests on how the commitment was made)"
  | .covered a =>
    "covered: r=" ++ num a.r ++ " e=" ++ num a.e ++ " T=" ++ num a.T ++ " C=" ++ num a.C ++
    " theta=" ++ num a.theta ++ " cap=" ++ num a.cap ++ " s=" ++ num a.s ++ " sh=" ++ num a.sh ++
    " positions=" ++ num a.r ++ ".." ++ num (a.e - 1) ++ " tokens=" ++ tokensText a ++
    " y=" ++ yesNo a.y ++ " next-token=" ++ yesNo a.nextToken ++
    " policy=" ++ a.policy.text ++ " above-clip=" ++ num a.aboveClip ++ coveredSentence
  | .stageWork s w =>
    "stage " ++ s.text ++ ": work: " ++ cents w.centibits ++ " + " ++ num w.work ++
    " (one round's error without its work, in bits, + its bits of work; " ++
    shown L.places "unlisted-place" w.place ++ ")"
  | .work none _ => "proof of work: none counted"
  | .work (some w) least =>
    "proof of work: up to " ++ num w.bits ++ " bits counted in " ++ num w.rounds ++
    (if w.rounds == 1 then " round" else " rounds") ++ "; with it the least round has " ++
    cents w.withWork ++ " bits, without it " ++ cents least ++ " bits"
  | .commitment n _ =>
    (if n == 0 then
      "commitment: every closeness round of the one-time files rests on the proved lemma"
    else
      "commitment: " ++ num n ++ " closeness round" ++ (if n == 1 then "" else "s") ++
      " of the one-time files rest" ++ (if n == 1 then "s" else "") ++
      " on another source than the proved lemma") ++
    recordClause
  | .result status bits leaf a c =>
    "result-v1 status=" ++ num status ++ " claim=" ++ claimText a.claim ++ " id=" ++
    (match c.idHex with
     | some h => hex64 h
     | none => "not-shown-without-id") ++
    " bits=" ++ num bits ++ " work=" ++ num ((c.work.map (·.bits)).getD 0) ++
    " work-rounds=" ++ num ((c.work.map (·.rounds)).getD 0) ++
    " least-round=" ++ cents c.leastRound ++
    " least-round-without-work=" ++ cents c.leastWithoutWork ++
    " commitment-assumed-rounds=" ++ num c.oneTimeAssumed ++
    " record=1" ++
    " r=" ++ num a.r ++ " e=" ++ num a.e ++ " T=" ++ num a.T ++ " tokens=" ++ tokensText a ++
    " y=" ++ yesNo a.y ++ " policy=" ++ a.policy.text ++ " C=" ++ num a.C ++
    " theta=" ++ num a.theta ++ " cap=" ++ num a.cap ++ " s=" ++ num a.s ++ " sh=" ++ num a.sh ++
    " sT=" ++ num a.sT ++ " F=" ++ num a.F ++ " above-clip=" ++ num a.aboveClip ++
    " leaf=" ++ num leaf ++ " stages=key,leaf,request dw=8 build=lean-verify-on-bytes"
  | .theCall => "---- the call ----"
  | .callCause c => c.text
  | .refusedBy s none => "refused by the stage " ++ s.text
  | .refusedBy s (some why) =>
    if inList L.names why then "refused by the stage " ++ s.text ++ ": " ++ why
    else "refused by the stage " ++ s.text
  | .otherId1 =>
    "id: these are not the files of the commitment that you named; nothing in them was checked"
  | .otherId2 =>
    "id: take the commitment ID from your own record of where it was published, never from " ++
    "these files"
  | .policyWhy why => "policy: " ++ whyText why
  | .note n => n.text
  | .planLine c h => c.text ++ " " ++ hex64 h
  | .noPlan c => c.text ++ " not derived"
  | .unreadable role u =>
    "input-unreadable-" ++ role.text ++ ": " ++ role.file ++ " cannot be read: " ++ u.text
  | .yes => "YES"
  | .withinLimits a =>
    "WITHIN LIMITS: " ++ a.policy.text ++ " C=" ++ num a.C ++ " theta=" ++ num a.theta ++
    " cap=" ++ num a.cap ++ " s=" ++ num a.s ++ " sh=" ++ num a.sh
  | .partPassed s => "PART PASSED: " ++ s.text
  | .notVer => "NOT-A-VERIFICATION"
  | .no name => "NO: " ++ shown L.names "unlisted-check" name
  | .notChecked name => "NOT CHECKED: " ++ shown L.names "unlisted-check" name
  | .testPassed => "TEST FILES PASSED"
  | .planOnly => "PLAN ONLY: no proof was checked"

/-- What the shell itself knows of a call and puts into its lines. -/
structure Fields where
  /-- why the file of a role could not be read -/
  why : Role → Unread := fun _ => .other
  /-- the bits that the call asked -/
  bits : Nat := 0
  /-- the number of the entry that the proof names -/
  leaf : Nat := 0
  /-- the call is a call on an entry file alone -/
  leafCall : Bool := false

/-- The closing lines of a call on one file alone, before the verdict: the heading, the call's own
causes `why` if it is not a verification, whether the ID was compared, the digest of the
configuration files, what the call does not check, the stage's note on work, and the line on
work. -/
def closingPart (why : List CallCause) (leaf : Bool) (c : Closing) : List Line :=
  [.theCall] ++ why.map .callCause ++ [.idCompared c.idNamed, .hPar c.hPar] ++
  (if leaf then [.keyNotChecked] else []) ++
  [.weightHiding] ++ c.stageWork.map (fun x => Line.stageWork x.1 x.2) ++
  [.work c.work c.leastWithoutWork]

/-- The closing lines of a whole call that ends with the exit code status, 0 or 14, before the
verdict: the heading, the call's own causes `why` if it is not a verification, the ID, whether it
was compared, the digest of the configuration files, what the call does not check, what the result
is about, the stages' notes on work, and the last three: the line on the commitment, the line on
work and the line for programs. -/
def closingWhole (p : Fields) (why : List CallCause) (status : Nat) (a : Covered) (c : Closing) :
    List Line :=
  [.theCall] ++ why.map .callCause ++
  [.commitmentId c.idHex, .idCompared c.idNamed, .hPar c.hPar, .weightHiding, .covered a] ++
  c.stageWork.map (fun x => Line.stageWork x.1 x.2) ++
  [.commitment c.oneTimeAssumed c.tableRecord, .work c.work c.leastWithoutWork,
   .result status p.bits p.leaf a c]

/-- The lines of standard output for a result, before its last line. -/
def before (p : Fields) : CallEnd → List Line
  | .yes a c => closingWhole p [] 0 a c
  | .withinLimits a c => closingWhole p [] 0 a c
  | .partPassed s c => closingPart [] (s == .leaf) c
  | .notVer causes (some a) c => closingWhole p (callCauses causes c) 14 a c
  | .notVer causes none c => closingPart (callCauses causes c) p.leafCall c
  | .refusedBy s w _ => [.theCall, .refusedBy s w]
  | .wrongId => [.otherId1, .otherId2]
  | .policy w => [.policyWhy w]
  | _ => []

/-- The last line of standard output for a result. A bad command line prints none: `finish`
(OnBytes/Shell/Ask.lean) ends such a call before it would call this function. -/
def verdict (p : Fields) : CallEnd → Line
  | .yes _ _ => .yes
  | .withinLimits a _ => .withinLimits a
  | .partPassed s _ => .partPassed s
  | .notVer _ _ _ => .notVer
  | .refusedBy _ _ name => .no name
  | .wrongId => .no "model-statement"
  | .policy _ => .no "policy"
  | .no name => .no name
  | .notChecked name => .notChecked name
  | .unreadable role => .unreadable role (p.why role)
  | .usage _ => .notChecked "internal-no-line"

end OnBytes.Shell
