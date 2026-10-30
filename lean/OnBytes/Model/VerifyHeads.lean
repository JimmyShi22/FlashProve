-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyHeads.lean: the tests of a call that come before its three stages.

The C++ verifier reads every file once, tests the headers of the key file and of the proof file, and
only then starts the stages (verifier/src/cp_verify.cpp, cpMain; vf_input_files.h). A test that
fails here ends the call with a no that belongs to no stage. Two tests, on the form of the named ID
and on the kind of the named policy, end it as a bad command line. A file that cannot be read ends
it without a verdict. This file makes these tests in the same order and with the same names. One
guard is this program's own and ends a call as not checked (`policyEnd`, internal-policy-empty).

A whole call's policy is also tested here, before the proof is read: first the numbers of a named
policy by themselves, then the parameter file's policy against the named one and against what the
request covers. Between the two, a whole call tests the lengths of the request and of the reply
(`cpLengthHeld`).

Words (more in lean/GLOSSARY.md). A whole call checks a key file, an
entry file and the proof of one request, in the three stages key, leaf and request
(OnBytes/Model/VerifyStages.lean); the calls -key and -leaf check one file. The parameter file is
policy.txt: the role `.policy` and a name that ends in "(policy)" mean that file. KL.bin, the scale
file, holds the quantization scales. The y file holds the reply's one token (the next token).

The policy is the acceptance policy: seven lines of the parameter file that say how close the
request's checked tokens must be to the model's top choice. Their names are C, theta, cap, s, sh, sT
and F. The line sT selects the table that the output head looks up, and F scales it. A whole call
accepts only sT = sh - 4. A checked token's cost is then its logit gap, which is 0 for the top
choice, plus 2^sh. Only a checked token of the request itself has a cost. The reply's token has
none: under every policy it is meant to be the top choice. A proof is meant to show that the costs,
each clipped at C, add up to at most theta times their number, and that at most cap of them exceed
C. With C = theta = 2^sh and cap = 0 that is the exact match: every checked token is the top choice.
With other numbers it is a clipped gap, which can say less: a token above C can be any token. The
line s is the provider's statement of the scale of the logits (an integer logit is a real logit
times 2^s); no test compares it with the model. With -policy a caller names the kind (exact-match or
clipped-gap) and C, theta, cap, s, sh (`PolicyNamed`, OnBytes/Model/Config.lean). Every line:
verifier/docs/parameter-file.md, section 8.

Main definitions: `cpPolicyWord`, `cpKeyHead`, `cpProofHead`, `cpConfRead`, `Read`, `policyEnd`,
`cpPolicySays`, `cpPolicyHeld`, `readFirst`, `kindNamed`, `cpLengthHeld`, `readCall`.
What is not claimed: no theorem is stated here, and nothing is said about the content of the files
beyond the tests of this file.
-/
import OnBytes.Model.VerifyInputs
import OnBytes.Proof.Head

namespace OnBytes.Model.Verify

open OnBytes.Model.Stages

/-- Ends the call with a no and the given name, before any stage has run. -/
def callNo {α : Type} (name : String) : Except CallEnd α := .error (.no name)

/-- Refuses with the given name unless ok is true. -/
def callNeeds (ok : Bool) (name : String) : Except CallEnd Unit :=
  if ok then pure () else callNo name

/-- True if a call asks for fewer bits than the threshold. Such a call makes every test and ends at
best as not a verification. C++: askedBelowBar. -/
def askedBelowBar (asked : Nat) : Bool := decide (asked < bar)

/-- The bytes of a file. A file that could not be read ends the call. That end is no verdict: it
says what role the file has in the call and never its path. C++: needBytes, mustReadWords,
unreadableInput. -/
def needBytes (f : FileIn) (role : Role) : Except CallEnd ByteArray :=
  match f with
  | some b => pure b
  | none => .error (.unreadable role)

/-- The value of x, or the end of the call with a no and the name that x carries. -/
def callNamed {α : Type} (x : Except String α) : Except CallEnd α :=
  match x with
  | .ok a => pure a
  | .error name => callNo name

/-- The four bytes that name the version of the format that this program accepts. -/
def servedVersion : ByteArray := Proof.versionOf .two

/-- Why the four bytes of the parameter file's first line are not the served version, as one of four
names. C++: version_refusal, checkVersionLine. -/
def versionRefusal (w : List UInt8) : String :=
  match w with
  | [0x48, b, c, _] =>
    if b == 0x47 || b == 0x37 then "version-of-an-earlier-format (policy)"
    else if b == 0x38 && c != 0x32 then "version-of-another-field (policy)"
    else if b == 0x38 then "version-of-another-hash (policy)"
    else "version-unknown (policy)"
  | _ => "version-unknown (policy)"

/-- The test on the first line of the parameter file: the word version, a space, four bytes, a line
feed, and the four bytes are the served version. Every stage makes this test again in its scan.
C++: cpPolicyWord (verifier/src/cp_verify.cpp). -/
def cpPolicyWord (pol : ByteArray) : Except CallEnd Unit :=
  let has := pol.extract 0 8 == "version ".toUTF8 && decide (12 < pol.size) &&
    pol.extract 12 13 == ⟨#[0x0A]⟩
  let w := pol.extract 8 12
  if has && w == servedVersion then pure ()
  else callNo (versionRefusal (if has then w.toList else []))

/-- The test on the header of the key file: its tag and the served version. C++: cpKeyHead
(verifier/src/vf_input_files.h). -/
def cpKeyHead (b : ByteArray) : Except CallEnd Unit := do
  callNeeds (decide (8 ≤ b.size)) "cp-key-length"
  callNeeds (b.extract 0 4 == Proof.FileKind.key.tag && b.extract 4 8 == servedVersion)
    "cp-key-head"

/-- The test on the header of a proof file: its tag and the served version. Returns the number of
the entry on which the proof was made. There is no test on that number: a number without an entry
ends the call where the entry is read. C++: cpProofHead (verifier/src/vf_input_files.h). -/
def cpProofHead (b : ByteArray) : Except CallEnd Nat := do
  callNeeds (decide (12 ≤ b.size)) "cp-proof-length"
  callNeeds (b.extract 0 4 == Proof.FileKind.proof.tag && b.extract 4 8 == servedVersion)
    "cp-proof-head"
  pure (Proof.word32At b 8)

/-- The bytes of the three configuration files, or the end of the call. If the folder has no
layout.txt the result has none; if the name exists, the file must be readable. The length of the
scale file must be a multiple of four. Without a layout file no call passes: it is refused as
plan-layout at the latest. C++: cpConfRead (verifier/src/vf_input_files.h). -/
def cpConfRead (policy KL : FileIn) (layout : Option FileIn) :
    Except CallEnd (ByteArray × ByteArray × Option ByteArray) := do
  let pol ← needBytes policy .policy
  let KL ← needBytes KL .KL
  callNeeds (KL.size % 4 == 0) "KL-length"
  let layout ←
    match layout with
    | none => pure none
    | some l => (needBytes l .layout).map some
  pure (pol, KL, layout)

/-- The ID of the option -id in lower-case digits, or `none` if it is not 64 hex digits. -/
def idAsked (id : String) : Option String :=
  let l := id.toList.map fun c => if 'A' ≤ c && c ≤ 'F' then c.toLower else c
  if l.length == hexW && l.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    some (String.ofList l)
  else none

/-- The files of a call as the stages take them. -/
structure Read where
  /-- policy.txt -/
  pol : ByteArray
  /-- KL.bin; its length is a multiple of four -/
  KL : ByteArray
  /-- layout.txt, if the folder has one -/
  layout : Option ByteArray
  /-- key.bin -/
  key : ByteArray
  /-- the request file -/
  request : ByteArray
  /-- the y file -/
  y : ByteArray
  /-- the proof file -/
  proof : ByteArray
  /-- the number of the entry that the proof names -/
  entry : Nat
  /-- what the call knows of the commitment's ID, whether it names a policy, whether it had
  -no-proof-of-work, and the digest of the configuration files that is printed -/
  id : CpId

/-- Ends the call with a no on the policy, before any stage has run. -/
def policyNo {α : Type} (why : PolicyWhy) : Except CallEnd α := .error (.policy why)

/-- What follows from kind, the number that `policyEmpty` (OnBytes/Model/Config.lean) gives for a
named policy. At 0 the call goes on. At 1 to 4 a result would mean nothing, and the call is refused
with the reason that the number stands for. Any other number would be a fault of this program: the
call ends as not checked. The C++ verifier has no such last case. place: the position of the last
token of a request, which the fourth reason carries. -/
def policyEnd (kind place : Nat) : Except CallEnd Unit :=
  match kind with
  | 0 => pure ()
  | 1 => policyNo .clipBelowLeast
  | 2 => policyNo .meanBelowLeast
  | 3 => policyNo .meanAboveClip
  | 4 => policyNo (.noneBarred place)
  | _ => .error (.notChecked "internal-policy-empty")

/-- Refuses a named policy of one of the four kinds that `policyEmpty` finds. A policy that passes
can still bar no token. n: how many tokens of the request are checked, or 0 where no request has
been read. T: the number of tokens of a request. C++: cpPolicySays. -/
def cpPolicySays (p : Option PolicyNamed) (n T : Nat) : Except CallEnd Unit :=
  match p with
  | some p => policyEnd (policyEmpty n p.C p.theta p.cap p.sh) (T - 1)
  | none => pure ()

/-- Compares the policy of the parameter file with the call, before the proof is read. pol: the
parameter file. request: the words of the request. The tests, in their order: the file sets the
exact match or a clipped gap; a named policy is the file's; a call that names none covers no token
of the request under a policy other than the exact match; the named policy passes `cpPolicySays` for
this request. Where one of the lines that are read here is missing from the file
or misspelled, or the request does not have the length or the range that the file asks for, the
remaining tests are left out: if the call reaches the stages, one of them refuses it (`readCall` has
refused a wrong length before, where the line lt is at most 20). C++: cpPolicyHeld. -/
def cpPolicyHeld (p : Option PolicyNamed) (pol : ByteArray) (request : Array Nat) :
    Except CallEnd Unit :=
  match Config.polWord pol "C", Config.polWord pol "theta", Config.polWord pol "cap",
      Config.polWord pol "s", Config.polWord pol "sh", Config.polWord pol "sT" with
  | some C, some theta, some cap, some s, some sh, some sT => do
    if sT + 4 != sh then
      policyNo (.fileKind (policyKind C theta cap s sh sT == "log-probability"))
    if p.any (!·.is C theta cap s sh sT) then policyNo .differs
    match Config.polWord pol "lt" with
    | none => pure ()
    | some lt =>
      if 20 < lt || request.size != 2 ^ lt + 2 then pure () else
      let T := 2 ^ lt
      let r := request.getD T 0
      let e := request.getD (T + 1) 0
      if e ≤ r || T < e then pure () else
      -- the tokens r + 1 .. min e (T - 1) of the request are checked
      let n := min e (T - 1) - r
      if p.isNone && n != 0 && !exactMatch C theta cap sh sT then policyNo .notNamed
      cpPolicySays p n T
  | _, _, _, _, _, _ => pure ()

/-- The tests that every call makes first, in the order of cpMain: the ID's form, the requested
bits, the numbers of a named policy, the configuration files, the key file, the digest of the
configuration files, the parameter file's first line, the key's header. An ID that is not 64 hex
digits ends the call as a bad command line, before a file is looked at. needed: true for a whole
call, which is not a verification unless it names an ID. The request, the reply and the proof are
left empty. The option -no-proof-of-work is handed on in id; nothing is tested of it here. -/
def readFirst (o : Options) (f : Files) (needed : Bool) : Except CallEnd Read := do
  let asked ←
    match o.id with
    | none => pure ""
    | some t =>
      match idAsked t with
      | some x => pure x
      | none => .error (.usage "-id requires 64 hex digits")
  callNeeds (decide (o.bits ≤ hashLeast)) "cp-bits-above-digest"
  cpPolicySays o.policy 0 0
  let (pol, KL, layout) ← cpConfRead f.policy f.KL f.layout
  let key ← needBytes f.key .key
  let h ← callNamed (hPar pol KL layout)
  cpPolicyWord pol
  cpKeyHead key
  pure { pol, KL, layout, key, request := .empty, y := .empty, proof := .empty, entry := 0,
         id := { asked := asked, named := o.id.isSome, needed := needed,
                 policyGiven := o.policy.isSome, hPar := hex64 h,
                 noProofOfWork := o.noProofOfWork } }

/-- True if the kind of a named policy is one of the two that a command line can name. The other
kinds that the lines of a parameter file can set have no name on a command line, so that no call
can say that it expects such a policy. C++: policyNamedRead. -/
def kindNamed (p : PolicyNamed) : Bool :=
  ["exact-match", "clipped-gap"].contains p.kind

/-- Tests that a file has exactly `words` words of four bytes, before its content is looked at. An
empty file, or a length that is no multiple of four, is refused as statement-required; any other
wrong length as statement-range. A file that could not be read passes: the caller's read ends the
call. If one file alone is at fault, the name is the one with which the stage request refuses that
length (`requestRun`, OnBytes/Model/VerifyStages.lean; `Head.stFromCall`). If request and reply are
both at fault the names can differ: that stage looks for statement-required in both files first.
C++: cpLengthHeld (verifier/src/cp_verify.cpp), which asks the operating system for the length and
opens nothing. The two differ on a regular file of a wrong length that cannot be opened: cp_verify
refuses it here, with exit code 1; this program ends as for an input that cannot be read, with exit
code 2. -/
def cpLengthHeld (f : FileIn) (words : Nat) : Except CallEnd Unit :=
  match f with
  | none => pure ()
  | some b =>
    if b.size == 4 * words then pure ()
    else callNo (if b.size == 0 || b.size % 4 != 0 then "statement-required" else "statement-range")

/-- The tests of a whole call that come before the entry is read. A named policy of another kind
than the two ends the call as a bad command line, before anything else is looked at. The program's
shell tests the ID's form and the policy's kind itself when it reads the options, so the program
never gets to these two ends. The words that such a result holds are the C++ verifier's for the ID
and shorter than its words for the policy. The shell does not print them: it writes a fixed line of
its own to standard error (`finish`, OnBytes/Shell/Ask.lean). The lengths of the request and then of
the reply are tested before any test that looks at their bytes (`cpLengthHeld`). So a wrong length
of one ends the call with a no even if the other cannot be read. The program's shell has read both
files by then, each up to `fileLimit` (OnBytes/Shell/Ask.lean): that limit, and not this test,
bounds what is loaded. A request must have 2^lt tokens and two more words, a reply one word. The
request's length is tested only if the parameter file has a line lt of at most 20. The policy is
compared with the parameter file and the request after these tests and before the proof is looked
at. That test is left out if the request's length is no multiple of four. Such a request gets this
far only if its length was not tested. If the call reaches the stages, they refuse the parameter
file. The reply has four bytes by then, so the condition on its length always holds. -/
def readCall (o : Options) (f : Files) : Except CallEnd Read := do
  if o.policy.any (!kindNamed ·) then throw (.usage "-policy requires kind,C,theta,cap,s,sh")
  let r ← readFirst o f true
  match Config.polWord r.pol "lt" with
  | some lt => if lt ≤ 20 then cpLengthHeld f.request (2 ^ lt + 2)
  | none => pure ()
  cpLengthHeld f.y 1
  let request ← needBytes f.request .request
  let y ← needBytes f.y .y
  if request.size % 4 == 0 && y.size % 4 == 0 then cpPolicyHeld o.policy r.pol (fileWords request)
  let proof ← needBytes f.proof .proof
  let k ← cpProofHead proof
  pure { r with request := request, y := y, proof := proof, entry := k }

/-- The names with which this file refuses or ends a call as not checked. -/
def namesHeads : List String :=
  ["version-of-an-earlier-format (policy)", "version-of-another-field (policy)",
   "version-of-another-hash (policy)", "version-unknown (policy)", "policy", "cp-key-length",
   "cp-key-head", "cp-proof-length", "cp-proof-head", "cp-bits-above-digest", "KL-length",
   "internal-policy-empty", "statement-required", "statement-range"]

end OnBytes.Model.Verify
