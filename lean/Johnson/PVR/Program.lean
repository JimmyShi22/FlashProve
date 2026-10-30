-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/Program.lean: what the command `tools/lean-verify/lean_verify.sh` runs inside Lean to
judge a proof, but for the three lines of its entry (tools/lean-verify/LeanVerify.lean): from the
bytes of eleven files to a verdict.

`Given`: the eleven files, as bytes. `Claim`, `T`, `rangeOf`, `callOk`, `claimOf`: what the user
claims (commitment ID, prompt, output), and the request's tokens behind the checked positions, read
off the user's three files by the two readers `PV.Front.idOf` and `PV.Front.userOf`, behind four
tests of the format page. Below, "the claim reads" means that `claimOf g` is `some`.
`pubOf`, `formOf`: the three public files; the five parsed files with the further tokens.
`stepsOf`, `verdictAt`: the Lean verifier's executable form (`PV.Ride.rideThe`,
`PV.Ride.verdictThe`) at the format's hash `Fmt.oracle`. `verdictOf`: `claimOf`, then these two: one
pure function of the bytes. `verifyValue`: the value of `VerifierAndGoals.verify` at
`VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription`, the description of which the soundness theorem speaks, at
its own parser, at a claim, at these public files and parsed files, evaluated at
`hashOf Fmt.oracle`.
`verdictOf_at`: where the claim reads, `verdictOf g` is `verdictAt g c (stepsOf g c)`, whose parts
`ending` calls. `verdictOf_is_verify`: whatever verdict is given is `verifyValue` at the claim that
was read. `verdictOf_none`: where the claim does not read, no verdict is given. That a verdict is
always given where the claim reads: Johnson/PVR/ProgramTotal.lean.
`Ending`, `say`, `readRole`, `policyLines`, `whyNoClaim`, `ending`, `run`: the shell. It reads the
files, prints the claim, the steps and the verdict, and returns the exit code 0, 1 or 2, to which
the entry adds 10. It calls `claimOf`, `stepsOf` and `verdictAt` in turn, to print between them. By
its text it only reads files; how much of that a check holds: Johnson/PVR/ProgramGuard.lean, (3).

Limits. No soundness is stated here: `verdictOf_is_verify` says that two texts give one answer. It
is the case O = `Fmt.oracle` of a theorem that holds at every function O on bytes
(`PV.Ride.verdictThe_is_theDescription`). No theorem says that `claimOf` cuts the user's files as
the format page means or as the C++ verifier `cp_verify` does (lean/GAPS.md, 37). What tests look
at it in this library: 22 known answers in Johnson/PVR/ProgramGuard.lean; none of them against
`cp_verify`. So `run` prints the claim that it judges. No theorem speaks of `run`, nor of compiled
or interpreted code. The hash is one fixed function (BLAKE2b, called as the format page prescribes),
where the soundness theorem draws it at random. The parsed files come from a parser outside Lean
(tools/parser/), which is not verified. The soundness theorem takes the whole of `formOf` from the
prover: to that theorem a wrong parsed file is the prover's choice: it can cost an honest proof its
accept, and do no more than a prover can. Beside its own lines a run can print a fixed line of the
library's. Exact match is not tested here: at public files in scope that state another policy
`verdictOf` can be `some true`, where the main soundness theorem is silent: the foot of this file.
Terms: lean/TERMS.md; lean/GLOSSARY.md.
-/
import Johnson.PVR.RideThe
import Johnson.Top.Fire.Code.PvFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.Program
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutD (FastSteps)

/-- All that one call hands over, as bytes. The first three are the public files, the next three
the user's, the last five the parser's. -/
structure Given where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  id : ByteArray
  req : ByteArray
  y : ByteArray
  key : ByteArray
  keySeeds : ByteArray
  leaf : ByteArray
  leafSeeds : ByteArray
  proof : ByteArray

/-- What the user claims: the first three fields. The fourth is no part of the claim: the request's
tokens behind the checked positions, which go to the verifier with the proof. -/
structure Claim where
  commitment : Commitment
  prompt : List Token
  output : List Token
  further : List Token

/-- The number of tokens in a request file. The format page has 2 ^ lt, where lt is a line of the
parameter file; here it is the constant 1,024 of the one size that is in scope. At public files
with another lt the verifier's own test of the scope rejects. -/
abbrev T : Nat := Inst.Model.ppref.T

/-- The request file's two positions: the words number T and T + 1. -/
def rangeOf (req : ByteArray) : Nat × Nat :=
  let P := OnBytes.Model.Verify.words32 req
  ((P.getD T 0).toNat, (P.getD (T + 1) 0).toNat)

/-- Tests 1 to 4 of the format page on the caller's two files (docs/format/FORMAT.md, 12.2): the
request file has exactly T + 2 words of four bytes and the token file one; r < e ≤ T; where e < T
the token file holds 0. Where one of them fails this command gives no verdict, where `cp_verify`
rejects. Test 5 (every token below the vocabulary's size) is not made here: the verifier makes it
itself (step buildOk), and there the verdict is reject. -/
def callOk (req y : ByteArray) : Bool :=
  let (r, e) := rangeOf req
  req.size == 4 * (T + 2) && y.size == 4 && decide (r < e) && decide (e ≤ T) &&
    (e == T || ((OnBytes.Model.Verify.words32 y).getD 0 0).toNat == 0)

/-- The claim, off the user's three files; none where one of them does not read. The ID file: 64
hex digits in lower case, then at most a newline (`PV.Front.idOf`). The request file: T tokens, then
r and e; the token file: the next token (FORMAT.md, 12.2). By `PV.Front.userOf` the prompt is the
tokens 0 to r; the output is the tokens r + 1 to e, where token number T is the next token; the
further tokens are those behind e. -/
def claimOf (g : Given) : Option Claim :=
  if callOk g.req g.y then
    match PV.Front.idOf g.id, PV.Front.userOf T g.req g.y with
    | some i, some u => some ⟨_root_.Run.bytesToDig i, u.1.1, u.1.2, u.2⟩
    | _, _ => none
  else none

/-- The three public files. -/
def pubOf (g : Given) : VerifierAndGoals.PublicFiles := ⟨g.pol, g.lay, g.KL⟩

/-- The proof as `VerifierAndGoals.verify` takes it at `VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription`. -/
def formOf (g : Given) (c : Claim) : FlashProve.FormBytes :=
  ⟨c.further, g.key, g.keySeeds, g.leaf, g.leafSeeds, g.proof⟩

/-- The executable form's run, at the format's hash. -/
def stepsOf (g : Given) (c : Claim) : Except String FastSteps :=
  PV.Ride.rideThe (pubOf g) _root_.Fmt.oracle (formOf g c) c.commitment c.prompt c.output

/-- The executable form's verdict, read off a run. -/
def verdictAt (g : Given) (c : Claim) (r : Except String FastSteps) : Option Bool :=
  PV.Ride.verdictThe (pubOf g) _root_.Fmt.oracle (formOf g c) r

/-- **From bytes to verdict.** -/
def verdictOf (g : Given) : Option Bool :=
  (claimOf g).bind fun c => verdictAt g c (stepsOf g c)

/-- What `VerifierAndGoals.verify` answers at a claim, at these files, at the format's hash. -/
noncomputable def verifyValue (g : Given) (c : Claim) : Bool :=
  (VerifierAndGoals.verify (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription) (pubOf g)
    ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).parse (pubOf g)) c.commitment c.prompt c.output
    (formOf g c)).evaluate (hashOf _root_.Fmt.oracle)

/-- Where the claim reads, `verdictOf` is `verdictAt` at `stepsOf`: the parts `ending` calls. -/
theorem verdictOf_at (g : Given) (c : Claim) (h : claimOf g = some c) :
    verdictOf g = verdictAt g c (stepsOf g c) := by
  unfold verdictOf
  rw [h]
  rfl

/-- **Whatever verdict is given is `VerifierAndGoals.verify`'s, at the claim that was read.** -/
theorem verdictOf_is_verify (g : Given) (b : Bool) (h : verdictOf g = some b) :
    ∃ c, claimOf g = some c ∧ b = verifyValue g c := by
  cases hc : claimOf g with
  | none =>
    unfold verdictOf at h
    rw [hc] at h
    cases h
  | some c =>
    rw [verdictOf_at g c hc] at h
    exact ⟨c, rfl, PV.Ride.verdictThe_is_theDescription (pubOf g) _root_.Fmt.oracle (formOf g c)
      c.commitment c.prompt c.output b h⟩

/-- Where the claim does not read, no verdict is given. -/
theorem verdictOf_none (g : Given) (h : claimOf g = none) : verdictOf g = none := by
  unfold verdictOf
  rw [h]
  rfl

/-! ### The shell -/

/-- How a call ends. -/
inductive Ending where
  | accept
  | reject
  | noVerdict (why : String)

/-- The exit code: 0 for accept alone. The entry adds 10. -/
def Ending.code : Ending → UInt32
  | .accept => 0
  | .reject => 1
  | .noVerdict _ => 2

/-- The call's last line. -/
def Ending.line : Ending → String
  | .accept => "VERDICT: ACCEPT"
  | .reject => "VERDICT: REJECT"
  | .noVerdict why => "NO VERDICT: " ++ why

/-- The ending of a verdict. -/
def Ending.of : Option Bool → Ending
  | some true => .accept
  | some false => .reject
  | none => .noVerdict
      "the verifier gave none: PV.Program.verdictAt_eq rules this out for the Lean term, not for \
        compiled code"

/-- One line, to the error stream, at once. -/
def say (s : String) : IO Unit := do
  let h ← IO.getStderr
  h.putStrLn s
  h.flush

/-- No file above this many bytes is read (the parser's own bound). -/
def fileLimit : Nat := 2 ^ 28

/-- A file's bytes, or the words that say why there are none. -/
def readRole (role : String) (p : System.FilePath) : IO (Except String ByteArray) := do
  try
    let m ← p.metadata
    if m.type != .file then return .error s!"{role} is not a regular file: {p}"
    if m.byteSize.toNat > fileLimit then return .error s!"{role} has more than 2^28 bytes: {p}"
    let b ← IO.FS.readBinFile p
    if b.size > fileLimit then return .error s!"{role} has more than 2^28 bytes: {p}"
    return .ok b
  catch e => return .error s!"{role} cannot be read: {p}: {(toString e).replace "\n" " "}"

/-- yes or no, for the print. -/
def yn (b : Bool) : String := if b then "yes" else "no"

/-- The seven lines of the parameter file that are the acceptance policy (FORMAT.md, 12.5), for the
print alone: the verifier reads the parameter file by its own readers. A line with a sign that is
not printable ASCII is not shown: words that say so stand in its place. -/
def policyLines (pol : ByteArray) : List String :=
  match String.fromUTF8? pol with
  | none => ["(the parameter file is no text)"]
  | some t =>
    ((t.splitOn "\n").filter fun l =>
      ["C ", "theta ", "cap ", "s ", "sh ", "sT ", "F "].any fun w => l.startsWith w).map fun l =>
        if l.all fun ch => 32 ≤ ch.toNat && ch.toNat < 127 then l
        else "(a line with a sign that is not printable: not shown)"

/-- Why `claimOf` gave none, for the message alone. -/
def whyNoClaim (g : Given) : String :=
  let (r, e) := rangeOf g.req
  if (PV.Front.idOf g.id).isNone then
    "the commitment ID's file is not 64 lower-case hex digits and at most a newline"
  else (if g.req.size != 4 * (T + 2) then
    s!"the request file does not have {4 * (T + 2)} bytes (this command is for full size alone)"
  else if g.y.size != 4 then "the token file does not have 4 bytes"
  else if !(decide (r < e) && decide (e ≤ T)) then
    s!"the request's two positions are not r < e ≤ {T}: r = {r}, e = {e}"
  else s!"e = {e} is below {T}, and the token file does not hold 0") ++
    " (docs/format/FORMAT.md, 12.2)"

/-- What the entry must hand over. -/
def usage : String :=
  "seven lines are wanted in LEAN_VERIFY_ARGS: CONFIG_DIR ID_FILE REQUEST_FILE TOKEN_FILE \
    KEY_PARSED LEAF_PARSED PROOF_PARSED: call tools/lean-verify/lean_verify.sh"

/-- The eleven files of a call, in the order of `Given`, each with its role. -/
def rolesOf (config id req y key leaf proof : String) : List (String × System.FilePath) :=
  [("the parameter file", (config : System.FilePath) / "policy.txt"),
   ("the layout file", (config : System.FilePath) / "layout.txt"),
   ("the scale file", (config : System.FilePath) / "KL.bin"),
   ("the commitment ID's file", id), ("the request file", req), ("the token file", y),
   ("the parsed key file", key), ("the parsed key file's seeds", key ++ ".seeds"),
   ("the parsed leaf file", leaf), ("the parsed leaf file's seeds", leaf ++ ".seeds"),
   ("the parsed proof file", proof)]

/-- The call but for its last line. Its text calls `verdictOf`'s three parts one after the other, so
that the claim is printed before the run; that `verdictOf g` is these parts: `verdictOf_at`. No
theorem speaks of the IO around them. -/
def ending (args : List String) : IO Ending := do
  let [config, id, req, y, key, leaf, proof] := args | return .noVerdict usage
  unless (← IO.getEnv "LEAN_ABORT_ON_PANIC") == some "1" do
    return .noVerdict "LEAN_ABORT_ON_PANIC=1 is not set: a panic would pass unseen: call \
      tools/lean-verify/lean_verify.sh"
  let mut bs : Array ByteArray := #[]
  for (role, p) in rolesOf config id req y key leaf proof do
    match ← readRole role p with
    | .ok b => say s!"read: {role}: {b.size} bytes"; bs := bs.push b
    | .error why => return .noVerdict why
  let #[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] := bs
    | return .noVerdict "not all eleven files were read"
  let g : Given := ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
  let some c := claimOf g
    | return .noVerdict (whyNoClaim g)
  say s!"claim: commitment ID: {PV.Front.hex (_root_.Run.digToBytes c.commitment)}"
  say s!"claim: checked positions: from r = {c.prompt.length - 1} up to, not including, \
    e = {c.prompt.length - 1 + c.output.length}"
  say s!"claim: prompt, {c.prompt.length} tokens: {c.prompt}"
  say s!"claim: output, {c.output.length} tokens: {c.output}"
  say s!"not part of the claim: tokens of the request behind position e, which go to the \
    verifier with the proof: {c.further.length}"
  say s!"public files: the acceptance policy, by the parameter file's own lines: \
    {policyLines g.pol}"
  let r ← IO.lazyPure fun _ => stepsOf g c
  match r with
  | .ok s =>
    say s!"steps: buildOk {yn s.buildOk}; encOk {yn s.encOk}; idOk {yn s.idOk}; \
      laidT {yn s.laidT}; laidL {yn s.laidL}; laidB {yn s.laidB}; num {yn s.num}; \
      seed0 {yn s.seed0}; seedJ {yn s.seedJ}; armT {yn s.armT}; armL {yn s.armL}; \
      armB {yn s.armB}"
    say "(what the twelve steps are: tools/lean-verify/README.md)"
  | .error w => say s!"the run stopped before the steps: {w}"
  return Ending.of (verdictAt g c r)

/-- **The call.** `args`: `usage`. The result is the exit code. -/
def run (args : List String) : IO UInt32 := do
  let e ← ending args
  say e.line
  return e.code

end PV.Program

/-
The foot of this file: on the policy. The main soundness theorem, `sound_of_verify_at`
(Johnson/Goal/Skeleton/SoundOfVerifyAt.lean), has three hypotheses: the public files are in scope,
they are read, and they state exact match (`pp.pol = Inst.Model.AcceptancePolicy.exact`: C, theta and cap are
256, 256 and 0). `verify` tests the first two (`VerifierAndGoals.InScope`) and not the third. At public files
in scope under another policy, for instance (25856, 512, 1), `verdictOf` can be `some true` (seen in
runs, not proved: lean/THEOREM.md, on runs under that policy), and `run` then prints
"VERDICT: ACCEPT" and returns 0. There the main soundness theorem does not speak. A second theorem,
`soundUnderPolicy_of_verify_at` (Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean), speaks, for public
files in scope: the accepted reply meets the files' policy at the weights that the protocol's
extractor returns, except with probability at most the stated bound; that says less than that it is
the model's own output, and alone it is weak (that file's head; lean/THEOREM.md, on other acceptance
policies). `run` shows the parameter file's lines on the policy (`policyLines`) and tests nothing
of them. The script tools/lean-verify/lean_verify.sh says in an accept's line whether they state
exact match.
-/
