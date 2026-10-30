-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/Claim.lean: a `Body` (the part that a program supplies to the general command-line
wrapper, OnBytes/ShellOf/Body.lean) whose types keep what the user claims apart from what an
untrusted parser hands over.

States. Definitions only. `Claim`: what the user gives: the commitment ID and the three public
files. `Kit`: what such a program is made of: trusted `state` (by its type it sees the claim alone)
and `verify`; untrusted `parse`; text for messages only: `stage`, `gives`, `word`, `usage`.
`bodyOf`: the body. `runOf`: the call's truth value as a plain function. The notes hold a table: who
supplies each datum, and what tests it.
Under. No hypothesis. The theorems are in ClaimLaws.lean.
Does not show.
  1. What `verify` is worth.
  2. That `verify` makes the tests which the table says it owes: that is each program's own matter.
  3. That `runOf` agrees with the shell's program, except, one way, at exit codes 0 and 10.
  4. Any test of `a.further` outside `verify` itself (see the table).
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ShellOf.Body
import OnBytes.Shell.Whole
import OnBytes.Model.VerifyHeads
import OnBytes.Params.Std
import OnBytes.Tie.EntryAsked

set_option autoImplicit false

namespace OnBytes.ShellOf.Claimed

open OnBytes.Tie (AskedE)

/-- What the user gives. -/
structure Claim where
  /-- the commitment ID, from the arguments, in lower-case digits -/
  id : String
  /-- the bytes of the three public files of the user's config folder -/
  cfg : Params.StdCfg

/-- An untrusted parser: from the claim, the key file and the entry file to plain data. -/
abbrev Parser : Type := Claim → ByteArray → ByteArray → Except String AskedE

/-- What a program of this kind is made of. -/
structure Kit where
  /-- the statement -/
  X : Type
  /-- Trusted. The statement, made of the claim alone. -/
  state : Claim → Except String X
  /-- Untrusted: it owes completeness alone. -/
  parse : Parser
  /-- Trusted: the verifier. -/
  verify : X → AskedE → Bool
  /-- Words alone: which of the verifier's stages said no. -/
  stage : X → AskedE → String
  /-- Words alone: what a yes gives out beside itself. -/
  gives : X → AskedE → List String
  /-- the last line of a yes: it says of what the yes is a yes -/
  word : String
  /-- the line that a call with other arguments gets -/
  usage : String

/-- The five files of a call, in the order in which they are read. -/
def wants (config key entry : String) : List Want :=
  [⟨config ++ "/policy.txt", Shell.textLimit⟩, ⟨config ++ "/layout.txt", Shell.textLimit⟩,
   ⟨config ++ "/KL.bin", Shell.fileLimit⟩, ⟨key, Shell.fileLimit⟩, ⟨entry, Shell.fileLimit⟩]

/-- Trusted. The arguments: the ID, as verify-on-bytes reads its option -id, and three paths. -/
def askC : List String → Option (String × List Want)
  | [id, config, key, entry] => (Model.Verify.idAsked id).map fun i => (i, wants config key entry)
  | _ => none

def usageC : String :=
  "usage: <commitment ID: 64 hex digits> <config folder> <key file> <entry file>"

/-- The body. -/
def bodyOf (K : Kit) : Body where
  A := String
  X := K.X
  V := AskedE
  ask := askC
  head := fun _ _ => none
  state := fun id bs =>
    match bs with
    | [pol, lay, kl, _, _] => K.state ⟨id, ⟨pol, lay, kl⟩⟩
    | _ => .error "not five files"
  short := fun _ => none
  conv := fun id _ bs =>
    match bs with
    | [pol, lay, kl, key, ent] => K.parse ⟨id, ⟨pol, lay, kl⟩⟩ key ent
    | _ => .error "not five files"
  verify := K.verify
  stage := K.stage
  gives := K.gives
  word := K.word
  usage := K.usage

/-- The call's truth value, as a plain function of the claim and the two other files. -/
def runOf (K : Kit) (cl : Claim) (key ent : ByteArray) : Bool :=
  match K.state cl with
  | .error _ => false
  | .ok x =>
    match K.parse cl key ent with
    | .error _ => false
    | .ok a => K.verify x a

end OnBytes.ShellOf.Claimed

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/ShellOf/Claim.lean: a body for the general shell (OnBytes/ShellOf/Body.lean) whose shape
keeps the user's claim apart from an untrusted parser's value. Definitions alone; the laws are in
OnBytes/ShellOf/ClaimLaws.lean.

  The call: <commitment ID: 64 hex digits> <config folder> <key file> <entry file>
  `Claim`: what the user gives: the commitment ID (an argument) and the bytes of the three public
    files.
  `Kit`: what a program of this kind is made of. Trusted: `state` (the statement; BY ITS TYPE it
    sees the claim alone: neither the key file, nor the entry file, nor the parser's value) and
    `verify`. Untrusted: `parse`. Words alone: `stage`, `gives`, `word`, `usage`.
  `bodyOf`: the body. `runOf`: the call's truth value as a plain function of the claim and the two
    files.

Who lays what, and what tests it (the value's type is `AskedE`, OnBytes/Tie/EntryAsked.lean):
  datum                      | who lays it                   | what tests it
  the claim's ID             | the user: an argument         | `idAsked`: 64 hex digits
  the three public files     | the user: read in the folder  | the caps; then `state`
  the statement x            | `state`, of the claim alone   | nothing of the parser's enters it
  a.first (root, answers)    | THE PARSER                    | `verify` owes a test by the claim
  a.further (root, answers)  | THE PARSER                    | nothing outside `verify`'s own run
  a.l0, a.l1 (seeds)         | THE PARSER                    | `verify` owes a test
  a.out.run (a salt)         | THE PARSER                    | it is hashed: `verify` owes a test
  a.out (the rest, as read)  | THE PARSER                    | it is the proof: `verify`
Each file is read once, and the same bytes go to `state` and to `parse`.

What this file does not give. Nothing here says what `verify` is worth, nor that it makes the tests
that the table says it owes: that is each kit's matter. `runOf` is a second text of the order in
which `judged` (OnBytes/ShellOf/Body.lean) goes; ClaimLaws.lean ties it to the program at the codes
0 and 10 alone.

-/
