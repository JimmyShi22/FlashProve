-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/Body.lean: a shell that is general in its body. Definitions alone; the laws are in
OnBytes/ShellOf/Laws.lean.

A program of this kind is a small shell, an untrusted converter (from the files' bytes to the value
that the verifier takes) and a verifier. The shell is written once, for every body.
  `Body`: what such a program is made of. Trusted: `ask` (the arguments), `head` (the files' kind
    and version), `state` (the statement, made of what the user gave), `short` (why a yes at that
    statement would be no verification) and `verify`. Untrusted: `conv`. Words alone: `stage`,
    `gives`, `word`, `usage`.
  `judged`: the pure part: on the bytes read, how the call ends.
  `prog`: the whole program as a value (OnBytes/Shell/Ask.lean): the reads, the lines, the end.
  `mainOf`: the program in IO, with the three operations of OnBytes/Shell/Ops.lean, and its exit
    code.
The shape enforces one rule: `verify` is called at the statement that `state` made, and `state`
never sees the converter's value. So nothing has to be compared afterwards, and the converter
cannot choose of what a yes is a yes. The words with which the converter refuses go to standard
error alone.

What this file does not give. Nothing here says what `verify` is worth. A body whose value holds a
part of the protocol, whose `verify` ignores its statement, or whose `short` never speaks, passes
through this shell like any other. By its type `state` sees the bytes of all files: that it reads
only the user's own is the body's duty, not the shape's. So is what `stage` and `gives` print of
the converter's value.
"Untrusted" says that `conv` may be any Lean function of its type; its compiled code runs in the
same process and is trusted like the rest of the program's. A path that the user gives is printed
as it is. Judge a call by its exit code.

-/
import OnBytes.Shell.Ops

set_option autoImplicit false

namespace OnBytes.ShellOf

open OnBytes.Shell (Ask FileRead opsIO)

/-- A file that a call reads: its path, and the most bytes that it may have. -/
structure Want where
  path : String
  cap : Nat

/-- What a program of this kind is made of. -/
structure Body where
  /-- what the arguments say, beside the paths -/
  A : Type
  /-- the statement -/
  X : Type
  /-- the value that the verifier takes beside the statement -/
  V : Type
  /-- Trusted. Reads the arguments: what they say, and the files to read, in their order. -/
  ask : List String → Option (A × List Want)
  /-- Trusted. The tests on the files' heads (kind, version): the name of the first that fails. -/
  head : A → List ByteArray → Option String
  /-- Trusted. The statement, from the arguments and the bytes of the user's own files (it is
  handed the bytes of all files: see the head). -/
  state : A → List ByteArray → Except String X
  /-- Trusted. Why a yes at this statement would be no verification, or nothing. It sees the
  statement alone, and it is asked before the converter runs. -/
  short : X → Option String
  /-- Untrusted: it owes completeness alone. From the bytes read to the value. It may see all that
  the shell holds, the statement too; the statement never sees it. -/
  conv : A → X → List ByteArray → Except String V
  /-- Trusted: the verifier. -/
  verify : X → V → Bool
  /-- Words alone: which of the verifier's own stages said no. Nothing is decided by it. -/
  stage : X → V → String
  /-- Words alone: what a yes gives out beside itself. Printed before the last line of a yes. -/
  gives : X → V → List String
  /-- the last line of a yes: it says of what the yes is a yes -/
  word : String
  /-- the line on standard error for arguments that `ask` refuses -/
  usage : String

/-- How a call ends. Every end but `yes` names the stage that made it. -/
inductive End where
  /-- the verifier said yes, and every line was written -/
  | yes
  /-- the verifier said no; the words name its own stage -/
  | no (stage : String)
  /-- the arguments give no call -/
  | usage
  /-- a file is missing or cannot be read -/
  | unread (path : String)
  /-- a file has more bytes than it may have -/
  | tooLong (path : String)
  /-- a file's head is of another kind or version -/
  | head (why : String)
  /-- what the user gave makes no statement -/
  | state (why : String)
  /-- a yes at this statement would be no verification; no further test is made -/
  | notVer (why : String)
  /-- the converter hands nothing over -/
  | converter (why : String)
  /-- an exception in IO; by `mainOf_never_fault` (Laws.lean) no run ends so -/
  | fault
  /-- a line could not be written to standard output: the call counts as not made -/
  | unwritten
  deriving DecidableEq, Repr

/-- The exit code. 0 is the yes alone. Every other end has a code of its own, from 10 to 19, which
names the shell's stage; the stages that a body's verifier has of its own share the code 10 and
differ in the printed words alone. The codes 1 to 9 are never returned: Lean's run-time was seen to
end a compiled program that ran out of memory with the status 1 (seen in runs; its source was not
read), so a no with the code 1 could not be told from such a crash. -/
def End.code : End → UInt32
  | .yes => 0
  | .no _ => 10
  | .usage => 11
  | .unread _ => 12
  | .tooLong _ => 13
  | .head _ => 14
  | .state _ => 15
  | .converter _ => 16
  | .fault => 17
  | .unwritten => 18
  | .notVer _ => 19

/-- The last line of a call on standard output. `w`: the body's word for its yes. The converter's
own words are no part of it. -/
def End.line (w : String) : End → String
  | .yes => w
  | .no s => "NO: the verifier: " ++ s
  | .usage => "NOT CHECKED: the arguments"
  | .unread p => "NOT CHECKED: cannot read " ++ p
  | .tooLong p => "NOT CHECKED: too long: " ++ p
  | .head y => "NOT CHECKED: the shell: a file's head: " ++ y
  | .state y => "NOT CHECKED: the shell: no statement: " ++ y
  | .notVer y => "NOT A VERIFICATION: " ++ y
  | .converter _ => "NOT CHECKED: the converter hands nothing over"
  | .fault => "NOT CHECKED: a fault"
  | .unwritten => "NOT CHECKED: not written"

/-- What is written to standard error before the last line: the converter's own words, where it
hands nothing over. -/
def End.aside : End → List String
  | .converter y => ["the converter's own words: " ++ y]
  | _ => []

/-- The pure part. On the bytes read: the lines before the last, and the end. The order: the heads,
the statement, whether a yes at it would be a verification, the converter, the verifier at the
statement. -/
def judged (B : Body) (a : B.A) (bs : List ByteArray) : List String × End :=
  match B.head a bs with
  | some y => ([], .head y)
  | none =>
    match B.state a bs with
    | .error y => ([], .state y)
    | .ok x =>
      match B.short x with
      | some y => ([], .notVer y)
      | none =>
        match B.conv a x bs with
        | .error y => ([], .converter y)
        | .ok v =>
          match B.verify x v with
          | true => (B.gives x v, .yes)
          | false => ([], .no (B.stage x v))

/-- The end of a call whose answer could not be written. -/
def unwritten : Ask End :=
  .err "the answer could not be written to standard output: take this call as not made"
    (.done .unwritten)

/-- Prints the lines and goes on. A line that cannot be printed ends the call. -/
def sayThen : List String → Ask End → Ask End
  | [], next => next
  | l :: ls, next => .say l fun ok =>
    match ok with
    | true => sayThen ls next
    | false => unwritten

/-- Writes the words to standard error and goes on. -/
def errThen : List String → Ask End → Ask End
  | [], next => next
  | l :: ls, next => .err l (errThen ls next)

/-- Prints the lines, then the end's own line, and ends. -/
def close (w : String) (pre : List String) (e : End) : Ask End :=
  sayThen pre (.say (e.line w) fun ok =>
    match ok with
    | true => .done e
    | false => unwritten)

/-- What follows on the answer to the read of the file w. -/
def afterRead (word : String) (w : Want) (next : ByteArray → Ask End) : FileRead → Ask End
  | .bytes b => if b.size ≤ w.cap then next b else close word [] (.tooLong w.path)
  | .absent => close word [] (.unread w.path)
  | .unreadable _ => close word [] (.unread w.path)

/-- Reads the files in their order, each with one byte more than it may have, and goes on with
their bytes. -/
def readAll (word : String) : List Want → (List ByteArray → Ask End) → Ask End
  | [], k => k []
  | w :: ws, k =>
    .read w.path (w.cap + 1) (afterRead word w fun b => readAll word ws fun l => k (b :: l))

/-- The program, once the arguments are read. -/
def progAt (B : Body) : Option (B.A × List Want) → Ask End
  | none => .err B.usage (.done .usage)
  | some (a, ws) => readAll B.word ws fun bs =>
    let r := judged B a bs
    errThen r.2.aside (close B.word r.1 r.2)

/-- The program as a value. -/
def prog (B : Body) (args : List String) : Ask End := progAt B (B.ask args)

/-- The program in IO, and its exit code. -/
def mainOf (B : Body) (args : List String) : IO UInt32 := do
  let e ← tryCatch ((prog B args).run opsIO) fun _ => pure End.fault
  return e.code

end OnBytes.ShellOf
