-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/ProgramGuard.lean: five checks of Johnson/PVR/Program.lean. They are made whenever the
library is built. Each of (1) to (4) can fail, and then this file does not compile.

(1) `#guard_cone` walks all constants that `PV.Program.run` uses, by the kernel's terms, and lists
those whose compiled code is not made from the definition that the kernel checked (the kinds: the
head of OnBytes/Guard/Cone.lean), in three groups: Lean's core and Std; Mathlib and the packages;
this library. It fails if this library's group holds any. The first two groups are listed and not
judged: some 180, five of them Mathlib's stand-ins for the recursors of Bool, List,
Option, PSum and Sum, which Mathlib puts in by rules for the compiler without a proof
(OnBytes/Guard/Allow.lean). A constant that such a rule replaces is followed, not listed, and the
rules are not checked here: the command that checks them (OnBytes/Guard/Csimp.lean) is not called.
(2) `#guard_has`: the parts that matter stand in that cone: the reader of the claim, the executable
form, the format's hash.
(3) `#guard_ctors`: of `IO.FS.Mode`'s five constructors that cone holds `read` alone (see the foot).
(4) Known answers of `claimOf` on made-up bytes (`#guard`): where it cuts a request, and what it
refuses. They are tests at a few values, not theorems.
(5) The axioms beneath four theorems are printed: `verdictOf_is_verify`, `verdictAt_eq`,
`verdictOf_map`, `verdictOf_eq`. Nothing fails by it.

Limits. Of the fifteen guard commands that OnBytes/Guard/Program.lean holds over
`verify-on-bytes`, three are called here (which, and what the others would hold: the foot). The walk
follows the kernel's terms, not the compiler's output; the number of constants that it saw is
printed, not held. The entry's three lines (tools/lean-verify/LeanVerify.lean) lie outside the
library and outside this cone. Nothing here speaks of Lean's compiler, interpreter or runtime.
-/
import Johnson.PVR.ProgramTotal
import OnBytes.Guard.Core

set_option autoImplicit false

#guard_cone [``PV.Program.run] []
#guard_has [``PV.Program.run] [``PV.Program.claimOf, ``PV.Program.stepsOf, ``PV.Program.verdictAt,
  ``PV.Front.idOf, ``PV.Front.userOf, ``PV.Ride.rideOf, ``PV.Ride.verdictThe, ``Fmt.oracle]
#guard_ctors [``PV.Program.run] ``IO.FS.Mode [``IO.FS.Mode.read]

namespace PV.Program.Known
open VerifiableInference

/-- A word of 32 bits, the lowest byte first. -/
def w32 (n : Nat) : ByteArray :=
  ⟨#[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]⟩

/-- Words, one after the other. -/
def words (l : List Nat) : ByteArray := l.foldl (fun b n => b ++ w32 n) ByteArray.empty

/-- T made-up tokens, all different, some above 2 ^ 16. -/
def toks : List Nat := (List.range T).map fun i => 131 * i + 3

/-- A request file: the tokens, then r and e. -/
def req (r e : Nat) : ByteArray := words (toks ++ [r, e])

/-- 64 hex digits in lower case: 32 bytes, no two alike. -/
def hex64 : String := "00112233445566778899aabbccddeeff0123456789abcdeffedcba9876543210"

/-- A call with these three files of the user's and nothing else. -/
def given (id rq y : ByteArray) : Given :=
  ⟨.empty, .empty, .empty, id, rq, y, .empty, .empty, .empty, .empty, .empty⟩

/-- Prompt, output and further tokens, as `claimOf` cuts them, at a good ID. -/
def cut (rq y : ByteArray) : Option (List Token × List Token × List Token) :=
  (claimOf (given (hex64 ++ "\n").toUTF8 rq y)).map fun c => (c.prompt, c.output, c.further)

/-- The commitment ID in hex, as `claimOf` reads it, at a good request. -/
def idAt (id : ByteArray) : Option String :=
  (claimOf (given id (req 2 5) (w32 0))).map fun c =>
    PV.Front.hex (_root_.Run.digToBytes c.commitment)

end PV.Program.Known

open PV.Program PV.Program.Known in
section
-- where it cuts
#guard cut (req 2 5) (w32 0) == some (toks.take 3, (toks.drop 3).take 3, toks.drop 6)
#guard cut (req 0 1) (w32 0) == some (toks.take 1, (toks.drop 1).take 1, toks.drop 2)
#guard cut (req 23 T) (w32 77) == some (toks.take 24, toks.drop 24 ++ [77], [])
#guard cut (req (T - 1) T) (w32 77) == some (toks, [77], [])
#guard cut (req 23 (T - 1)) (w32 0) == some (toks.take 24, toks.drop 24, [])
-- what it refuses: tests 1 to 4 of the format page
#guard cut (req 2 5) (w32 1) == none
#guard cut (req 5 5) (w32 0) == none
#guard cut (req 6 5) (w32 0) == none
#guard cut (req 2 (T + 1)) (w32 0) == none
#guard cut ((req 2 5).extract 0 (4 * (T + 2) - 1)) (w32 0) == none
#guard cut (req 2 5 ++ ⟨#[0]⟩) (w32 0) == none
#guard cut (req 2 5) ((w32 0).extract 0 3) == none
#guard cut (req 2 5) (w32 0 ++ ⟨#[0]⟩) == none
#guard cut ByteArray.empty ByteArray.empty == none
-- the commitment ID's file
#guard idAt hex64.toUTF8 == some hex64
#guard idAt (hex64 ++ "\n").toUTF8 == some hex64
#guard idAt (hex64.toUpper ++ "\n").toUTF8 == none
#guard idAt (hex64 ++ "\r\n").toUTF8 == none
#guard idAt (hex64 ++ "a").toUTF8 == none
#guard idAt (hex64.drop 1).toString.toUTF8 == none
#guard idAt ("g" ++ (hex64.drop 1).toString).toUTF8 == none
#guard idAt ByteArray.empty == none
end

#print axioms PV.Program.verdictOf_is_verify
#print axioms PV.Program.verdictAt_eq
#print axioms PV.Program.verdictOf_map
#print axioms PV.Program.verdictOf_eq

/-
The foot of this file. Which three, and what the others would hold. By the numbers of
OnBytes/Guard/Cmd.lean and OnBytes/Guard/Core.lean, called here: 2 `#guard_cone`, 6 `#guard_has`,
10 `#guard_ctors`. The other twelve are not called, so what they hold over `verify-on-bytes` is not
held over `PV.Program.run`. Six of them: 1, that every rule for the compiler on record is a theorem
that depends only on the three standard axioms; 3, that no constant of a package in the cone has
compiled code that is not made from its definition (here five of Mathlib's have; they are listed,
not judged); 4, the same, for this library's constants too, by the declarations from which the C
files are written, and that these call no function of the library or a package that the kernel's
terms do not name; 5, that Lean core's such constants are exactly those of a closed list (here some
180 are listed, not judged); 13, that the compiled declarations that call back into their own
recursion, otherwise than by a last call to themselves, are those of two closed lists; 14, that no
module with a barred name is imported. The other six (7, 8, 9, 11, 12, 15): the head of
OnBytes/Guard/Core.lean.
What (3) holds, and what not. `#guard_ctors` looks at one type, `IO.FS.Mode`. A call that changes
the disk or starts a program without naming a mode (for instance `IO.FS.removeFile`, `IO.FS.rename`,
`IO.FS.createDir`, `IO.FS.createTempFile`, `IO.Process.spawn`) does not show there. It would stand
in the first group of (1), which is printed and not judged. That `run` makes no such call is read
off its text (Johnson/PVR/Program.lean); no check here holds it. And the walk stops at Lean core's
leaves: what the C code calls that stands in for a core constant, and what a core function calls
that Lean took without a proof that it ends, is not walked (the head of OnBytes/Guard/Cone.lean,
"What it does not reach"): a mode that is named there does not show either.
-/
