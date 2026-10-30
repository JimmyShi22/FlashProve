-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/ArmAt.lean: THE ENTRY FILE: TWO STATEMENTS ON ONE CHECKER, at two sizes, with one
hypothesis. AT THE WAY OF READING THE FILES THAT THE FIRST USES THE SECOND SAYS NEXT TO NOTHING, AND
NO THEOREM CARRIES THE PROBABILITY TO THE PROGRAM's YES.

 `entry_arm_small`, `entry_arm_full`: `EntryArm` (OnBytes/K/Left/Arm.lean) holds at the small
     example's and at the full size's typed parameters, under `Cb.BCHKS46At GF GE` alone. The left
     half, which Arm.lean takes as a hypothesis, is a theorem here (`left_small`, `left_full`,
     OnBytes/K/Left/LaxDone.lean).

In plain words. (1) If a call of this tree's Lean verifier program ends with exit code 0, it was a
call to verify, with an ID, that read certain files; and if the parameter file among them has the
setting's lines, then a second checker, at the converter that goes through the program's own reader,
returns a typed value on that call's own key file and entry file, under the oracle made from the
format's hash; the value's two roots and both tables' answers are those of the two tables of the
program's own yes, and the user's ID in its normal form is the commitment ID of its first root,
first seeds and first answers. (2) The public files, the converter and the maker are fixed first;
then, over one uniformly random oracle, a maker of files with at most 2^64 queries gets that checker
to return a value of which the entry's language fails with probability at most 2^-61. And it is one
checker: files with a log lie in the event of (2), taken at the format's hash, if and only if the
checker of (1), at that converter, returns on them a value of which the language fails, read off
that log; that is no third result: it holds by unfolding, with no hypothesis.

Read the head of Arm.lean before citing this. NO BOUND STANDS ON THE PROGRAM's OWN CHECK, AND NO
PROBABILITY IS SAID OF ITS YES: (1) is at one fixed hash, (2) over a drawn oracle; at the converter
of (1) itself (2) says next to nothing. ONE file of three; a checker made by a second form of the
compiler, with a hand-written step for the seeds; not `innerCompiledVerifier`. Only (2) uses the
hypothesis on codes. The figure is a ceiling of this bound, with 32 of 128 bits counted as proof of
work. Nothing is said where the first table does not decode or its record does not single one table
out. The ID stands in (1) alone. That a parameter file has the setting's lines is a decidable
equation on that file; it is evaluated here of no file (OnBytes/K/Left/TestSaysLines.lean proves it
of copies of the first 32 lines of two example parameter files, and SaysLinesPrefix.lean of every
byte string that begins with one of these copies). No call is shown to end with exit code 0, which
is given for `YES` and for `WITHIN LIMITS` alike. Nothing on hiding.

Beside that: these theorems are no instance of `InnerCompilerInput`. That (2) says next to
nothing at the converter of (1) is a reading of that converter's text, no theorem; (2) has its force
at a converter that only parses, which is not written (OnBytes/K/Oracle/ArmOAt.lean has the two
statements for a checker whose reader asks the oracle). (2) concludes of strings read off a maker's
log; in (1) there is no maker and no log. Without the key file's part nothing follows from the entry
file's. The work stands at 6 of the 41 rounds and at 4 of the 24; the figure is no level of security
of any program.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Arm
import OnBytes.K.Left.LaxDone

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie (recordGround smallRecordGround)
open OnBytes.Slice (GE GF)
open TypedOracleCompiler.Slice

/-- The two ways of writing the left half are one. -/
theorem entryLeft_of_at (G : OnBytes.Tie.EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (z : Params.StdSize) (h : EntryLeftAt G hok z) : EntryLeft G hok z := h

/-- **`EntryArm` at the small example.** One hypothesis: the statement on codes. -/
theorem entry_arm_small (hA : Cb.BCHKS46At GF GE) :
    EntryArm smallRecordGround homeSmall (convSmall false) 101 :=
  entry_arm_of_left_small hA (entryLeft_of_at _ _ _ left_small)

/-- **`EntryArm` at the full size.** One hypothesis: the statement on codes. -/
theorem entry_arm_full (hA : Cb.BCHKS46At GF GE) :
    EntryArm recordGround (homeOf recordGround record_ok Params.recordRadius)
      (convPlay recordGround record_ok Params.recordRadius false) 142 :=
  entry_arm_of_left_full hA (entryLeft_of_at _ _ _ left_full)

end OnBytes.K.Left
