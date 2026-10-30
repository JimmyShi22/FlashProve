-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1Run.lean: the first toy at tiny sizes, on 73 files of this library's own: which component is
to give the verdict on each file, and what the two file readers do with them.

The first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i; Fmt/M1Types.lean).
On the way through the compiled verifier a file first meets a file reader and then the verifier.
This file says, for each of 73 files, which of the two is to refuse it, from the table that came
with the files. It holds definitions that compute, with tests. It is generic in the run function:
no compiled verifier is run here.

Sources. The files (Fmt/M1Files.lean, Fmt/M1FilesB.lean: two sizes; 34 and 39 files) are this
library's own. They were made outside Lean by a reference program of this library's own, at an
edition of the format page that is not the one that ships (docs/format/FORMAT.md, which comes with
the programs, the C++ implementation that comes with this Lean code; this file is not held against
the page that ships). Each bad file comes with the part of the toy's decision that refuses it first
in that reference: 1 form, 2 work, 3 openings, 4 and 5 the last block's two checks.

1. What the file contains.
   `Runner`: a run function: from a description, a decision on the view and a file to the outcome
     (Run/PlanQRun.lean: limits, reader, verifier, accepted).
   `wantStrict`: behind the strict reader, which tests form, work and openings itself: 0 gives
     accepted; 1, 2, 3 the reader; 4, 5 the verifier.
   `wantLax`: behind the lenient reader, which only splits the file: 0 gives accepted; 1 the
     reader; 3, 4, 5 the verifier (there it must refuse a false opening itself); 2 the reader, but
     the verifier for a file whose name begins with "recut" (made anew behind a nonce that fails:
     see the gap below). To cut the file, the lenient reader recomputes the hash chain, and it
     refuses some files (what it still asks the hash, what it refuses and what it does not test:
     part 1 of the head of Run/ParseLax.lean).
   `wantLaxAt luck`, `luckOK`: `wantLax` with a fixed list of exceptions by name. The rule "part 2,
     not re-cut: the reader; part 3: the verifier" is a matter of luck for a file in which a byte
     of a message is altered: the draws behind it change, and whether the work then fails, and
     whether the file can still be split, depends on the bytes (seen at the sets made at an edition
     of the format page that is not the one that ships). An exception names such a file and says
     "the reader" or "the verifier", never "accepted".
   `wrong run want S P files`: the test to be stated for it is "wrong .. = []".
   `bareStrict`, `bareLax`: two run functions without a compiled verifier.

2. What is checked when the file compiles (with the format's hash; no compiled verifier).
   The strict reader reads the honest files and all files of parts 4, 5, and none of parts 1, 2, 3.
   The lenient reader reads the honest files and all files of parts 3, 4, 5, and none of parts 1,
   2. `bareStrict` gives the wanted outcome on all 73 files.
   `bareLax` accepts two bad files of part 3 at each size (alt-05, alt-06: by the files' table a
   byte of a salt and a byte of a given digest; neither enters a symbol). On these four files the
   decision does not refuse. By the way they were made, what is left to refuse them is the compiled
   verifier's own walk through the openings: they are meant as the test of that walk. The two other
   files of part 3 are refused by the decision too.

3. Theorems. None.

4. What is not claimed, and a gap.
   A gap in these 73 files: none makes the compiled verifier's own test of the work the one that
   refuses. In the three files of part 2 at each size a byte is altered before a round with work.
   Behind it the chain draws other positions, the openings in the file no longer have the length
   that these positions ask for, and the lenient reader cannot split the file. A file for that test
   has to be made anew behind the altered place (a nonce that fails, and all that follows by the
   honest rules). This library's own reference has made such files, under names that begin with
   "recut"; they are not among the 73.
   No run of the compiled verifier: that is for a file that puts a run function into "wrong"
   (Run/M1RunS.lean, with `runStrictS`, `runLaxS` of Run/PlanQS.lean).
   No file of the programs is looked at here.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQRun
import Fmt.M1Tiny

set_option autoImplicit false

namespace Run.M1Run
open _root_.Fmt.M1 Run.PQ

/-- a run function: from a description, a decision on the view and a file to the outcome -/
abbrev Runner : Type := _root_.Fmt.Spec → (_root_.Fmt.View → Bool) → ByteArray → Who

/-- the table's parts as numbers 1 .. 5; 0: accepted -/
def partA : Option Files.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

def partB : Option FilesB.Dn → Nat
  | none => 0
  | some .d1 => 1
  | some .d2 => 2
  | some .d3 => 3
  | some .d4 => 4
  | some .d5 => 5

/-- name, bytes, the table's part -/
def filesA : List (String × ByteArray × Nat) := Files.files.map fun x => (x.1, x.2.1, partA x.2.2)
def filesB : List (String × ByteArray × Nat) := FilesB.files.map fun x => (x.1, x.2.1, partB x.2.2)

/-- the wanted outcome behind the page's own reader (in the head: the strict reader); the file's
name is not looked at -/
def wantStrict (_ : String) (part : Nat) : Who :=
  if part = 0 then .accepted else if part ≤ 3 then .reader else .verifier

/-- the wanted outcome behind the lenient reader. A file of part 2 whose name begins with "recut"
is made anew after a nonce that fails: it can be split, and the verifier's own test of the work is
to refuse it -/
def wantLax (name : String) (part : Nat) : Who :=
  if part = 0 then .accepted
  else if part = 1 then .reader
  else if part = 2 then (if name.startsWith "recut" then .verifier else .reader)
  else .verifier

/-- the wanted outcome behind the lenient reader, with a fixed list of exceptions. Where a byte of
a message is altered, the chain after it draws other values: whether the next test of work fails
(part 2) or passes by luck (then part 3: the openings), and whether the openings in the file still
have the lengths that the new positions ask for (so that the lenient reader can split the file),
depends on the bytes. For such files the outcome is fixed by name -/
def wantLaxAt (luck : List (String × Who)) (name : String) (part : Nat) : Who :=
  (luck.lookup name).getD (wantLax name part)

/-- the conditions on a list of exceptions: each names a file of the set, of part 2 or 3, not
re-cut; the outcome is the reader or the verifier: never "accepted" -/
def luckOK (luck : List (String × Who)) (files : List (String × ByteArray × Nat)) : Bool :=
  luck.all fun e =>
    (e.2 == .reader || e.2 == .verifier) && !e.1.startsWith "recut" &&
      files.any fun x => x.1 == e.1 && (x.2.2 == 2 || x.2.2 == 3)

/-- the files on which a run function does not give the wanted outcome: name, the outcome, the
wanted outcome -/
def wrong (run : Runner) (want : String → Nat → Who) (S : _root_.Fmt.Spec) (P : Par)
    (files : List (String × ByteArray × Nat)) : List (String × Who × Who) :=
  files.filterMap fun x =>
    if run S (dec P) x.2.1 = want x.1 x.2.2 then none
    else some (x.1, run S (dec P) x.2.1, want x.1 x.2.2)

def laxReads (S : _root_.Fmt.Spec) (b : ByteArray) : Bool :=
  (laxWhole (m := Id) _root_.Fmt.formatHash S b).isSome
def strictReads (S : _root_.Fmt.Spec) (b : ByteArray) : Bool :=
  (_root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash S b).isSome

/-- for each part 0 .. 5: how many files the table puts there, and how many of them a reader
reads -/
def tally (reads : ByteArray → Bool) (fs : List (String × ByteArray × Nat)) : List (Nat × Nat) :=
  (List.range 6).map fun d =>
    ((fs.filter fun x => x.2.2 == d).length, (fs.filter fun x => x.2.2 == d && reads x.2.1).length)

#guard tally (strictReads Known.spec) filesA = [(1, 1), (3, 0), (3, 0), (4, 0), (20, 20), (3, 3)]
#guard tally (strictReads KnownB.spec) filesB = [(1, 1), (3, 0), (3, 0), (4, 0), (23, 23), (5, 5)]
#guard tally (laxReads Known.spec) filesA = [(1, 1), (3, 0), (3, 0), (4, 4), (20, 20), (3, 3)]
#guard tally (laxReads KnownB.spec) filesB = [(1, 1), (3, 0), (3, 0), (4, 4), (23, 23), (5, 5)]
-- "wrong" sees a run function that always accepts and one that always lets the verifier refuse
#guard (wrong (fun _ _ _ => .accepted) wantLax Known.spec Known.par filesA).length = 33
#guard (wrong (fun _ _ _ => .verifier) wantLax Known.spec Known.par filesA).length = 7
#guard (wrong (fun _ _ _ => .verifier) wantStrict Known.spec Known.par filesA).length = 11
#guard wantLax "alt-01" 2 = .reader ∧ wantLax "recut-16" 2 = .verifier ∧ wantStrict "recut-16" 2 = .reader
#guard wantLaxAt [("alt-01", .verifier)] "alt-01" 2 = .verifier ∧ wantLaxAt [("alt-01", .verifier)] "alt-02" 2 = .reader ∧ wantLaxAt [] "alt-04" 3 = .verifier
#guard luckOK [("alt-01", .verifier)] filesA ∧ !luckOK [("alt-01", .accepted)] filesA ∧ !luckOK [("honest", .reader)] filesA ∧ !luckOK [("no such file", .reader)] filesA

/-- run functions without a compiled verifier, to try how the parts are put together: a reader,
then the decision on the view -/
def bareStrict : Runner := fun S d b =>
  match _root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash S b with
  | none => .reader
  | some o => if d (_root_.Fmt.viewOf S.firstTree o) then .accepted else .verifier

def bareLax : Runner := fun S d b =>
  match laxWhole (m := Id) _root_.Fmt.formatHash S b with
  | none => .reader
  | some o => if d (_root_.Fmt.viewOf S.firstTree o) then .accepted else .verifier

-- behind the strict reader the decision alone says what is wanted, on all files of both sizes
#guard wrong bareStrict wantStrict Known.spec Known.par filesA = [] ∧ wrong bareStrict wantStrict KnownB.spec KnownB.par filesB = []
-- behind the lenient reader the decision alone accepts two bad files of each size (see the head, 2)
#guard (wrong bareLax wantLax Known.spec Known.par filesA).map (fun x => (x.1, x.2.1)) = [("alt-05", .accepted), ("alt-06", .accepted)]
#guard (wrong bareLax wantLax KnownB.spec KnownB.par filesB).map (fun x => (x.1, x.2.1)) = [("alt-05", .accepted), ("alt-06", .accepted)]
-- the library's own run function has a Runner's type (it cannot be run at this toy: most rounds
-- draw field elements; see Run/PlanQRun.lean, the head, 4)
-- (That head: it cannot be run by a test (#guard). Run/PlanQS.lean writes the construction again
-- in a form that can be evaluated: its `runStrictS`, `runLaxS` are run at this toy in
-- Run/M1RunS.lean.)
example : Runner := runLax
example : Runner := runStrict

end Run.M1Run
