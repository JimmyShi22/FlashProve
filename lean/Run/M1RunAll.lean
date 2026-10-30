-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunAll.lean: for the programs' own proof files of the first toy: eight run functions for the
compiled verifier in one list, and which component may give the verdict on a file.

The programs (the C++ implementation that comes with this Lean code) delivered proof files of the
first toy (a product test): honest proofs, altered copies and false proofs. With each bad file came
the reason why the programs' two verifiers refuse it; for the false proofs it was written down
before they were made. This file lists eight ways in which this library runs the compiled verifier
on a file (there are further functions of the same type in Run/PageQRun.lean, Run/PageQRunC.lean,
Run/PageQFull.lean and Run/PlanQRun.lean), and derives from those reasons which component (the file
reader or the verifier) may be the one that refuses. It holds definitions that compute, with tests
on the definitions. No file is run here.

1. What the file contains.
   `Road`, `roads`: a run function: its name; whether its file reader is the strict reader (this
     library's rendering of the format page's verifier up to its decision: it checks form, work and
     openings
     itself) or a lenient reader (it only cuts the file into its parts, and refuses a file that
     cannot be cut; to cut the file it recomputes the hash chain (what it still asks the hash, what
     it refuses and what it does not test: part 1 of the head of Run/ParseLax.lean); it tests no
     proof of work, walks no path and compares no root: behind it the compiled verifier makes these
     three checks itself); and the function itself. Of `runFullSP` and `runFullS`: the reader that
     fills in whole paths (`fullWhole`, Run/ParseFull.lean) does more: it also hashes the opened
     leaves and walks up each tree; it tests no proof of work and compares no root. There are
     eight, all of the type `Run.M1Run.Runner`. Over one oracle on bit strings, through the
     encoding of the queries: `run1PF` (challenges as hash blocks, `ckP`) and `run1K` (challenges
     as sampled values, `ck`). These are two choices of what a round's verifier message is: as
     sampled values (`ck`: the values that the format draws, field elements and positions among
     them) or as hash blocks (`ckP`: the round's 256-bit blocks themselves; reads and decision
     apply the sampling rule). At typed oracle functions, with pruned openings: `runLaxSP`,
     `runStrictSP` (hash blocks) and `runLaxS`, `runStrictS` (sampled values). At typed oracle
     functions, with whole authentication paths: `runFullSP` (hash blocks) and `runFullS` (sampled
     values).
   `may strict part`: the part is the part of the toy's decision that refuses the file first in the
     programs' two verifiers (for a false proof: the part that the programs' list of expectations
     names, written before the proof was made: Fmt/M1ProgPTFiles.lean, `table`); 0 is the honest
     proof; for 6 see below.
     0: accepted. 1 (form): the reader. 3 (openings): behind the strict reader, the reader; behind
     a lenient one, the verifier. 4, 5 (the last block's two checks): the verifier.
     2 (work): behind the strict reader, the reader. Behind a lenient reader, the reader or the
     verifier: a byte altered before a round with work changes the hash chain; other positions are
     drawn; the openings in the file may or may not have the length that these positions ask for.
     6: the altered copy in which the last round's shown word is changed. It fails the linear check
     and also that round's test of the work. The programs' verifiers make the linear check first;
     by their own note, a verifier that asks every query first meets the work. So: behind the
     strict reader, the reader; behind a lenient one, the reader or the verifier.
   `amiss road S P files`: the test to be stated for a run function is "amiss .. = []".
   `voices`: meant to be fixed in a test.

2. What is checked when the file compiles. Tests (#guard) on these definitions only.

3. Theorems. None.

4. What is not claimed. Nothing is run here. Which part a file has is a matter of the tables that
came with the files.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.M1Run
import Run.PlanQSP
import Run.PlanQSFP
import Run.PageQKeepC

set_option autoImplicit false

namespace Run.M1RunAll
open _root_.Fmt.M1 Run.PQ Run.M1Run

structure Road where
  name   : String
  strict : Bool
  run    : Runner

/-- The eight run functions. -/
def roads : List Road :=
  [⟨"run1PF", false, run1PF⟩, ⟨"run1K", false, run1K⟩,
    ⟨"runLaxSP", false, runLaxSP⟩, ⟨"runStrictSP", true, runStrictSP⟩,
    ⟨"runLaxS", false, runLaxS⟩, ⟨"runStrictS", true, runStrictS⟩,
    ⟨"runFullSP", false, runFullSP⟩, ⟨"runFullS", false, runFullS⟩]

/-- Which components may give the verdict. -/
def may (strict : Bool) (part : Nat) : List Who :=
  match part with
  | 0 => [.accepted]
  | 1 => [.reader]
  | 2 => if strict then [.reader] else [.reader, .verifier]
  | 3 => if strict then [.reader] else [.verifier]
  | 6 => if strict then [.reader] else [.reader, .verifier]
  | _ => [.verifier]

/-- the files on which a run's verdict comes from none of the components that may give it -/
def amiss (R : Road) (S : _root_.Fmt.Spec) (P : Par) (files : List (String × ByteArray × Nat)) :
    List (String × Who) :=
  files.filterMap fun x =>
    if (may R.strict x.2.2).contains (R.run S (dec P) x.2.1) then none
    else some (x.1, R.run S (dec P) x.2.1)

/-- who gave the verdict, file by file -/
def voices (R : Road) (S : _root_.Fmt.Spec) (P : Par) (files : List (String × ByteArray × Nat)) :
    List (String × Who) :=
  files.map fun x => (x.1, R.run S (dec P) x.2.1)

/-- no file of a part other than 0 is accepted -/
def neverAccepts (R : Road) (S : _root_.Fmt.Spec) (P : Par)
    (files : List (String × ByteArray × Nat)) : Bool :=
  files.all fun x => x.2.2 == 0 || R.run S (dec P) x.2.1 != .accepted

#guard roads.map (fun R => (R.name, R.strict)) = [("run1PF", false), ("run1K", false), ("runLaxSP", false), ("runStrictSP", true), ("runLaxS", false), ("runStrictS", true), ("runFullSP", false), ("runFullS", false)]
-- "accepted" may be said of the honest proof alone; of it nothing else may be said
#guard (List.range 8).all fun p => [true, false].all fun s => ((may s p).contains .accepted) == (p == 0)
#guard may true 0 = [.accepted] ∧ may false 0 = [.accepted]
-- "limits" may never be said
#guard (List.range 8).all fun p => [true, false].all fun s => !(may s p).contains .limits
-- amiss sees a road that always accepts, and one that always lets the reader refuse
#guard (amiss ⟨"", false, fun _ _ _ => .accepted⟩ Known.spec Known.par [("a", ByteArray.empty, 0), ("b", ByteArray.empty, 4), ("c", ByteArray.empty, 2)]).map (·.1) = ["b", "c"]
#guard (amiss ⟨"", false, fun _ _ _ => .reader⟩ Known.spec Known.par [("a", ByteArray.empty, 0), ("b", ByteArray.empty, 4), ("c", ByteArray.empty, 2), ("d", ByteArray.empty, 3)]).map (·.1) = ["a", "b", "d"]

end Run.M1RunAll
