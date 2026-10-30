-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneWorldEntry.lean: pieces at an entry file for the checker on bytes over one oracle:
one description for all names, and that the chain's reader is the same at `Run.oBits` and at the
format's own oracle.



OnBytes/Slice/OneWorldTop.lean states a bound, under one random oracle, for a checker `chainChk` of
one chain that opens two stored tables; its head says what the experiment is and what is read off
the maker's queries.





Main definition: `entryS0`.
Main theorems.
- `reStated_entryS0`: `entryS0` with a statement put in is the description with that statement.










- `readerAt_oBits`: at the one fixed oracle `Run.oBits`, which the library
  makes from the format's hash, the chain's reader is that at the
  format's own oracle.



What is not claimed. `one_world_at` and the theorem at `Run.oBits` stand side by side and
are not one statement. The first is on an oracle that is drawn at random; the other is on one
fixed oracle, with no probability. No probability is stated of the program, of `Entry.check` or of
BLAKE2b, and the event in the bound speaks of the maker's queries, which have no meaning at a fixed
hash or for a file on a disk. That a bound under a random oracle says anything of a fixed hash is an
assumption that this file does not state and does not use.
That `entryS0` is within the limits (`withinX`) is proved here of no parameters.













That `Entry.check` says yes on any file is not shown.


One chain of the seven of a whole call; an entry file is the committer's file: no request and no
reply. The key is not checked: both roots are the maker's choice and are tied to nothing published.

All limits in the heads of OnBytes/Slice/OneWorldTop.lean,
OnBytes/Slice/OneWorld.lean, OnBytes/Tie/EntryAt.lean and OnBytes/Tie/EntryPre.lean hold here too.
Nothing is said of the C++ program `cp_verify` or of how its results compare. For proofs only; the
program does not import this file.

-/
import OnBytes.Slice.OneWorldTop
import OnBytes.Tie.EntryAt
import OnBytes.Tie.EntryPre
import OnBytes.Slice.RootsInAt

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (xdOf inFile withinX StmInv CompiledAcceptsXAt pinned readInAt readAskR
  readAskR_det bareStatement EntryPlace readerAt)

/-- One description for all names: that of an entry's chain at the parameters p and the rounds rs,
with a fixed string x0 as its statement. The statement of the two roots goes in its
place (`reStated`), and that description does not hang on x0 (`reStated_entryS0`). The tests
`withinX` and `Run.PQ.fourBounds` of `entryS0` do hang on it: they
read the length of x0. x0 is a parameter so that a theorem on the description at some statement can
be used as it stands. -/
def entryS0 (p : Params.Link) (rs : Params.Rounds) (x0 : ByteArray) : Fmt.SpecX :=
  Params.entrySpecOf p rs x0

/-- `entryS0` with a statement put in is the description with that statement, whatever x0 is. -/
theorem reStated_entryS0 (p : Params.Link) (rs : Params.Rounds) (x0 x : ByteArray) :
    reStated (entryS0 p rs x0) x = Params.entrySpecOf p rs x := rfl

/-- The chain's reader at the function that `Run.oBits` induces on byte strings is the reader at the
format's own oracle: the hashes that the pinned forms of the two functions induce are the same
(`Tie.HO_pinned_oBits`). That the two functions themselves agree is not stated. -/
theorem readerAt_oBits : readerAt (oB (oBits ())) = readerAt Fmt.oracle := by
  funext S b i
  unfold readerAt readInAt
  rw [Tie.HO_pinned_oBits]

end OnBytes.Slice
