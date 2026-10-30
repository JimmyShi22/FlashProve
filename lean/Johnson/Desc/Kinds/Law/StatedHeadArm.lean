-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/StatedHeadArm.lean (with the three reads of the planes in
truth): THE OUTPUT HEAD'S ARM OF THE STATED DATA: one term of the type that the dispatcher of the
table's letter St asks of each kind (Johnson/Desc/Sound/StatedAll.lean: uBySort uL uA uH; the arm's
type: the link's number to a stated function), off the public parameters and the link's number
alone.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  nuK6 X: THE LOOKUP'S PLACES AT THE HEAD, OFF THE DATA: a mask entry j below the number of slots:
      the data's mask row's entry; a cell (r, c): the cast of segment 24's own integer at the
      planes' matrix (number NHf + 2 of the list) behind the data's symbols (Law/CellsOfData.lean:
      symD); every other place, and a mask entry from the number of slots on: 0.
  p8K6 X l: the parameters of the quiet step that makes the head's tables at piece 5 of link l.
  uHeadK6 X l: the stated reads with the planes' three (Law/K6StatedPlanes.lean:
      statedAll) at the parameters of the quiet step that makes the head's tables at piece 5 of link
      l, at the head's integer cells made of the data (cellsOfData at Meaning.sizesOf X), at the
      planes' matrix's logarithm of rows and nuK6.

What it says, in words: at a column of the array of the reads (row 0): run the quiet step that makes
the tables silently on the verifier's state; find the table in whose stretch the column lies; the
value is that table's read IN TRUTH: at the twelve reads of the head's own relation: K6's
own sum over the integer cells, at the kind's own weights; at the three reads of the planes: the
lookup library's own column sums at what the lookup heard, over nuK6. 0 where the step rejects,
where the kind's letters cannot be had, or where the column lies in no table's stretch.

Every letter under "there is": none.
What it does not say. THAT THIS VALUE IS THE SUM IN WHICH THE TIE OF THE APPROXIMATE RANGE PROOF
SPEAKS (over the tables' own weights and the unpacked symbols): NOT BY UNFOLDING at the twelve: it
is K6's law on the twelve reads (Law/TwelveOurs.lean, under RunIs): not called here. That
the tables which the silent step makes are those that the state holds behind the sub-protocol at
piece 5. Nothing on soundness.
-/
import Johnson.Desc.Sound.StatedAll
import Johnson.Desc.Kinds.Law.K6StatedPlanes
import Johnson.Desc.Kinds.Law.CellsOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound)

/-- **The lookup's places at the head, off the data.** -/
def nuK6 (Wp : OnBytes.Model.Verify.Public) : S → Bound Cb.Gl.E → _root_.Fo.Pl → Cb.Gl.E :=
  fun _ D pq =>
    match pq with
    | .mask j => if j < Wp.H.ns then D.mask j else 0
    | .cell r c => ((Meaning.ownOf (Meaning.sizesOf Wp) (symD Wp (Meaning.sizesOf Wp) D) 24
        (Wp.hS.NHf + 2) r c : Int) : Cb.Gl.E)
    | _ => 0

/-- The parameters of the quiet step that makes the head's tables at piece 5 of link l. -/
def p8K6 (X : OnBytes.Model.Verify.Public) (l : Nat) : K8.ReadsQuiet.PH :=
  ⟨⟨1, some l, 5, .K1⟩, X.hS, X.HLy, X.H⟩

/-- **The output head's arm of the stated data.** -/
def uHeadK6 (X : OnBytes.Model.Verify.Public) : Nat → Sound.UFn :=
  fun l => statedAll X (p8K6 X l)
    (fun _ D => cellsOfData X (Meaning.sizesOf X) D) X.hS.lmbH (nuK6 X)

end VerifiableInference.Desc.Kinds.Head.Law
