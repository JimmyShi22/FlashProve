-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawReads.lean: THE SMALLNESS TEST: "THE SENT READS ARE THE TRUE ONES": THE
STATEMENT, AT THE BOUNDARY IN FRONT OF THE DRAW.

The row: each entry of the committed vector of reads that a kind's form names is the stated function
of the committed cells. Other kinds spend it: their forms read entries of that vector where they
mean weighted sums of cells.
WHERE IT IS HAD. It is a clause of what stands at the boundary IN FRONT OF the draw of the matrix
(behind the commitment to the reads): the proved block's first joint (Cb/Pv/Tail/Block.lean:
`relIn`; as named cells: `CellsOK`, Cb/Pv/Tail/Cells.lean). Knowledge soundness runs backward:
whoever has a witness of what stands BEHIND the draw (digits in their tables that meet every tie and
every read at the drawn matrix) has, but for the round's error, a witness of what stands in front:
that is `piece_good` (Johnson/Desc/First/K8/LawPiece.lean). So the row is paid in two steps: this
unfolding, and the road from the batching's challenge back to the boundary behind the draw (the
test's equations: the kind's second half, other files').
  `Reads.reads_are_true`: of what stands at the chain's boundary in front of the kind's block
    (`Reads.relA`): the messages of which it speaks are those that the statement's samples and words
    decode to; and THE cells behind the committed symbols (`cellsOf`, Cb/Pv/Tail/Unique.lean: a
    function of the committed symbols alone, neither of the weights nor of the reads) are small,
    have the committed packing, AND EVERY COMMITTED READ IS THEIR WEIGHTED SUM under the read's
    stated weights.
  `Reads.read_is`: that last clause by itself.
  `Reads.reads_are_true_at`: the premise on the numbers is paid where the caller's sizes are the
    library's `sizeOf` of a record of the smallness test (`sizeOf_uniq`).
Statements and proofs; nothing is counted anew.
Limits. THE NO-WRAP PREMISE IS `Size.Uniq`: 0 < beta; 4 beta - 1 <= rad; (4 beta - 2)(1 + rad + rad
^ 2) < the field's characteristic: without it "there are small cells" does not name them, and in a
ring of small characteristic the joint is true and weak. `cellsOf` is found by choice: no program is
given. Which entries of which vector `tab` reads, and that `w` is the function that a kind's form
means, is the caller's: no caller is named. Nothing here says that the boundary's relation holds.

-/
import Johnson.Desc.First.K8.LawPiece
import Cb.Pv.Tail.Unique
import OnBytes.Tie.Pv.Tail.SizeUniq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb.Pv.Tail KObj VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

section
variable {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base e : ℕ} {d : TailCallerOn}

/-- **The sent reads are the true ones**, at the chain's boundary in front of the kind's block. -/
theorem Reads.reads_are_true (Q : Reads Cl W F seat p base e d) (hu : d.c.s.Uniq Cb.Gl.p) (a : S ×
    F.E.Str) (w : W)
    (h : Q.relA a w) :
    (∀ i, d.c.Sg.decs (Q.rd a).1.2 (Q.rd a).2.2 i = some ((Q.wit w).1 i).1) ∧
      CellsOK d.c.letters (Q.rd a).1.1 (d.c.Sg.msgs (Q.wit w).1) (cellsOf d.c.letters (d.c.Sg.msgs
          (Q.wit w).1)) :=
  ⟨h.1, cellsOK_cellsOf d.c.letters Cb.Gl.p hu h.2.2⟩

/-- Every committed read is the weighted sum of THE committed cells under the read's stated weights.
-/
theorem Reads.read_is (Q : Reads Cl W F seat p base e d) (hu : d.c.s.Uniq Cb.Gl.p) (a : S × F.E.Str)
    (w : W)
    (h : Q.relA a w) (μ : Fin d.c.s.NM) (c : Fin (d.c.s.k μ)) (r : Fin (d.c.s.nr μ)) :
    d.c.tab (d.c.Sg.msgs (Q.wit w).1) μ r c =
      ∑ i, d.c.w (Q.rd a).1.1 μ r i *
        ((cellsOf d.c.letters (d.c.Sg.msgs (Q.wit w).1) μ c i : ℤ) : Cb.Gl.E) :=
  (Q.reads_are_true hu a w h).2.2.2 μ c r

/-- The premise on the numbers is paid at the library's sizes of a record of the smallness test. -/
theorem Reads.reads_are_true_at (Q : Reads Cl W F seat p base e d) (tl : OnBytes.Model.HTailF2)
    (hs : d.c.s = (OnBytes.Tie.Pv.Tail.sizeOf tl).size) (a : S × F.E.Str) (w : W) (h : Q.relA a w) :
    CellsOK d.c.letters (Q.rd a).1.1 (d.c.Sg.msgs (Q.wit w).1) (cellsOf d.c.letters (d.c.Sg.msgs
        (Q.wit w).1)) :=
  (Q.reads_are_true (hs ▸ OnBytes.Tie.Pv.Tail.sizeOf_uniq tl) a w h).2

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.Reads.reads_are_true
#print axioms VerifiableInference.Desc.First.K8.Reads.read_is
#print axioms VerifiableInference.Desc.First.K8.Reads.reads_are_true_at
