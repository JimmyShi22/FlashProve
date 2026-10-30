-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/JoinsK14.lean: JOINS: from the law on the two texts of the committed table's
rows (Johnson/Bind/ForProver/K14Rows.lean) to the terms that other files call: the own parameters of
the linear claim's shared rounds (the shared chain) off a public part; the stand-in committer's
message and tail; a shape that passes the tests; what each text lays where the matrix reaches among
the pads, and a shape at which they part. Definitions, statements and proofs.

Main names (namespace `Bind.ForProver`).
  `p14Of_S`, `p14Of_item`: the shared chain's own parameters off Z (`Desc.K14.p14Of`,
    Johnson/Desc/K14/Blocks.lean) have the shape `linOf Z` and the item 0: by unfolding.
  **`rowsOf_at`**: at a value Z of `ProofFile.Pub`, under the very test that `encW` asks, at every row
    below 2^v: the rows that the shared rounds' honest side is handed at these parameters, with the
    pads and tails of the parameters' item, are `rowLaidE (linOf Z) w (rc 0)`.
  **`rowLaidE_message`**, **`rowLaidE_tail`**: `rowLaidE` is, place by place, the stand-in
    committer's message and tail of that row (`Bind.Twin.message`, `tailOf`, Johnson/Bind/Twin.lean)
    at the table `tableOfRand`, read in the field and written as the programs' element: so it is the
    row that `encAt` encodes.
  `exampleLin`, `exampleLin_ok`, `exampleLin_fits`: a small shape that passes the library's own test
    `LinShape.ok`, and so `rowsFit`: the premises of K14Rows.lean are met by something.
  `parts_at_pads`: where the matrix reaches beyond the plain entries: at a place among the pads
    `rowsOf` is the matrix's element and `rowLaidE` the pad.
  `exampleOver`, **`parts_example`**: a small shape whose matrix reaches among the pads, and a
    matrix of ones with pads of 0: at the row 0 and the place 10 the two texts differ: so
    `rowsOf_eq`'s premise `rowsFit` cannot be dropped. Of its other premise (r below 2^v) no example
    is given.

Limits. Z ranges over all values of the structure `ProofFile.Pub`, made of three public files or not. That
`linOf Z` passes `LinShape.ok` or `rowsFit` at any Z is not said here: `rowsFit` passes at a Z
that the maker of the public part returned of files in scope (`rowsFit_inScope`, ShapeInScope.lean);
the side library proves at the library's written copies of the two stored sets, in scope
(StartAtWrittenFiles.lean), that the maker returns, and
Johnson/Second/Seam/SeatFacts.lean evaluates it at its written copies of the small stored example's
files, out of scope. That a description's shared
chain is seated at `p14Of`'s parameters is read in the library's text and said by no theorem here.
That the honest side is handed `rowsOf` at these parameters is said by no theorem here. `exampleLin`
and `exampleOver` are no sizes of a release. No completeness, no index privacy; nothing on any
program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.K14Rows
import Johnson.Bind.ForProver.Laws
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E zeroE noId)
open OnBytes.Params (LinShape)
open OnBytes.Slice (toF ofF)
open ProofFile.Honest (TableRand Weights eOfF)

/-! ## At a public part -/

/-- The shared chain's own parameters off Z have the shape that `encW` reads. -/
theorem p14Of_S (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) : (Desc.K14.p14Of Z.p.chains l).S = linOf Z := rfl

/-- And the item 0. -/
theorem p14Of_item (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) : (Desc.K14.p14Of Z.p.chains l).item = 0 := rfl

/-- **The rows that the shared rounds' honest side is handed off Z are the rows that `encW`
encodes**, under the test that `encW` asks, at the rows below 2^v. -/
theorem rowsOf_at (Z : ProofFile.Pub) (l : List (ℕ × ℕ)) (w : Weights) (rc : ℕ → TableRand)
    (hfit : rowsFit (shapeOf Z) (linOf Z).kLo (linOf Z).matrixRows = true) (r k : ℕ)
    (hr : r < 2 ^ (shapeOf Z).v) :
    ProofFile.Honest.K14.rowsOf (Desc.K14.p14Of Z.p.chains l).S w
        ⟨(rc (Desc.K14.p14Of Z.p.chains l).item).pad,
          (rc (Desc.K14.p14Of Z.p.chains l).item).tail⟩ r k =
      rowLaidE (linOf Z) w (rc 0) r k :=
  rowsOf_eq (linOf Z) w (rc 0) hfit r k hr

/-! ## The row that is encoded -/

section
variable (S : LinShape) (w : Weights) (ρ : TableRand) (r : ℕ)

/-- **Below ell `rowLaidE` is the stand-in committer's message of that row.** -/
theorem rowLaidE_message (k : ℕ) (hk : k < S.fold.index.code.ell) :
    rowLaidE S w ρ r k =
      eOfF (toF ((Bind.Twin.message (shapeOfIndex S.fold.index)
        (tableOfRand (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ) r).getD k 0)) := by
  have hk' : k < (shapeOfIndex S.fold.index).l := hk
  unfold rowLaidE
  rw [if_pos hk, toF_message _ _ _ _ _ hk']

/-- **From `tailFirst` on it is the stand-in committer's tail of that row.** -/
theorem rowLaidE_tail (q : ℕ) (hq : q < S.fold.index.code.r) :
    rowLaidE S w ρ r (S.fold.tailFirst + q) =
      eOfF (toF ((Bind.Twin.tailOf (shapeOfIndex S.fold.index)
        (tableOfRand (entryAtF S.kLo S.matrixRows S.fold.index.v w.entry) ρ) r).getD q 0)) := by
  have hq' : q < (shapeOfIndex S.fold.index).r := hq
  have n1 : ¬ S.fold.tailFirst + q < S.fold.index.code.ell :=
    Nat.not_lt.2 (Nat.le_trans (ell_le_tailFirst S.fold) (Nat.le_add_right _ _))
  have p2 : S.fold.tailFirst ≤ S.fold.tailFirst + q ∧ S.fold.tailFirst + q < S.fold.entries :=
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hq _⟩
  unfold rowLaidE
  rw [if_neg n1, if_pos p2, Nat.add_sub_cancel_left, toF_tailOf _ _ _ _ _ hq']

/-- **Where the matrix reaches among the pads**: one text lays the matrix's element, the other the
pad. -/
theorem parts_at_pads (k : ℕ) (h1 : k < S.matrixRows * 2 ^ S.kLo) (h2 : S.fold.index.plain ≤ k)
    (h3 : k < S.fold.index.code.ell) :
    ProofFile.Honest.K14.rowsOf S w ⟨ρ.pad, ρ.tail⟩ r k =
        eOfF (w.entry (k / 2 ^ S.kLo) (k % 2 ^ S.kLo + 2 ^ S.kLo * r)) ∧
      rowLaidE S w ρ r k = eOfF (ρ.pad r (k - S.fold.index.plain)) := by
  have n2 : ¬ k < (shapeOfIndex S.fold.index).plain := Nat.not_lt.2 h2
  have h3' : k < (shapeOfIndex S.fold.index).l := h3
  refine ⟨?_, ?_⟩
  · unfold ProofFile.Honest.K14.rowsOf ProofFile.Honest.K14.entriesOf
    rw [if_pos h1, if_pos h1]
  · unfold rowLaidE rowMsgF
    rw [if_pos h3, if_neg n2, if_pos h3']
    rfl

end

/-! ## A shape that passes the tests -/

/-- A small shape: a table of four rows under a code of 64 positions, messages of 16 entries, tails
of 2; two OOD answers a row; a matrix of three rows, two of its columns in a row of the table. -/
def exampleLin : LinShape :=
  { fold := { index := { code := ⟨6, 16, 2⟩, v := 2, answers := 2, saltBytes := 40 }
              u := { code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := noId,
                     answers := 1 }
              rowsHigh := true, leafClass := 0, columns := 3 }
    kLo := 1, matrixRows := 3
    omega := { code := 1, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := noId,
               answers := 1 }
    w := { code := 1, mainRows := 3, mainDeg := 3, maskRows := 0, maskCode := noId, answers := 1 }
    omegaRowsHigh := true, wRowsHigh := true
    sharedSplit := { code := noId, mainRows := 0, mainDeg := 3, maskRows := 1, maskCode := 0,
                     answers := 1 }
    ownSplit := { code := noId, mainRows := 0, mainDeg := 1, maskRows := 0, maskCode := noId,
                  answers := 0 }
    omegaLeafClass := 1, sharedSplitLeafClass := 2, wLeafClass := 0, ownSplitLeafClass := 3
    sharedMaskCode := 0, ownMaskCode := 0, masksAhead := true
    testU := [⟨0, 0, 1, 0⟩], testOmega := [⟨1, 0, 0, 0⟩], testOwn := [⟨1, 0, 2, 0⟩]
    testOwnOmega := [], choice := ⟨true⟩ }

/-- It passes the library's own test on the shape. -/
theorem exampleLin_ok : exampleLin.ok = true := by decide

/-- So it passes `rowsFit`. -/
theorem exampleLin_fits :
    rowsFit (shapeOfIndex exampleLin.fold.index) exampleLin.kLo exampleLin.matrixRows = true :=
  rowsFit_of_ok exampleLin exampleLin_ok

/-- The same shape with a matrix of six rows: twelve places, where ten are plain. -/
def exampleOver : LinShape := { exampleLin with matrixRows := 6 }

/-- **There the two texts differ**: at a matrix of ones and pads of 0, at the row 0 and the place
10. -/
theorem parts_example :
    ProofFile.Honest.K14.rowsOf exampleOver ⟨fun _ _ => 1⟩ ⟨fun _ _ => 0, fun _ _ => 0⟩ 0 10 ≠
      rowLaidE exampleOver ⟨fun _ _ => 1⟩ ⟨fun _ _ => 0, fun _ _ => 0⟩ 0 10 := by
  obtain ⟨h1, h2⟩ := parts_at_pads exampleOver ⟨fun _ _ => 1⟩ ⟨fun _ _ => 0, fun _ _ => 0⟩ 0 10
    (by decide) (by decide) (by decide)
  rw [h1, h2]
  intro h
  have k : toF (ofF (1 : Cb.Gl.F)) = toF (ofF (0 : Cb.Gl.F)) :=
    congrArg (fun e : E => toF e.c0) h
  rw [OnBytes.Slice.toF_ofF, OnBytes.Slice.toF_ofF] at k
  exact one_ne_zero k

end Bind.ForProver

#print axioms Bind.ForProver.p14Of_S
#print axioms Bind.ForProver.p14Of_item
#print axioms Bind.ForProver.rowsOf_at
#print axioms Bind.ForProver.rowLaidE_message
#print axioms Bind.ForProver.rowLaidE_tail
#print axioms Bind.ForProver.parts_at_pads
#print axioms Bind.ForProver.exampleLin_ok
#print axioms Bind.ForProver.exampleLin_fits
#print axioms Bind.ForProver.parts_example
#print axioms Bind.ForProver.exampleLin
#print axioms Bind.ForProver.exampleOver
