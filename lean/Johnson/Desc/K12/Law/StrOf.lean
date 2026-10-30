-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/StrOf.lean: "the word as sent" off a written oracle. Definitions and one
equation, with its proof.

It gives a string of the library's oracle message of a shape (`portOmZ`, Johnson/Pack/PortZ.lean)
whose reading as a native word of the code is the library's reading of the written oracle
(`Mb.ofOrc`, OnBytes/Slice/KeyGroup.lean) at the format that the shape gives (`mbOfShape`,
Johnson/Desc/K12/Law/ShareNear.lean).
Main names:
  `rowOf`, `upRow_rowOf`: a symbol as it is sent (over the base field or the extension field), and
    how the library's `upRow` reads it.
  `strOf cs sh e0 L d o`: the string: main symbols from word L.oM on (one word a symbol where the
    shape's main degree is 1, else three), mask symbols from word L.oZ on (three words), in the
    columns of the written round d's oracle o.
  `upW_strOf`: where L.base = (sh.mainDeg == 1): (portOmZ cs sh e0).upW (strOf cs sh e0 L d o) =
    (mbOfShape cs sh e0).ofOrc L d o.
Limits: `strOf` is a definition of this file's own: that it is what the frame of Johnson/Desc/Sound/
reads off the oracle model's strings (its `wordsOf`) is not shown; Johnson/Desc/K12/Law/StrRows.lean
has one form of the two, under two premises. Positions beyond the tree's depth: a position x of the
message is below 2 ^ aOf (mask) or 2 ^ (the main code's logarithm)
(main): that the written oracle has a column there belongs to the reading. No soundness is claimed,
and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.TieRoad

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice Johnson.Pack
open _root_.Run

/-- A symbol as it is sent: over the base field if b, else over the extension field. -/
def rowOf : (b : Bool) → GF → GE → RowTy b
  | true, x, _ => x
  | false, _, y => y

theorem upRow_rowOf (b : Bool) (x : GF) (y : GE) :
    upRow b (rowOf b x y) = if b then algebraMap GF GE x else y := by
  cases b <;> rfl

/-- The word as sent, off a written oracle: the string of the oracle message of the shape sh whose
symbols stand in the columns of the written round d's tree as the record L says (the library's Lay:
the first word of the main symbols and of the mask symbols). A main symbol is one word over the base
field where the shape's main degree is 1, else three words. -/
noncomputable def strOf (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) (L : Lay) (d :
    PQ.RD)
    (o : (wRound d).Orc) : (portOmZ cs sh e0).Str := fun p =>
  match p with
  | .inl x => fun r => rowOf (sh.mainDeg == 1) (toF (wordAt d o x.val (L.oM + r.1.val)))
      (symW d o x.val (L.oM + 3 * r.1.val))
  | .inr x => fun r => rowOf false 0 (symW d o x.val (L.oZ + 3 * r.1.val))

/-- Read as a native word of the code, it is the library's reading of the written oracle
(Mb.ofOrc) at the format that the shape gives. -/
theorem upW_strOf (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) (L : Lay) (d : PQ.RD)
    (o : (wRound d).Orc) (hL : L.base = (sh.mainDeg == 1)) :
    (portOmZ cs sh e0).upW (strOf cs sh e0 L d o) = (mbOfShape cs sh e0).ofOrc L d o := by
  funext p
  rcases p with x | x
  · funext r
    show upRow (sh.mainDeg == 1) (rowOf (sh.mainDeg == 1) _ _) =
      if L.base then symF d o x.val (L.oM + r.1.val) else symW d o x.val (L.oM + 3 * r.1.val)
    rw [upRow_rowOf, hL]
    rfl
  · funext r
    rfl

end H2K.Pin

#print axioms H2K.Pin.upW_strOf
