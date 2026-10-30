-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ClaimsLedger.lean: the letter A of the description made of the three files' protocols,
as a written term at the reference sizes.

One definition, two equivalences.
  `claimsLedger D N s : D.Claims (Instance' ppref)` (OnBytes/Slice/DecoderRec.lean): the matrices,
    the matrix of a decoded table and the law that it reads no pad are those of
    Johnson/Flat/Claims.lean
    (`Cells D N`, `cellsOf D N`, `cellsOf_cut`); in range: the matrix holds an index; the claim of a
    request: the matrix holds an index at which some trace meets the library's relaxed relation with
    the cost ledger at the protocol's prime and exact match (`InRange`, `RelL s`:
    Johnson/Flat/LedgerClaim.lean, where it is said what enforces which clause).
  `says_iff`, `inRange_iff`: `Says` and "holds an index" of Johnson/Flat/Claims.lean are `SaysC` and
    `InRange`.

Against `claims D N s` of Johnson/Flat/Claims.lean: `Mat`, `mat`, `mat_cut`: the same. `inRange`:
the same up to `inRange_iff`. `Rel`: there "if the matrix holds an index, the request is true
there" (`Cm.PaperTrue`); here "the matrix holds an index and a trace meets the relaxed relation
there".

Limits: nothing on a protocol. The reference sizes alone: the small example has no such relation in
the library.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Claims
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model VerifiableInference
open Inst.Model.Layout (kRef hRef)

variable (D : DecR) (N : MatrixNums)

/-- **What the statements read of a decoded table**, at a table of scales s. -/
def claimsLedger (s : Cm.Scales) : D.Claims (Instance' ppref) where
  Mat := Cells D N
  mat := cellsOf D N
  inRange := OnPublicFiles.Flat.InRange
  Rel := OnPublicFiles.Flat.RelL s
  mat_cut := cellsOf_cut D N

theorem says_iff (M : Cells D N) (W : Mat) : Says D N M W ↔ OnPublicFiles.Flat.SaysC M W := Iff.rfl

theorem inRange_iff (M : Cells D N) :
    (indexIn D N M).isSome = true ↔ OnPublicFiles.Flat.InRange M := by
  unfold indexIn
  constructor
  · intro h
    by_contra hn
    rw [dif_neg (show ¬ ∃ i : Cm.Idx, Says D N M i.mat from hn)] at h
    cases h
  · intro h
    rw [dif_pos (show ∃ i : Cm.Idx, Says D N M i.mat from h)]
    rfl

end OnBytes.Flat
