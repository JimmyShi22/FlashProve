-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Decoder.lean: what a decoder of a stored table is made of.

OnBytes/Slice/LinkAt.lean has the decoder of a stored table among the sizes of the link (`Sz.dcd`)
and, with it, the language of an entry file's chain (`Sz.Lang`: the first table does not decode, or
the copy decodes to the same). A statement on a key file, an entry file and a proof file together
needs one decoder for all three. This file takes out of `Sz` what the decoder reads, and nothing of
the link: the table's code, the number of row variables, the radius (`Dec`).
The decoder and three languages over it: `DecR` (OnBytes/Slice/DecoderRec.lean).

Main definitions: `Dec`, `Dec.dist`, `Sz.toDec`.

Not claimed. No protocol is shown sound here, and none for `Sz.Lang`.
(OnBytes/Slice/LinkSoundRec.lean and the files above it have theorems for other languages,
`Sz.LangR` and `Sz.LangE2T`, under the hypotheses that they name.)
Nothing here is shown of `DecR` (OnBytes/Slice/DecoderRec.lean).
-/
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.Raw

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood

/-! ## The decoder -/

/-- **What a decoder of a stored table is made of.** T: the table's code. v: the number of row
variables. eM: the radius, in columns. -/
structure Dec where
  T : Fmt.M1.Code
  v : ℕ
  eM : ℕ

namespace Dec
variable (D : Dec)

/-- positions of a stored table; coefficients of a row's polynomial; entries of a row's message -/
abbrev Pos : Type := Fin (2 ^ D.T.a)
/-- See `Pos`. -/
abbrev Co : Type := Fin (D.T.r + D.T.l)
/-- See `Pos`. -/
abbrev En : Type := Fin D.T.l

/-- A symbol of a stored table, read at a row: a missing word is read as 0, and the position is not
read. -/
def up (s : Run.PQ.SgX) (r : Fin D.v → Bool) : GE :=
  algebraMap GF GE (toF (s.2.getD (Sz.rowNo r) 0))





variable {D} {X : Type}

/-! ## The code's distance -/

variable (D)

/-- The number 2^a - (r + l) + 1: for a ≤ 32 and r + l ≤ 2^a the table's code has that distance
(`hasDist_genOf`, OnBytes/Slice/CodeFacts.lean). -/
def dist : ℕ := 2 ^ D.T.a - (D.T.r + D.T.l) + 1

end Dec

/-! ## The sizes of the link -/

/-- The decoder of the link's sizes. -/
@[reducible] def Sz.toDec (S : Sz) : Dec := ⟨S.P.T, S.P.v, S.eM⟩

end OnBytes.Slice
