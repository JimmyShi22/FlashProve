-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkAtRec.lean: the format of a stored table with a record at the link's sizes
(`Sz.ixR`, OnBytes/Slice/LinkAtIxR.lean), held against the letters of OnBytes/Slice/DecoderRec.lean
(`DecR`), and at the programs' sample map as OnBytes/Slice/RecordRead.lean reads it. DEFINITIONS,
AND EQUATIONS THAT HOLD BY DEFINITION: NOTHING ON SOUNDNESS IS SHOWN.

Main definitions.
 `Sz.toDecR Z cut`      the data `DecR` at the link's code, number of row variables and radius.
 `Sz.ixRec lg s`        `ixR` at the sample map `recZ` (OnBytes/Slice/RecordRead.lean).
Main theorems, each by definition.
 `toDecR_ix`, `dcdR_eq`, `collR_eq`   format, decoder and collisions of `toDecR` are `ixR`, `dcdR`,
                        `collR`.
 `ixRec_eq`, `toDecR_rec`   at `recZ` and the cut l - 3 s: the format and the data of `decRec`.

What is not claimed. The limits of OnBytes/Slice/LinkAtIxR.lean stand: no link, language or protocol
over `ixR` is written here (they are in OnBytes/Slice/CorePeelRec.lean, LinkSoundRec.lean).
`Sz.P.cut`, the entries that the link compares, is not held against the argument `cut`: there it is
a hypothesis. That lg and s are those of any setting. That `recZ` is the programs' sample map is a
reading of their text. Nothing on any hash function.

-/
import OnBytes.Slice.LinkAtIxR
import OnBytes.Slice.RecordRead

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood

namespace Sz
variable (S : Sz)

/-- The data of a decoder with a record, at the link's sizes. cut: the number of entries of a row's
message before its pads. -/
@[reducible] def toDecR (Z : Sample GE S.En) (cut : ℕ) : DecR :=
  { S.toDec with Z := Z, cut := cut }

/-- The format of `toDecR` is `ixR`. -/
theorem toDecR_ix (Z : Sample GE S.En) (cut : ℕ) : (S.toDecR Z cut).ix = S.ixR Z := rfl

/-- It is the decoder of `toDecR`. -/
theorem dcdR_eq (Z : Sample GE S.En) (cut : ℕ) : S.dcdR Z = (S.toDecR Z cut).dcd := rfl

/-- It is `DecR.coll` of `toDecR`. -/
theorem collR_eq (Z : Sample GE S.En) (cut : ℕ) : S.collR Z = (S.toDecR Z cut).coll := rfl

/-- **At the programs' sample map**: lg coordinates, s answers. -/
@[reducible] noncomputable def ixRec (lg s : ℕ) : LdIx GE S.Pos S.Co S.En :=
  S.ixR (recZ S.P.T.l lg s)

/-- It is the format of `decRec` (OnBytes/Slice/RecordRead.lean) at the link's code, number of row
variables and radius. -/
theorem ixRec_eq (lg s : ℕ) : S.ixRec lg s = (decRec S.P.T S.P.v S.eM lg s).ix := rfl

/-- `toDecR` at the programs' sample map and the cut l - 3 s is `decRec`. -/
theorem toDecR_rec (lg s : ℕ) :
    S.toDecR (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) = decRec S.P.T S.P.v S.eM lg s := rfl

end Sz
end OnBytes.Slice
