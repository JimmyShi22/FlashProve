-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkAtIxR.lean: the format and the decoder of a stored table WITH A RECORD at the
link's sizes (`Sz`, OnBytes/Slice/LinkAt.lean), over that file alone. DEFINITIONS:
NOTHING ON SOUNDNESS IS SHOWN.

WHY. `Sz.ix` has the empty sample by definition: over it a record has one value. A key's, an entry's
or a proof's statement on tables with a record needs the same format with a sample map of one row.
Here that is ONE definition, `Sz.ixR Z`, for all of them, in a file that imports as little as may
be. The format and the decoder of the files over `Sz.ix` are the case `Sample.nil` (their
language compares whole decoded tables, not the entries before a cut). How it stands to the letters
of OnBytes/Slice/DecoderRec.lean, and the programs' sample map: OnBytes/Slice/LinkAtRec.lean.

Main definitions.
 `Sz.ixR Z`             `Sz.ix` with the sample map Z. Positions, coefficients, entries, rows and
                        decoded tables keep their types.
 `Sz.dcdR Z`, `Sz.collR Z`   the decoder with a record; "the record does not single one out".




What is not claimed. No link, language or protocol over `ixR` is written HERE: `Sz.lw`, `Sz.lk`,
`Sz.fam`, `Sz.Lang` and all that stands on them are over `Sz.ix`; `dcdR` takes of `Sz.lk` how a
symbol is read at a row, and nothing else. A link, two languages and the link's soundness over
`ixR`: OnBytes/Slice/CorePeelRec.lean, LinkSoundRec.lean (`Sz.lkR`, `Sz.LangR`, `Sz.LangE2T`,
`link_sound_rec`). Nothing on any hash function.

-/
import OnBytes.Slice.LinkAt

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood

namespace Sz
variable (S : Sz)

/-- **The format of a stored table with a record, at the link's sizes**: `Sz.ix` with the sample map
Z of one row in the place of `Sample.nil`. The types of positions, coefficients, entries, rows and
decoded tables are those of `Sz.ix`. -/
@[reducible] noncomputable def ixR (Z : Sample GE S.En) : LdIx GE S.Pos S.Co S.En :=
  { S.ix with Z := Z }

/-- **The decoder of a stored table with a record**, at the link's sizes: the library's `LdIx.dec`
at `ixR`, on the table as the link reads it. -/
noncomputable def dcdR (Z : Sample GE S.En) (f : S.Pos → Run.PQ.SgX) (rec : (S.ixR Z).Rec) :
    Option ((S.ixR Z).Row × S.En → GE) :=
  (S.ixR Z).dec (S.lk.tab f) rec

/-- **The record does not single one out**, at the link's sizes. -/
def collR (Z : Sample GE S.En) (f : S.Pos → Run.PQ.SgX) (ρ : Z.D) : Prop :=
  (S.ixR Z).Coll (S.lk.tab f) ρ

end Sz
end OnBytes.Slice
