-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/InRangeOwed.lean: TWO STATEMENTS THAT ARE OWED FOR K14's LAW, AS PROPOSITIONS
BY def: NO PROOF HERE. The linear claim's vectors Omega and W lie in the main tables of two oracle
messages, by a layout (OnBytes.VectorLay: linLayOmega, linLayW, OnBytes/Iop/Lin.lean). A reader of a
witness's words cuts a table's index i into a row (i modulo 2 ^ ceilLog2 mainRows) and a PLACE in
the row (i / 2 ^ ceilLog2 mainRows) (wordsOn, Johnson/Desc/Means/ItemsTab.lean). A typed message has
the places below its code's message length alone. OWED: under the shape's own conditions at the
codes (OnBytes.linOk, which holds matrixRows ≤ vectorRoom … and 2 ^ kCol ≤ vectorRoom …), every
index that the layout gives an entry of the vector has its place below that length.

  OmegaInRange    for Omega: spent as the premise hin of omega_at_last
                  (Johnson/Desc/K14/Law/LedgerLast.lean): the two readers of a witness say the same
                  of o_omega.
  WInRange        the like for W.
What is not claimed. That they hold.
(As typed both are false: not_omegaInRange, not_wInRange. With one premise more, that every code's
message length is a power of two, they hold: omegaInRange_of_lengths, wInRange_of_lengths. All four:
Johnson/Desc/K14/Law/InRange.lean.)
Nothing on soundness.

-/
import OnBytes.Iop.Lin
import Johnson.Pack.Port

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params

/-- OWED: Omega's indices lie inside o_omega's message's range. -/
def OmegaInRange : Prop :=
  ∀ (codes : Codes) (S : LinShape), linOk codes S = true → ∀ y < S.matrixRows,
    (linLayOmega codes S).index y / 2 ^ ceilLog2 S.omega.mainRows <
      (Johnson.Pack.pMain codes S.omega).ell

/-- OWED: W's indices lie inside W's message's range. -/
def WInRange : Prop :=
  ∀ (codes : Codes) (S : LinShape), linOk codes S = true → ∀ c < 2 ^ S.kCol,
    (linLayW codes S).index c / 2 ^ ceilLog2 S.w.mainRows < (Johnson.Pack.pMain codes S.w).ell

end Desc.K14.Law
