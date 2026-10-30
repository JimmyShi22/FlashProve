-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwEnt.lean.
Which mask entry of a sumcheck a name of a coefficient of its hiding polynomial is.

One definition: `pEnt l i`: for a list `l` of formats of variables and a name `i : PIdx l`
(Cb/Ld/LdPsc.lean), the entry in the words of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean (`Sizes.Ent`):
(round, power less one), or the constant.
Limits: no statement.

-/
import Cb.Ld.LdPsc
import OnBytes.Tie.Pv.Lookup.Port.TwNums

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb
open TwNums.Sizes (Ent)

/-- which mask entry of a sumcheck the name i is: by round, the power less one; the Unit at the
list's end is the constant -/
def pEnt {E : Type} : (l : List (PFmt E)) → PIdx l → Ent
  | [], _ => .const
  | _ :: _, .inl t => .coef 0 t.1
  | _ :: l, .inr i =>
    match pEnt l i with
    | .coef j t => .coef (j + 1) t
    | e => e

end Cb.Tw
