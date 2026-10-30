-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/OneWeight.lean: ONE PUBLIC TEST MORE BESIDE THE TABLE OF JOINTS' "forms":
BEHIND THE BATCHING, WHERE THE VIRTUAL ROWS' WEIGHTS LIE: an entry names row 0 of an array that has
one own row, AND THAT VIRTUAL ROW's ONE WEIGHT IS 1. Definitions with code. No Mathlib.
Why. A claim's form names virtual rows; the sentence "forms" reads the arrays' own rows. `ownRow`
(Johnson/Desc/First/Batch/ReaderOf.lean) asks "row 0 of an array of one own row" where the weights
are still empty. `oneWeight` asks the last step, at the ledger at which the one sum is taken;
`joinIn`: every entry of a form is such an entry, and every slot that it names is filled. With them
the two worlds give a form one worth (Johnson/Desc/Sound/FormsJoin.lean).
Limits: tests. Nothing is proved of any block. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- The entry names row 0 of an array of one own row, and that virtual row's one weight is 1. -/
def oneWeight (F : Fork) (x : Ent) : Bool :=
  match F.trees[x.tree]? with
  | some T =>
    match T.rows[0]? with
    | some r => decide (T.R = 1) && (decide (x.row = 0) && decide (r.coef.getD 0 zeroE = oneE))
    | none => false
  | none => false

/-- Every entry of a form is such an entry, and every slot that it names is filled. -/
def joinIn (F : Fork) (f : Aff) : Bool :=
  (f.ents.toList.all fun x => oneWeight F x) && f.slots.toList.all fun x => F.gotF.getD x.1 false

end VerifiableInference.Desc.K9
