-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonPlanDef.lean: the session's plan at the write-up's form
(Cb/Ld/LdLinCloseDemandP.lean, Cb/Ld/LdLinClosePlanRows.lean, Cb/Obj/LdObjectPpRows.lean) with the
errors of its four whole tests overwritten by the full list.

Three definitions; no statement. Generic. The full list (`Err.full`, Cb/Gen/FullErr.lean) has, for
each round, the number of all values of that round's verifier message: as a probability, the error
1.

Main names:
  `T.full`, for `T : LdLinPpT p`: the three whole tests T₁, T₂, T₃ (blocks to the trivial statement)
    with their errors overwritten (`LdEnd.full`, Cb/Gen/FullErr.lean); the groups are the plan p's;
    evaders, list bounds, numbers of positions, the rest (`Q'`: the closing of what the preamble
    left), fixed values are T's own.
  `X.full`, for `X : LdRowsD S E₀ Wp rows`: the like for the one whole test of "the rest".
  `R.fullB`, for `R : LdObjRp F E`: R with `TB₀.full`, `XB.full` for the session's tests TB₀, XB.
    The offline tests, the link, the request, all data are R's own.

Limits: `R.fullB` is another object's data: a device of proofs. At it "the session's four whole
tests are in order" asks nothing on the chance of a cheating prover in a round of these tests. This
file does not say how `R.fullB`'s terms stand to R's (that they agree off their errors:
Cb/Ld/LdHonPlanEq.lean).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gen.FullErrTow
import Cb.Obj.LdObjectPpRows

set_option autoImplicit false

namespace Cb
open Iop Prob Iop.IOR Hiop

/-- the plan's three whole tests, their errors overwritten by the full list -/
def LdLinPpT.full {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
    {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T : LdLinPpT p) : LdLinPpT p :=
  { T with T₁ := T.T₁.full, T₂ := T.T₂.full, T₃ := T.T₃.full }

/-- the rest's whole test, its errors overwritten by the full list -/
def LdRowsD.full {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp Cl B : Type}
    [Fintype B] {rows : B → Slf E Cl S.Ent} (X : LdRowsD S E₀ Wp rows) : LdRowsD S E₀ Wp rows :=
  { X with T := X.T.full }

/-- the object's data with the session's four whole tests at the full list -/
def LdObjRp.fullB {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdObjRp F E) : LdObjRp F E := { R with TB₀ := R.TB₀.full, XB := R.XB.full }

end Cb
