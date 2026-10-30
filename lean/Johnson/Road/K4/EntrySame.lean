-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EntrySame.lean: the entries entryTrue (Johnson/Road/K4/EntryTrue.lean) read of the
smallness test's record tl ITS NUMBERING OF PLACES ALONE (HTailF2.tabAt). So they are the same at
two records with the same rows and columns of matrices, at equal matrices.

  `entryOf_tabAt`: entryOf at two records whose tabAt is one function.
  `entryTrue_tl`: entryTrue at two records with one list of rows and columns, each with as many
    matrices as its list is long (tabAt_congr, Johnson/Road/K4/ReadsAtPub.lean).
  `entryTrue_both`: the same with two names for one family of matrices (M = M', whole): a rewriting.
No new argument.
Limits. Equations of definitions. That a record behind a yes holds the plan's rows and columns, and
that two readers of the first sending's matrices agree, are premises: shown by nobody here. Nothing
on soundness.


-/
import Johnson.Road.K4.EntryTrue
import Johnson.Road.K4.ReadsAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes.Model (Reading HFun HTailF2)
open OnBytes.Model.Layer (Own)

/-- entryOf reads of tl its numbering of places alone. -/
theorem entryOf_tabAt {K : Type} [Field K] (ρ : Reading K) {tl tl' : HTailF2}
    (h : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg) (funs : Array HFun) (iU3 K3 : ℕ)
    (M : Mats K) : entryOf ρ tl funs iU3 K3 M = entryOf ρ tl' funs iU3 K3 M := by
  have e : tl.tabAt = tl'.tabAt := funext fun Fn => funext fun c => funext fun sg => h Fn c sg
  unfold entryOf
  rw [e]

/-- entryTrue at two records with one list of rows and columns. -/
theorem entryTrue_tl {tl tl' : HTailF2}
    (hm : (tl.mats.map fun M => (M.m, M.k)) = tl'.mats.map fun M => (M.m, M.k))
    (hN : tl.NM = tl.mats.size) (hN' : tl'.NM = tl'.mats.size) (o : Own) (M : Mats Cb.Gl.E) :
    entryTrue tl o M = entryTrue tl' o M :=
  entryOf_tabAt _ (tabAt_congr hm hN hN') _ _ _ _

/-- With the matrices equal too. -/
theorem entryTrue_both {tl tl' : HTailF2}
    (hm : (tl.mats.map fun M => (M.m, M.k)) = tl'.mats.map fun M => (M.m, M.k))
    (hN : tl.NM = tl.mats.size) (hN' : tl'.NM = tl'.mats.size) (o : Own) {M M' : Mats Cb.Gl.E}
    (hM : M = M') : entryTrue tl o M = entryTrue tl' o M' := by
  rw [hM]
  exact entryTrue_tl hm hN hN' o M'

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.entryOf_tabAt
#print axioms OnBytes.Road.K4.entryTrue_tl
#print axioms OnBytes.Road.K4.entryTrue_both
