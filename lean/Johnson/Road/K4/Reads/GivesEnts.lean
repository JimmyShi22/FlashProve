-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/GivesEnts.lean: THE READERS OF THE TABLES, IN THE FORM "WHEREVER IT IS THERE,
IT NAMES ENTRIES INSIDE THE FAMILIES OF TABLES". Statements and proofs. A tool for walking the texts
that are written with `do` over `Option` (OnBytes/Model/LayerForms.lean, LayerPanels.lean).

  `E1 v`: the first part of a pair (a form, its weight) is `InTab v`. `ge_mapP`: a form that is
    `InTab v`, with a weight laid beside it.
  `ge_U3at`, `ge_sumForms`, `ge_longA`, `ge_xbA`, `ge_shA`, `ge_shIn`, `ge_SA`, `ge_SxsA`, `ge_SBA`,
    `ge_shSum`: what a reader of the environment v returns is `InTab v`.

CARRIED OVER from Johnson/Road/K4/Slots/Gives.lean (the same ten on slots), letter for letter but
for the notion; the atoms are `inTab_U3at`, `inTab_sumForms`, `inTab_shortA`, `inTab_shA`
(Johnson/Road/K4/Reads/TermsEnts.lean), `entsIn_longA`, `entsIn_xbA` (GatedEnts.lean). `Gives` and
its rules are that file's.

Limits, as TermsEnts.lean's: NOT SAID: that the families of v.tab fill, or lie in, the part of the
array that the reads' test covers. An index that strays to another tensor, layer or limb of the same
family is not caught. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.Gives
import Johnson.Road.K4.Reads.GatedEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Slots (Gives)

variable {v : Env}

/-- The first part of a pair (a form, its weight) names entries inside the families alone. -/
abbrev E1 (v : Env) : Aff × E → Prop := fun p => InTab v p.1

theorem ge_U3at (t i : ℕ) : Gives (v.U3at t i) (InTab v) := fun _ h => inTab_U3at h

theorem ge_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)} (hg : ∀ x, Gives (g x) (E1 v)) :
    Gives (sumForms n g) (InTab v) :=
  fun _ h => inTab_sumForms (fun x p hp => hg x p hp) h

/-- A form with a weight beside it. -/
theorem ge_mapP {x : Option Aff} {f : Aff → Aff × E} (hx : Gives x (InTab v))
    (hf : ∀ a, InTab v a → InTab v (f a).1) : Gives (x.map f) (E1 v) :=
  Gives.map hx hf

theorem ge_longA (t : ℕ) (X : Ten) (i jh : ℕ) : Gives (v.longA t X i jh) (InTab v) :=
  fun _ h => entsIn_longA h

theorem ge_xbA (t kh : ℕ) : Gives (v.xbA t kh) (InTab v) := fun _ h => entsIn_xbA h

theorem ge_shA (X P : String) (i j : ℕ) : Gives (v.shA X P i j) (InTab v) :=
  fun _ h => inTab_shA h

theorem ge_shIn (found : Option (Ten × ℕ)) (i j : ℕ) : Gives (v.shIn found i j) (InTab v) := by
  unfold Env.shIn
  exact Gives.skip fun x _ h => inTab_shortA h

theorem ge_SA (wh : Array E) (X : String) (i : ℕ) (Z : String) :
    Gives (v.SA wh X i Z) (InTab v) := by
  unfold Env.SA
  refine Gives.skip fun x => ?_
  exact ge_sumForms fun xh => ge_mapP (ge_longA _ _ _ _) fun _ h => h

theorem ge_SxsA (wh : Array E) (Z : String) (sg : ℕ) : Gives (v.SxsA wh Z sg) (InTab v) := by
  unfold Env.SxsA
  refine Gives.skip fun tb => Gives.skip fun txs => ?_
  exact ge_sumForms fun xh =>
    ge_mapP (Gives.ite (ge_xbA _ _) (ge_longA _ _ _ _)) fun _ h => h

theorem ge_SBA (wh : Array E) (a b : ℕ) (X : String) (i : ℕ) (Z : String) (x0 : ℕ) :
    Gives (v.SBA wh a b X i Z x0) (InTab v) := by
  unfold Env.SBA
  refine Gives.skip fun x => ?_
  exact ge_sumForms fun k => ge_mapP (ge_longA _ _ _ _) fun _ h => h

theorem ge_shSum (ew : Array E) (n : ℕ) (X P : String) (i : ℕ) :
    Gives (v.shSum ew n X P i) (InTab v) := by
  unfold Env.shSum
  exact ge_sumForms fun x => ge_mapP (ge_shIn _ _ _) fun _ h => h

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Desc.First.K4.Reads.ge_SxsA
#print axioms OnBytes.Desc.First.K4.Reads.ge_SBA
#print axioms OnBytes.Desc.First.K4.Reads.ge_shSum
