-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/LineEnts.lean: THE FORMS OF THE SEGMENTS' KEYS, AND EACH CALL's FACTOR IN THE
LOOKUP's JOIN, NAME ENTRIES INSIDE THE FAMILIES OF TABLES (`InTab`,
Johnson/Road/K4/Reads/TermsEnts.lean). A walk of `Env.line` and `Env.joinPart`
(OnBytes/Model/LayerForms.lean), the plain functions from which K4's `joinStart`
(OnBytes/Desc/First/K4/Hear.lean) makes the start form of the batched sumcheck. Statements and
proofs.

  `inTab_high`, `ge_site`: the two keys of a rounding site.
  `ge_lineGU`, `ge_lineGUH`, `ge_lineQK`, `ge_lineROW`, `ge_lineDD`: five helper texts of `line`,
    for eight of its names (G U, GH UH, QK QKH, ROW, DD).
  **`ge_line`**: whatever `v.line sn lam ew wh` returns, at any string sn, is `InTab v`.
  **`ge_joinPart`**: whatever `v.joinPart alpha theta q c weighed` returns is `InTab v`.

HOW. Each text is a `do` over `Option` that makes its form from the readers' returns
(Johnson/Road/K4/Reads/GivesEnts.lean) and from constants, by sums, differences and factors. Two
small tactics, local to this file, take such a text apart: `ents` (a form made of forms that are
`InTab`) and `walk` (a `do` block: a branch, a bind, a return, a reader). `ge_line` is proved under
`set_option maxRecDepth 8000`: its chain of branches is long.

Limits. No hypothesis: OF WHATEVER IS RETURNED. At a string that is none of `line`'s 34 names
`line` returns none and the sentence is empty. That `line` returns at a plan's segments is not said
here (a run at a made-up shape: Johnson/Road/FormsKeysRun.lean). As TermsEnts.lean's: an index that
strays to another tensor, layer or limb of the same family is not caught; nothing on whether the
families lie in the part of the array that the reads' test covers. Nothing on what a form is worth.
Nothing on soundness.
-/
import Johnson.Road.K4.Reads.GivesEnts
import Johnson.Road.K4.Slots.Panels

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Slots (Gives gives_foldlM_inv)

variable {v : Env}

/-- The key of the high digits of a rounding site. -/
theorem inTab_high (w : E) {Srh : Aff} (k form : ℕ) (h : InTab v Srh) :
    InTab v (Env.high w Srh k form) := by
  unfold Env.high
  exact entsIn_scale _ (entsIn_add (entsIn_ofConst _) h)

/-- A form made of forms that are `InTab`, by sums, differences, factors and constants. The rules
are matched by the forms' letters alone (`with_reducible`): no element of the field is unfolded. -/
local macro "ents" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | with_reducible exact entsIn_ofConst _
  | with_reducible exact inTab_aff0
  | with_reducible refine inTab_high _ _ _ ?_
  | with_reducible refine entsIn_scale _ ?_
  | with_reducible refine entsIn_sub ?_ ?_
  | with_reducible refine entsIn_add ?_ ?_
  | with_reducible refine entsIn_addMul _ ?_ ?_)

/-- The low key of a rounding site. -/
theorem ge_site (w : E) {SQ : Aff} (k form : ℕ) {Srh : Unit → Option Aff} (hQ : InTab v SQ)
    (hS : Gives (Srh ()) (InTab v)) : Gives (Env.site w SQ k form Srh) (InTab v) := by
  unfold Env.site
  dsimp only
  refine Gives.ite (Gives.pure ?_) (Gives.bind hS fun a ha => Gives.pure ?_)
  · ents
  · ents

/-- A `do` block over `Option` that makes a form from the readers' returns, at the environment v. -/
local macro "walk " v:term : tactic => `(tactic| repeat' first
  | with_reducible exact ge_SA _ _ _ _
  | with_reducible exact ge_SBA _ _ _ _ _ _ _
  | with_reducible exact ge_SxsA _ _ _
  | with_reducible exact ge_shSum _ _ _ _ _
  | with_reducible exact ge_shA _ _ _ _
  | with_reducible exact ge_U3at _ _
  | with_reducible exact Gives.none
  | with_reducible refine Gives.ite ?_ ?_
  | with_reducible refine ge_site _ _ _ ?_ ?_
  | with_reducible refine ge_sumForms fun _ => ?_
  | with_reducible refine Gives.bind (Φ := InTab $v) ?_ fun _ _ => ?_
  | with_reducible refine Gives.pure ?_
  | with_reducible assumption
  | with_reducible exact entsIn_ofConst _
  | with_reducible exact inTab_aff0
  | with_reducible refine inTab_high _ _ _ ?_
  | with_reducible refine entsIn_scale _ ?_
  | with_reducible refine entsIn_sub ?_ ?_
  | with_reducible refine entsIn_add ?_ ?_
  | with_reducible refine entsIn_addMul _ ?_ ?_)

theorem ge_lineGU (up : Bool) (lam : ℕ) (ew wh : Array E) :
    Gives (v.lineGU up lam ew wh) (InTab v) := by
  unfold Env.lineGU
  dsimp only
  walk v

theorem ge_lineGUH (up : Bool) (lam : ℕ) (ew wh : Array E) :
    Gives (v.lineGUH up lam ew wh) (InTab v) := by
  unfold Env.lineGUH
  dsimp only
  walk v

theorem ge_lineQK (hi : Bool) (lam : ℕ) (ew wh : Array E) :
    Gives (v.lineQK hi lam ew wh) (InTab v) := by
  unfold Env.lineQK
  dsimp only
  walk v

theorem ge_lineROW (lam : ℕ) (ew : Array E) : Gives (v.lineROW lam ew) (InTab v) := by
  unfold Env.lineROW
  dsimp only
  refine Gives.skip fun t => Gives.skip fun trow => ge_sumForms fun x => ?_
  exact ge_mapP (ge_U3at _ _) fun a ha => entsIn_add ha (entsIn_ofConst _)

theorem ge_lineDD (lamM : ℕ) (ew : Array E) : Gives (v.lineDD lamM ew) (InTab v) := by
  unfold Env.lineDD
  dsimp only
  refine Gives.bind (Φ := fun s : Aff × Aff => InTab v s.1 ∧ InTab v s.2) ?_
    fun r hr => Gives.pure hr.1
  refine gives_foldlM_inv (P := fun s : Aff × Aff => InTab v s.1 ∧ InTab v s.2)
    (fun s x hs => ?_) _ _ ⟨inTab_aff0, inTab_aff0⟩
  refine Gives.bind (ge_shA _ _ _ _) fun a ha => Gives.bind (ge_shA _ _ _ _) fun b hb =>
    Gives.pure ⟨?_, ?_⟩
  · exact entsIn_addMul _ hs.1 (entsIn_add ha hs.2)
  · exact entsIn_add hs.2 hb

set_option maxRecDepth 8000 in
/-- **The form of the keys of a segment at a layer**: whatever `line` returns names entries inside
the families of tables alone. -/
theorem ge_line (sn : String) (lam : ℕ) (ew wh : Array E) :
    Gives (v.line sn lam ew wh) (InTab v) := by
  unfold Env.line
  dsimp only
  repeat' first
    | with_reducible exact ge_lineGU _ _ _ _
    | with_reducible exact ge_lineGUH _ _ _ _
    | with_reducible exact ge_lineQK _ _ _ _
    | with_reducible exact ge_lineROW _ _
    | with_reducible exact ge_lineDD _ _
    | with_reducible refine Gives.ite ?_ ?_
  all_goals walk v

/-- **One call's factor in the lookup's join**: whatever `joinPart` returns names entries inside the
families of tables alone. -/
theorem ge_joinPart (alpha theta : E) (q : ℕ) (c : CallD) (weighed : Array Bool) :
    Gives (v.joinPart alpha theta q c weighed) (InTab v) := by
  unfold Env.joinPart
  dsimp only
  refine Gives.bind (Φ := InTab v) ?_ fun lines hl =>
    Gives.pure (entsIn_add (entsIn_ofConst _) hl)
  refine gives_foldlM_inv (P := InTab v) (fun a s ha => ?_) _ _ inTab_aff0
  refine gives_foldlM_inv (P := InTab v) (fun a lam ha => ?_) _ _ ha
  exact Gives.ite (Gives.some ha) (Gives.map (ge_line _ _ _ _) fun f hf => entsIn_addMul _ ha hf)

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Desc.First.K4.Reads.ge_site
#print axioms OnBytes.Desc.First.K4.Reads.ge_lineGU
#print axioms OnBytes.Desc.First.K4.Reads.ge_lineGUH
#print axioms OnBytes.Desc.First.K4.Reads.ge_lineQK
#print axioms OnBytes.Desc.First.K4.Reads.ge_lineROW
#print axioms OnBytes.Desc.First.K4.Reads.ge_lineDD
#print axioms OnBytes.Desc.First.K4.Reads.ge_line
#print axioms OnBytes.Desc.First.K4.Reads.ge_joinPart
