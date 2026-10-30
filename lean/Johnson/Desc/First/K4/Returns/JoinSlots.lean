-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/JoinSlots.lean: THE LAYERS' OWN ROUNDS (K4): NO PART OF THE LOOKUP's
JOIN NAMES A SLOT. A walk of Env.line and Env.joinPart (OnBytes/Model/LayerForms.lean), built like
the library's walk for entries (Johnson/Road/K4/Reads/LineEnts.lean), over its laws on the readers
of the tables (Johnson/Road/K4/Slots/Gives.lean) and on folds (Johnson/Road/K4/Slots/Panels.lean).
General laws: nothing is evaluated.

How it is said. For a property S of slots, SlotsIn S f: every slot that the form f names has S. The
walk shows SlotsIn S of what is returned AT EVERY S; at the S that no slot has, that is: no slot is
named.

  sl_zero         the zero form names slots with S alone, at every S.
  sl_high, gs_site   so do Env.high's form and whatever Env.site returns, WHERE the forms that they
                  are made from do.
  gs_lineGU, gs_lineGUH, gs_lineQK, gs_lineROW, gs_lineDD   so does whatever each of these five
                  functions returns, which Env.line calls; no premise.
  gs_line         so does whatever v.line returns, at any string.
  **gs_joinPart**   so does whatever v.joinPart returns.
  slots_nil       at the S that no slot has: the shape's list of slots (affSh,
                  Johnson/Desc/First/Shape/Parts.lean) is empty.
  mapM_gives      Gives passes through mapM: if whatever f returns has a property, so has each
                  member of a list that l.mapM f returns.
  **join_no_slot**   of a list of parts that the join's reading returns, no part names a slot: the
                  last clause of JoinPub (Johnson/Desc/First/K4/Returns/Stack.lean).

Limits. OF WHATEVER IS RETURNED: that line or joinPart return is not said. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Road.K4.Slots.Gives
import Johnson.Road.K4.Slots.Panels
import Johnson.Desc.First.K4.Returns.Stack

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default instance Scl.ref (the reference scales, Inst/Model/Scl.lean) is switched
off in this file, as in its neighbours: so no statement can take that table of scales unsaid. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Slots

variable {v : Env} {S : ℕ → Prop}

/-- Every slot that the zero form names has S: it names none. -/
theorem sl_zero : SlotsIn S aff0 := slotsIn_ofConst _

/-- Where every slot that the form Srh names has S, so has every slot that Env.high names, the key
of the high digits of a rounding site made from Srh. -/
theorem sl_high (w : E) {Srh : Aff} (k form : ℕ) (h : SlotsIn S Srh) :
    SlotsIn S (Env.high w Srh k form) := by
  unfold Env.high
  exact slotsIn_scale _ (slotsIn_add (slotsIn_ofConst _) h)

/-- A tactic for goals "every slot that this form names has S", where the form is made by sums,
differences, factors and constants from forms of which that is known. -/
local macro "slots" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | with_reducible exact slotsIn_ofConst _
  | with_reducible exact sl_zero
  | with_reducible refine sl_high _ _ _ ?_
  | with_reducible refine slotsIn_scale _ ?_
  | with_reducible refine slotsIn_sub ?_ ?_
  | with_reducible refine slotsIn_add ?_ ?_
  | with_reducible refine slotsIn_addMul _ ?_ ?_)

/-- Whatever Env.site returns, the low key of a rounding site, names slots with S alone, where the
quotient SQ does and whatever the reading of the high digits returns does. -/
theorem gs_site (w : E) {SQ : Aff} (k form : ℕ) {Srh : Unit → Option Aff} (hQ : SlotsIn S SQ)
    (hS : Gives (Srh ()) (SlotsIn S)) : Gives (Env.site w SQ k form Srh) (SlotsIn S) := by
  unfold Env.site
  dsimp only
  refine Gives.ite (Gives.pure ?_) (Gives.bind hS fun a ha => Gives.pure ?_)
  · slots
  · slots

/-- A tactic for goals "whatever this do-block in Option returns names slots with S alone", where
the block makes a form from what the readers of the tables return. -/
local macro "walk " S:term : tactic => `(tactic| repeat' first
  | with_reducible exact gives_SA _ _ _ _
  | with_reducible exact gives_SBA _ _ _ _ _ _ _
  | with_reducible exact gives_SxsA _ _ _
  | with_reducible exact gives_shSum _ _ _ _ _
  | with_reducible exact gives_shA _ _ _ _
  | with_reducible exact gives_U3at _ _
  | with_reducible exact Gives.none
  | with_reducible refine Gives.ite ?_ ?_
  | with_reducible refine gs_site _ _ _ ?_ ?_
  | with_reducible refine gives_sumForms fun _ => ?_
  | with_reducible refine Gives.bind (Φ := SlotsIn $S) ?_ fun _ _ => ?_
  | with_reducible refine Gives.pure ?_
  | with_reducible assumption
  | with_reducible exact slotsIn_ofConst _
  | with_reducible exact sl_zero
  | with_reducible refine sl_high _ _ _ ?_
  | with_reducible refine slotsIn_scale _ ?_
  | with_reducible refine slotsIn_sub ?_ ?_
  | with_reducible refine slotsIn_add ?_ ?_
  | with_reducible refine slotsIn_addMul _ ?_ ?_)

/-- Whatever Env.lineGU returns names slots with S alone. -/
theorem gs_lineGU (up : Bool) (lam : ℕ) (ew wh : Array E) :
    Gives (v.lineGU up lam ew wh) (SlotsIn S) := by
  unfold Env.lineGU
  dsimp only
  walk S

/-- The like for Env.lineGUH. -/
theorem gs_lineGUH (up : Bool) (lam : ℕ) (ew wh : Array E) :
    Gives (v.lineGUH up lam ew wh) (SlotsIn S) := by
  unfold Env.lineGUH
  dsimp only
  walk S

/-- The like for Env.lineQK. -/
theorem gs_lineQK (hi : Bool) (lam : ℕ) (ew wh : Array E) :
    Gives (v.lineQK hi lam ew wh) (SlotsIn S) := by
  unfold Env.lineQK
  dsimp only
  walk S

/-- The like for Env.lineROW. -/
theorem gs_lineROW (lam : ℕ) (ew : Array E) : Gives (v.lineROW lam ew) (SlotsIn S) := by
  unfold Env.lineROW
  dsimp only
  refine Gives.skip fun t => Gives.skip fun trow => gives_sumForms fun x => ?_
  exact Gives.mapP (gives_U3at _ _) fun a ha => slotsIn_add ha (slotsIn_ofConst _)

/-- The like for Env.lineDD. -/
theorem gs_lineDD (lamM : ℕ) (ew : Array E) : Gives (v.lineDD lamM ew) (SlotsIn S) := by
  unfold Env.lineDD
  dsimp only
  refine Gives.bind (Φ := fun s : Aff × Aff => SlotsIn S s.1 ∧ SlotsIn S s.2) ?_
    fun r hr => Gives.pure hr.1
  refine gives_foldlM_inv (P := fun s : Aff × Aff => SlotsIn S s.1 ∧ SlotsIn S s.2)
    (fun s x hs => ?_) _ _ ⟨sl_zero, sl_zero⟩
  refine Gives.bind (gives_shA (S := S) _ _ _ _) fun a ha =>
    Gives.bind (gives_shA (S := S) _ _ _ _) fun b hb => Gives.pure ⟨?_, ?_⟩
  · exact slotsIn_addMul _ hs.1 (slotsIn_add ha hs.2)
  · exact slotsIn_add hs.2 hb

set_option maxRecDepth 8000 in
/-- **The form of the keys of a segment at a layer**: whatever line returns names slots with S
alone, at every S. -/
theorem gs_line (sn : String) (lam : ℕ) (ew wh : Array E) :
    Gives (v.line sn lam ew wh) (SlotsIn S) := by
  unfold Env.line
  dsimp only
  repeat' first
    | with_reducible exact gs_lineGU _ _ _ _
    | with_reducible exact gs_lineGUH _ _ _ _
    | with_reducible exact gs_lineQK _ _ _ _
    | with_reducible exact gs_lineROW _ _
    | with_reducible exact gs_lineDD _ _
    | with_reducible refine Gives.ite ?_ ?_
  all_goals walk S

/-- **One call's factor in the lookup's join**: whatever joinPart returns names slots with S alone,
at every S. -/
theorem gs_joinPart (alpha theta : E) (q : ℕ) (c : CallD) (weighed : Array Bool) :
    Gives (v.joinPart alpha theta q c weighed) (SlotsIn S) := by
  unfold Env.joinPart
  dsimp only
  refine Gives.bind (Φ := SlotsIn S) ?_ fun lines hl =>
    Gives.pure (slotsIn_add (slotsIn_ofConst _) hl)
  refine gives_foldlM_inv (P := SlotsIn S) (fun a s ha => ?_) _ _ sl_zero
  refine gives_foldlM_inv (P := SlotsIn S) (fun a lam ha => ?_) _ _ ha
  exact Gives.ite (Gives.some ha) (Gives.map (gs_line _ _ _ _) fun f hf => slotsIn_addMul _ ha hf)

open VerifiableInference.Desc.First.Shape (affSh)

/-- A form that names slots with "no slot" alone: its shape's list of slots is empty. -/
theorem slots_nil {f : Aff} (h : SlotsIn (fun _ => False) f) : (affSh f).slots = [] := by
  show f.slots.toList.map (·.1) = []
  cases hl : f.slots.toList with
  | nil => rfl
  | cons x l => exact (h x (by rw [hl]; exact List.mem_cons_self ..)).elim

/-- Gives passes through mapM: if whatever f returns has Φ, so has each member of a list that
l.mapM f returns. -/
theorem mapM_gives {α β : Type} {f : α → Option β} {Φ : β → Prop} (hf : ∀ x, Gives (f x) Φ) :
    ∀ (l : List α) (bs : List β), l.mapM f = some bs → ∀ b ∈ bs, Φ b
  | [], bs, h, b, hb => by
    obtain rfl : [] = bs := by simpa using h
    cases hb
  | x :: l, bs, h, b, hb => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : y :: ys = bs := Option.some.inj h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hf x _ hy
    · exact mapM_gives hf l ys hys b hb

/-- **No part of the join names a slot.** -/
theorem join_no_slot {alpha theta : E} {l : List ((CallD × Array Bool) × Nat)} {parts : List Aff}
    (h : (l.mapM fun x => v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts) :
    ∀ a ∈ parts, (affSh a).slots = [] :=
  fun a ha =>
    slots_nil (mapM_gives (f := fun x : (CallD × Array Bool) × Nat =>
      v.joinPart alpha theta x.2 x.1.1 x.1.2) (Φ := SlotsIn fun _ => False)
      (fun x => gs_joinPart alpha theta x.2 x.1.1 x.1.2) l parts h a ha)

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.sl_zero
#print axioms OnBytes.Desc.First.K4.Rt.sl_high
#print axioms OnBytes.Desc.First.K4.Rt.gs_site
#print axioms OnBytes.Desc.First.K4.Rt.gs_lineGU
#print axioms OnBytes.Desc.First.K4.Rt.gs_lineGUH
#print axioms OnBytes.Desc.First.K4.Rt.gs_lineQK
#print axioms OnBytes.Desc.First.K4.Rt.gs_lineROW
#print axioms OnBytes.Desc.First.K4.Rt.gs_lineDD
#print axioms OnBytes.Desc.First.K4.Rt.gs_line
#print axioms OnBytes.Desc.First.K4.Rt.gs_joinPart
#print axioms OnBytes.Desc.First.K4.Rt.slots_nil
#print axioms OnBytes.Desc.First.K4.Rt.mapM_gives
#print axioms OnBytes.Desc.First.K4.Rt.join_no_slot
