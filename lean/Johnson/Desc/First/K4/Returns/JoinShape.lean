-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/JoinShape.lean: THE LAYERS' OWN ROUNDS (K4): THE FORMS OF THE
LOOKUP's JOIN HAVE ONE SHAPE AT TWO ENVIRONMENTS THAT DIFFER IN THE POINTS ALONE. Congruences: each
statement compares two calls. Nothing is evaluated.

  EnvSame         two environments of the forms with one layout, one list of the tables' places, one
                  number of columns, one number of the array of the reads, one table of scales and
                  one group. EnvSame.lay, EnvSame.isMoe: Env.lay and Env.isMoe answer alike at
                  the two.
  map_rel, SA_rel, SBA_rel, SxsA_rel, shSum_rel, shA_rel, optRel_none, high_rel, site_rel   the
                  readers and the two keys of a rounding site, under two lists of weights.
  lineGU_rel, lineGUH_rel, lineQK_rel, lineROW_rel, lineDD_rel, **line_rel**   the form of a
                  segment's keys, at all 34 names (Env.line, OnBytes/Model/LayerForms.lean).
  **joinPart_rel**   a call's factor in the join.
Each: both calls refuse, or neither does and the forms have one shape (SameSh,
Johnson/Desc/First/K4/Returns/FormsShape.lean: the same entries and slots, in order).

Limits. NO FUNCTION IS SHOWN TO RETURN ANYWHERE. EnvSame ASKS MORE THAN ALL CONCLUSIONS BUT ONE
NEED: its fields sc and g serve only to rewrite shifts to one value, and by high_rel and site_rel,
which hold at two different shifts, a shift does not bear on a shape; with EnvSame cut to its field
keys the file's other 17 laws went through Lean in a trial outside the library (a scratch sheet);
EnvSame.lay, whose conclusion needs g, falls with the field. map_rel is the library's
OnBytes.Flat.optRel_map' (OnBytes/Flat/LinksFreeFork.lean) but for the letters' names. The proofs go
by four local tactic macros (samesh, shaped1, shaped, terms), line_rel under "set_option maxRecDepth
8000 in"; the default table of scales is struck as an instance for this file. Nothing on what a form
is worth. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FormsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.RtPub (EnvKeys U3at_eq shA_eq shIn_eq xbA_eq longA_eq optRel_ite
  optRel_pure)
open OnBytes.Desc.First.K4.Total (tabAt_skel tensorAt_skel)
open VerifiableInference.Desc.First.Shape

/-- Two environments of the forms that differ at most in the lookup's points. -/
structure EnvSame (v v₀ : Env) : Prop where
  keys : EnvKeys v v₀
  sc : v.sc = v₀.sc
  g : v.g = v₀.g

variable {v v₀ : Env}

theorem EnvSame.lay (S : EnvSame v v₀) (lam : Nat) : v.lay lam = v₀.lay lam := by
  unfold Env.lay
  rw [S.g, S.keys.y]

theorem EnvSame.isMoe (S : EnvSame v v₀) (lam : Nat) : v.isMoe lam = v₀.isMoe lam := by
  unfold Env.isMoe
  rw [S.keys.y]

/-- Forms of one shape, through the forms' operations. -/
local macro "samesh" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | with_reducible exact SameSh.refl _
  | with_reducible exact SameSh.const _ _
  | with_reducible refine SameSh.add ?_ ?_
  | with_reducible refine SameSh.sub ?_ ?_
  | with_reducible refine SameSh.scale ?_ _ _
  | with_reducible refine SameSh.addMul ?_ ?_ _ _)

theorem map_rel {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x y : Option α} {f g : α → β}
    (h : OptRel S x y) (hf : ∀ a b, S a b → R (f a) (g b)) : OptRel R (x.map f) (y.map g) := by
  cases x <;> cases y
  · trivial
  · exact h.elim
  · exact h.elim
  · exact hf _ _ h

theorem SA_rel (S : EnvSame v v₀) {wh wh₀ : Array E} (hw : wh.size = wh₀.size) (X : String)
    (i : Nat) (Z : String) : OptRel SameSh (v.SA wh X i Z) (v₀.SA wh₀ X i Z) := by
  unfold Env.SA
  rw [tensorAt_skel S.keys.skel, hw]
  refine optRel_bind_same fun x => sumForms_rel _ fun xh => ?_
  rw [longA_eq S.keys]
  exact pair_rel _ _ _

theorem SBA_rel (S : EnvSame v v₀) (wh wh₀ : Array E) (a b : Nat) (X : String) (i : Nat)
    (Z : String) (x0 : Nat) : OptRel SameSh (v.SBA wh a b X i Z x0) (v₀.SBA wh₀ a b X i Z x0) := by
  unfold Env.SBA
  rw [tensorAt_skel S.keys.skel, S.keys.y]
  refine optRel_bind_same fun x => sumForms_rel _ fun k => ?_
  dsimp only
  rw [longA_eq S.keys]
  exact pair_rel _ _ _

theorem SxsA_rel (S : EnvSame v v₀) (wh wh₀ : Array E) (Z : String) (sg : Nat) :
    OptRel SameSh (v.SxsA wh Z sg) (v₀.SxsA wh₀ Z sg) := by
  unfold Env.SxsA
  dsimp only
  rw [S.keys.y, tabAt_skel S.keys.skel]
  refine optRel_bind_same fun tb => optRel_bind_same fun txs => sumForms_rel _ fun xh => ?_
  rw [xbA_eq S.keys, longA_eq S.keys]
  exact pair_rel _ _ _

theorem shSum_rel (S : EnvSame v v₀) (ew ew₀ : Array E) (n : Nat) (X P : String) (i : Nat) :
    OptRel SameSh (v.shSum ew n X P i) (v₀.shSum ew₀ n X P i) := by
  unfold Env.shSum
  dsimp only
  rw [tensorAt_skel S.keys.skel]
  refine sumForms_rel _ fun x => ?_
  rw [shIn_eq S.keys]
  exact pair_rel _ _ _

theorem shA_rel (S : EnvSame v v₀) (X P : String) (i j : Nat) :
    OptRel SameSh (v.shA X P i j) (v₀.shA X P i j) := by
  rw [shA_eq S.keys]
  exact OptRel.refl SameSh.refl _

theorem optRel_none : OptRel SameSh none none := trivial

theorem high_rel (w w' : E) {a a' : Aff} (h : SameSh a a') (k k' form form' : Nat) :
    SameSh (Env.high w a k form) (Env.high w' a' k' form') := by
  unfold Env.high
  samesh

theorem site_rel (w w' : E) {SQ SQ' : Aff} (hq : SameSh SQ SQ') (k k' form : Nat)
    {Srh Srh' : Unit → Option Aff} (h : OptRel SameSh (Srh ()) (Srh' ())) :
    OptRel SameSh (Env.site w SQ k form Srh) (Env.site w' SQ' k' form Srh') := by
  unfold Env.site
  dsimp only
  refine optRel_ite (optRel_pure (by samesh)) ?_
  exact optRel_bind h fun a a' _ => optRel_pure (by samesh)

/-- Two do-blocks over Option of one build, at two environments that differ in the points alone. -/
local macro "shaped1 " S:term ", " hw:term : tactic => `(tactic| first
  | with_reducible assumption
  | with_reducible exact SA_rel $S $hw _ _ _
  | with_reducible exact SBA_rel $S _ _ _ _ _ _ _ _
  | with_reducible exact SxsA_rel $S _ _ _ _
  | with_reducible exact shSum_rel $S _ _ _ _ _ _
  | with_reducible exact shA_rel $S _ _ _ _
  | with_reducible exact SameSh.const _ _
  | with_reducible refine optRel_ite ?_ ?_
  | with_reducible refine site_rel _ _ ?_ _ _ _ ?_
  | with_reducible refine optRel_pure ?_
  | with_reducible refine high_rel _ _ ?_ _ _ _ _
  | with_reducible refine SameSh.add ?_ ?_
  | with_reducible refine SameSh.sub ?_ ?_
  | with_reducible refine SameSh.scale ?_ _ _
  | with_reducible refine SameSh.addMul ?_ ?_ _ _
  | with_reducible refine optRel_bind (S := SameSh) ?_ fun _ _ _ => ?_)

local macro "shaped " S:term ", " hw:term : tactic =>
  `(tactic| iterate 16 (try any_goals (shaped1 $S, $hw)))

theorem lineGU_rel (S : EnvSame v v₀) (up : Bool) (lam : Nat) (ew ew₀ : Array E)
    {wh wh₀ : Array E} (hw : wh.size = wh₀.size) :
    OptRel SameSh (v.lineGU up lam ew wh) (v₀.lineGU up lam ew₀ wh₀) := by
  unfold Env.lineGU
  dsimp only
  rw [S.isMoe, S.keys.y, S.sc, S.lay]
  shaped S, hw

theorem lineGUH_rel (S : EnvSame v v₀) (up : Bool) (lam : Nat) (ew ew₀ : Array E)
    {wh wh₀ : Array E} (hw : wh.size = wh₀.size) :
    OptRel SameSh (v.lineGUH up lam ew wh) (v₀.lineGUH up lam ew₀ wh₀) := by
  unfold Env.lineGUH
  dsimp only
  rw [S.isMoe, S.keys.y, S.sc, S.lay]
  shaped S, hw

theorem lineQK_rel (S : EnvSame v v₀) (hi : Bool) (lam : Nat) (ew ew₀ wh wh₀ : Array E) :
    OptRel SameSh (v.lineQK hi lam ew wh) (v₀.lineQK hi lam ew₀ wh₀) := by
  unfold Env.lineQK
  dsimp only
  rw [S.keys.y, S.sc, S.lay]
  shaped S, rfl

theorem lineROW_rel (S : EnvSame v v₀) (lam : Nat) {ew ew₀ : Array E} (he : ew.size = ew₀.size) :
    OptRel SameSh (v.lineROW lam ew) (v₀.lineROW lam ew₀) := by
  unfold Env.lineROW
  dsimp only
  rw [tabAt_skel S.keys.skel, S.keys.y, he]
  refine optRel_bind_same fun t => optRel_bind_same fun trow => sumForms_rel _ fun x => ?_
  rw [U3at_eq S.keys]
  exact map_rel (OptRel.refl SameSh.refl _) fun a b h => SameSh.add h (SameSh.refl _)

theorem lineDD_rel (S : EnvSame v v₀) (lamM : Nat) (ew ew₀ : Array E) :
    OptRel SameSh (v.lineDD lamM ew) (v₀.lineDD lamM ew₀) := by
  unfold Env.lineDD
  rw [S.keys.y]
  simp only [shA_eq S.keys]
  have key : ∀ (l : List Nat) (s s' : Aff × Aff), SameSh s.1 s'.1 ∧ SameSh s.2 s'.2 →
      OptRel (fun r r' : Aff × Aff => SameSh r.1 r'.1 ∧ SameSh r.2 r'.2)
        (l.foldlM (fun (s : Aff × Aff) x => do
          let a := s.1.addMul ((← v₀.shA "lr" "zt" lamM x) + s.2) (negE (ew.getD x zeroE))
          pure (a, s.2 + (← v₀.shA "sel" "zt" lamM x))) s)
        (l.foldlM (fun (s : Aff × Aff) x => do
          let a := s.1.addMul ((← v₀.shA "lr" "zt" lamM x) + s.2) (negE (ew₀.getD x zeroE))
          pure (a, s.2 + (← v₀.shA "sel" "zt" lamM x))) s') := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons x l ih =>
      intro s s' h
      rw [List.foldlM_cons, List.foldlM_cons]
      refine optRel_bind (S := fun r r' : Aff × Aff => SameSh r.1 r'.1 ∧ SameSh r.2 r'.2) ?_
        fun a b hab => ih a b hab
      refine optRel_bind_same fun p => optRel_bind_same fun q => optRel_pure ?_
      exact ⟨SameSh.addMul h.1 (SameSh.add (SameSh.refl _) h.2) _ _,
        SameSh.add h.2 (SameSh.refl _)⟩
  exact optRel_bind (key _ _ _ ⟨SameSh.refl _, SameSh.refl _⟩) fun r r' h => optRel_pure h.1

/-- A sum whose terms are made by a do-block: a pair of a form and a weight. -/
local macro "terms " S:term : tactic => `(tactic| (
  refine sumForms_rel _ fun _ => ?_
  simp only [shA_eq (EnvSame.keys $S)]
  repeat' first
    | with_reducible refine optRel_bind_same fun _ => ?_
    | with_reducible exact optRel_pure (SameSh.refl _)))

set_option maxRecDepth 8000 in
/-- **The form of a segment's keys at two environments that differ in the points alone, under two
lists of weights of one size each**: both are missing, or neither is and they have one shape. -/
theorem line_rel (S : EnvSame v v₀) (sn : String) (lam : Nat) {ew ew₀ wh wh₀ : Array E}
    (he : ew.size = ew₀.size) (hw : wh.size = wh₀.size) :
    OptRel SameSh (v.line sn lam ew wh) (v₀.line sn lam ew₀ wh₀) := by
  obtain ⟨y, sc, g, iU3, K3, tab, zk⟩ := v
  obtain ⟨y₀, sc₀, g₀, iU3₀, K3₀, tab₀, zk₀⟩ := v₀
  obtain rfl : y = y₀ := S.keys.y
  unfold Env.line
  dsimp only
  repeat' first
    | with_reducible exact lineGU_rel S _ _ _ _ hw
    | with_reducible exact lineGUH_rel S _ _ _ _ hw
    | with_reducible exact lineQK_rel S _ _ _ _ _ _
    | with_reducible exact lineROW_rel S _ he
    | with_reducible exact lineDD_rel S _ _ _
    | with_reducible refine optRel_ite ?_ ?_
  any_goals (with_reducible exact optRel_none)
  any_goals (terms S)
  shaped S, hw
  all_goals (terms S)

/-- **A call's factor in the lookup's join, at two environments that differ in the points alone**:
both are missing, or neither is and they have one shape. -/
theorem joinPart_rel (S : EnvSame v v₀) (alpha theta alpha₀ theta₀ : E) (q : Nat) (c : CallD)
    (weighed weighed₀ : Array Bool) :
    OptRel SameSh (v.joinPart alpha theta q c weighed)
      (v₀.joinPart alpha₀ theta₀ q c weighed₀) := by
  unfold Env.joinPart
  dsimp only
  rw [S.keys.y]
  refine optRel_bind (S := SameSh) ?_ fun a a' h =>
    optRel_pure (SameSh.add (SameSh.const _ _) h)
  refine foldlM_rel _ _ _ (SameSh.refl _) fun s a a' h => ?_
  refine foldlM_rel _ _ _ h fun lam b b' hb => ?_
  rw [S.isMoe]
  refine optRel_ite hb (map_rel (line_rel S _ _ ?_ ?_) fun f f' hf => SameSh.addMul hb hf _ _)
  · simp [Env.ewFrom]
  · split <;> simp [Env.ewhFrom]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.EnvSame.lay
#print axioms OnBytes.Desc.First.K4.Rt.EnvSame.isMoe
#print axioms OnBytes.Desc.First.K4.Rt.map_rel
#print axioms OnBytes.Desc.First.K4.Rt.SA_rel
#print axioms OnBytes.Desc.First.K4.Rt.SBA_rel
#print axioms OnBytes.Desc.First.K4.Rt.SxsA_rel
#print axioms OnBytes.Desc.First.K4.Rt.shSum_rel
#print axioms OnBytes.Desc.First.K4.Rt.shA_rel
#print axioms OnBytes.Desc.First.K4.Rt.optRel_none
#print axioms OnBytes.Desc.First.K4.Rt.high_rel
#print axioms OnBytes.Desc.First.K4.Rt.site_rel
#print axioms OnBytes.Desc.First.K4.Rt.lineGU_rel
#print axioms OnBytes.Desc.First.K4.Rt.lineGUH_rel
#print axioms OnBytes.Desc.First.K4.Rt.lineQK_rel
#print axioms OnBytes.Desc.First.K4.Rt.lineROW_rel
#print axioms OnBytes.Desc.First.K4.Rt.lineDD_rel
#print axioms OnBytes.Desc.First.K4.Rt.line_rel
#print axioms OnBytes.Desc.First.K4.Rt.joinPart_rel
#print axioms OnBytes.Desc.First.K4.Rt.EnvSame
