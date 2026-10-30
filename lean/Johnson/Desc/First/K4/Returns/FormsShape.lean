-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FormsShape.lean: THE LAYERS' OWN ROUNDS (K4): THE SHAPES OF THE FORMS
THAT ITS TWO LISTINGS OF CLAIMS MAKE (front, back: OnBytes/Desc/First/K4/Claims.lean) HANG ON THE
SHAPE OF WHAT THE HEARING LEFT. Congruences: each statement compares two calls. Nothing is
evaluated.

A form's shape (affSh, Johnson/Desc/First/Shape/Parts.lean): the entries and the slots that it
names, in the form's order, without a coefficient and without the constant.

  SameSh          two forms of one shape; its rules through the forms' operations (addMul, add, sub,
                  scale, const); shapes_eq: two lists, member by member.
  foldl_rel, foldlM_rel, pair_rel, sumForms_rel   folds and sums of forms under two lists of
                  weights.
  rowCells_eq, rowAt_eq, row5At_eq, rowR_eq, digitsAt_eq, twoM_eq   EQUATIONS: these readers read
                  four fields of the environment alone (the last: the scales and the group too).
  LevelAlike      two layers of a product tree of one shape.
  normsForms_rel, rowBatchForm_rel, rowsForms_eq, termsForms_eq, endsForms_rel, gatedForms_rel,
  oneHotForms_eq, planesAt_rel, planesParts_rel, embeddingForm_rel   THE BUILDERS OF FORMS, group by
                  group: at two environments with one layout, one list of the tables' places, one
                  number of columns and one number of the array of the reads (EnvKeys,
                  Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean): both calls refuse, or neither
                  does and the forms have one shape, member by member. Three of them give the same
                  forms outright.
  OwnAlike        two records of what the hearing leaves: one shape (ownSh,
                  Johnson/Desc/First/Shape/Own.lean), one layout, one table of scales.
  **front_rel**   the claims in front of the smallness test's, the lookup's own not listed.
  **back_rel**    the claims behind it.

Limits. NO FUNCTION IS SHOWN TO RETURN ANYWHERE. Nothing on what a form, a weight or a shown value
is worth, nor on a form's constant. front with the lookup's own claims listed is not treated.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Pub.PanelsKeys
import Johnson.Desc.First.Shape.Own
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.RtPub (EnvKeys U3at_eq shA_eq xbA_eq longA_eq optRel_of_isSome optRel_ite
  optRel_pure)
open OnBytes.Desc.First.K4.Total (tabAt_skel hiTab_same)
open VerifiableInference.Desc.First.Shape

/-! ## Two forms of one shape -/

/-- Two forms name the same entries and the same slots, in the same order. -/
def SameSh (a b : Aff) : Prop := affSh a = affSh b

theorem SameSh.refl (a : Aff) : SameSh a a := rfl

theorem SameSh.addMul {a a' b b' : Aff} (h1 : SameSh a a') (h2 : SameSh b b') (k k' : E) :
    SameSh (a.addMul b k) (a'.addMul b' k') := by
  unfold SameSh at h1 h2 ⊢
  rw [affSh_addMul, affSh_addMul, h1, h2]

theorem SameSh.add {a a' b b' : Aff} (h1 : SameSh a a') (h2 : SameSh b b') :
    SameSh (a + b) (a' + b') := SameSh.addMul h1 h2 _ _

theorem SameSh.sub {a a' b b' : Aff} (h1 : SameSh a a') (h2 : SameSh b b') :
    SameSh (a - b) (a' - b') := SameSh.addMul h1 h2 _ _

theorem SameSh.scale {a a' : Aff} (h : SameSh a a') (k k' : E) :
    SameSh (a.scale k) (a'.scale k') := SameSh.addMul (SameSh.refl _) h _ _

theorem SameSh.const (x y : E) : SameSh (Aff.ofConst x) (Aff.ofConst y) := rfl

/-- Lists of forms of one shape, member by member: the lists of their shapes are one. -/
theorem shapes_eq {l l' : List Aff} (h : All2 SameSh l l') : l.map affSh = l'.map affSh :=
  h.map_eq fun _ _ e => e

theorem all2_refl (l : List Aff) : All2 SameSh l l := All2.refl SameSh.refl l

/-- A fold of forms. -/
theorem foldl_rel {α : Type} {F G : Aff → α → Aff} :
    ∀ (l : List α) (a b : Aff), SameSh a b → (∀ x a b, SameSh a b → SameSh (F a x) (G b x)) →
      SameSh (l.foldl F a) (l.foldl G b)
  | [], _, _, h, _ => h
  | x :: l, a, b, h, hs => foldl_rel l _ _ (hs x a b h) hs

/-- A fold of forms that may refuse. -/
theorem foldlM_rel {α : Type} {F G : Aff → α → Option Aff} :
    ∀ (l : List α) (a b : Aff), SameSh a b →
      (∀ x a b, SameSh a b → OptRel SameSh (F a x) (G b x)) →
      OptRel SameSh (l.foldlM F a) (l.foldlM G b)
  | [], _, _, h, _ => h
  | x :: l, a, b, h, hs => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact optRel_bind (hs x a b h) fun c d hcd => foldlM_rel l c d hcd hs

/-- One reader's form, the same at both sides, under two weights. -/
theorem pair_rel (o : Option Aff) (k k' : Aff → E) :
    OptRel (fun t t' : Aff × E => SameSh t.1 t'.1) (o.map fun a => (a, k a))
      (o.map fun a => (a, k' a)) := by
  cases o
  · trivial
  · exact SameSh.refl _

/-- A sum of forms under weights. -/
theorem sumForms_rel (n : Nat) {f g : Nat → Option (Aff × E)}
    (h : ∀ x, OptRel (fun t t' : Aff × E => SameSh t.1 t'.1) (f x) (g x)) :
    OptRel SameSh (sumForms n f) (sumForms n g) := by
  unfold sumForms
  refine foldlM_rel _ _ _ (SameSh.refl _) fun x a b hab => ?_
  have h1 := h x
  cases hf : f x <;> cases hg : g x <;> rw [hf, hg] at h1
  · trivial
  · exact h1.elim
  · exact h1.elim
  · exact SameSh.addMul hab h1 _ _

/-! ## The readers of a norm's row, as equations: they read four fields of the environment alone -/

variable {v v₀ : Env}

theorem rowCells_eq (S : EnvKeys v v₀) (P : String) (i cells : Nat) :
    v.rowCells P i cells = v₀.rowCells P i cells := by
  unfold Env.rowCells
  rw [tabAt_skel S.skel, S.y]
  simp only [U3at_eq S]

theorem rowAt_eq (S : EnvKeys v v₀) (P : String) (i : Nat) : v.rowAt P i = v₀.rowAt P i := by
  unfold Env.rowAt
  rw [rowCells_eq S]

theorem row5At_eq (S : EnvKeys v v₀) (P : String) (i : Nat) : v.row5At P i = v₀.row5At P i := by
  unfold Env.row5At
  rw [rowCells_eq S]

theorem rowR_eq (S : EnvKeys v v₀) (P : String) (i : Nat) : v.rowR P i = v₀.rowR P i := by
  unfold Env.rowR
  rw [S.y, row5At_eq S, rowAt_eq S]

theorem digitsAt_eq (S : EnvKeys v v₀) (P : String) (i : Nat) :
    digitsAt v P i = digitsAt v₀ P i := by
  unfold digitsAt
  rw [rowCells_eq S]

theorem twoM_eq (S : EnvKeys v v₀) (hsc : v.sc = v₀.sc) (hg : v.g = v₀.g) (i : Nat) :
    twoM v i = twoM v₀ i := by
  unfold twoM Env.lay
  rw [hsc, hg, S.y]

/-! ## The builders of forms -/

/-- Two layers of a product tree of one shape. -/
def LevelAlike (l l₀ : Level) : Prop := levelSh l = levelSh l₀

theorem LevelAlike.r {l l₀ : Level} (h : LevelAlike l l₀) : l.r.size = l₀.r.size :=
  congrArg LevelSh.r h
theorem LevelAlike.sL {l l₀ : Level} (h : LevelAlike l l₀) : l.sL = l₀.sL := congrArg LevelSh.sL h
theorem LevelAlike.sR {l l₀ : Level} (h : LevelAlike l l₀) : l.sR = l₀.sR := congrArg LevelSh.sR h
theorem LevelAlike.row {l l₀ : Level} (h : LevelAlike l l₀) : SameSh l.row l₀.row :=
  congrArg LevelSh.row h

/-- Group 2, the sums of squares. -/
theorem normsForms_rel (P : Pub) (S : EnvKeys v v₀) {H H₀ : Heard}
    (hw : LevelAlike H.wpl H₀.wpl) :
    OptRel (All2 SameSh) (normsForms P v H) (normsForms P v₀ H₀) := by
  unfold normsForms
  dsimp only
  simp only [tabAt_skel S.skel]
  refine optRel_bind_same fun txs => optRel_bind_same fun _ => optRel_bind_same fun tI =>
    optRel_bind_same fun tA => ?_
  refine optRel_bind (S := fun _ _ => True) (optRel_of_isSome (hiTab_same hw.r _ _))
    fun e e' _ => ?_
  refine optRel_bind (S := SameSh) (sumForms_rel _ fun x => ?_) fun s s' hs => ?_
  · simp only [U3at_eq S]
    exact pair_rel _ _ _
  · refine optRel_pure (.cons hw.row (.cons ?_ (.cons ?_ .nil)))
    · rw [hw.sL, hw.sR]
      exact SameSh.refl _
    · rw [hw.sL]
      exact SameSh.add (SameSh.refl _) hs

/-- Group 3, first claim. -/
theorem rowBatchForm_rel (y : Lay) {H H₀ : Heard} (h1 : H.sPv = H₀.sPv)
    (h2 : H.tV.sCl = H₀.tV.sCl) : SameSh (rowBatchForm y H) (rowBatchForm y H₀) := by
  unfold rowBatchForm
  rw [h1, h2]
  exact foldl_rel _ _ _ (SameSh.refl _) fun i a b hab => SameSh.addMul hab (SameSh.refl _) _ _

/-- Groups 4 to 6: the same forms outright. -/
theorem rowsForms_eq (S : EnvKeys v v₀) (hsc : v.sc = v₀.sc) (hg : v.g = v₀.g) {H H₀ : Heard}
    (h1 : H.tV.sEnd = H₀.tV.sEnd) (h2 : H.sW = H₀.sW) (h3 : H.sPv = H₀.sPv) :
    rowsForms v H = rowsForms v₀ H₀ := by
  unfold rowsForms
  dsimp only
  rw [S.y, h1, h2, h3]
  simp only [digitsAt_eq S, twoM_eq S hsc hg]

/-- Group 7: the same forms outright, where the second token sumcheck's end values lie at one slot.
-/
theorem termsForms_eq (S : EnvKeys v v₀) {H H₀ : Heard}
    (h : H.tT.map (·.sEnd) = H₀.tT.map (·.sEnd)) : termsForms v H = termsForms v₀ H₀ := by
  unfold termsForms
  dsimp only
  rw [S.y]
  simp only [rowR_eq S, shA_eq S]
  cases h1 : H.tT with
  | none =>
    cases h2 : H₀.tT with
    | none => rfl
    | some t' =>
      rw [h1, h2] at h
      cases h
  | some t =>
    cases h2 : H₀.tT with
    | none =>
      rw [h1, h2] at h
      cases h
    | some t' =>
      rw [h1, h2] at h
      have e : t.sEnd = t'.sEnd := Option.some.inj h
      simp only [Option.bind_eq_bind, Option.bind_some, e]

/-- The two claims on the end values of a layer of the gated products. -/
theorem endsForms_rel (S : EnvKeys v v₀) {o o₀ : Level} (h : LevelAlike o o₀) (e e' : Array E)
    (t rows blocks stride : Nat) (lamOf : Nat → Nat) (first : Nat) :
    OptRel (All2 SameSh) (endsForms v o e t rows blocks stride lamOf first)
      (endsForms v₀ o₀ e' t rows blocks stride lamOf first) := by
  unfold endsForms
  dsimp only
  rw [S.y, h.sL, h.sR]
  refine optRel_bind_same fun ts => optRel_bind_same fun tu => ?_
  refine optRel_bind (S := SameSh) (sumForms_rel _ fun x => ?_) fun a a' ha => ?_
  · simp only [longA_eq S]
    exact pair_rel _ _ _
  refine optRel_bind (S := SameSh) (sumForms_rel _ fun x => ?_) fun b b' hb => ?_
  · simp only [longA_eq S]
    exact pair_rel _ _ _
  exact optRel_pure (.cons (SameSh.add (SameSh.refl _) ha)
    (.cons (SameSh.add (SameSh.refl _) hb) .nil))

/-- Groups 8 and 9, the gated products. -/
theorem gatedForms_rel (P : Pub) (S : EnvKeys v v₀) {hd hd₀ : Level} {hd2 hd2₀ : Option Level}
    (h1 : LevelAlike hd hd₀) (h2 : OptRel LevelAlike hd2 hd2₀) :
    OptRel (All2 SameSh) (gatedForms P v hd hd2) (gatedForms P v₀ hd₀ hd2₀) := by
  unfold gatedForms
  dsimp only
  simp only [tabAt_skel S.skel]
  refine optRel_bind (S := fun _ _ => True) (optRel_of_isSome (hiTab_same h1.r _ _))
    fun e e' _ => ?_
  refine optRel_bind_same fun tA => ?_
  refine optRel_bind (endsForms_rel S h1 e e' _ _ _ _ _ _) fun a a' ha => ?_
  refine optRel_bind h2 fun o o₀ ho => ?_
  refine optRel_bind (S := fun _ _ => True) (optRel_of_isSome (hiTab_same ho.r _ _))
    fun e2 e2' _ => ?_
  refine optRel_bind_same fun tB => ?_
  refine optRel_bind (endsForms_rel S ho e2 e2' _ _ _ _ _ _) fun b b' hb => ?_
  exact optRel_pure (.cons h1.row (ha.append (.cons ho.row hb)))

/-- Group 10: the same forms outright. -/
theorem oneHotForms_eq (S : EnvKeys v v₀) : oneHotForms v = oneHotForms v₀ := by
  unfold oneHotForms
  rw [S.y]
  simp only [shA_eq S]

/-- The planes at one of the two points. -/
theorem planesAt_rel {g g₀ : Forest.Heard} (h : g.shape = g₀.shape) (lm e : Nat)
    (bit : Nat → Nat → Option Aff) :
    OptRel SameSh (planesAt g lm e bit) (planesAt g₀ lm e bit) := by
  unfold planesAt
  dsimp only
  rw [h]
  refine foldlM_rel _ _ _ (SameSh.refl _) fun col a b hab => ?_
  cases bit e col
  · trivial
  · exact SameSh.addMul hab (SameSh.refl _) _ _

/-- Group 11, the lookup's three claims that read the planes. -/
theorem planesParts_rel (S : EnvKeys v v₀) {fo fo₀ : Forest.Heard} (h : fo.shape = fo₀.shape)
    (hb : fo.sBit = fo₀.sBit) :
    OptRel (fun x x' : Aff × List Aff => SameSh x.1 x'.1 ∧ All2 SameSh x.2 x'.2)
      (planesParts v fo) (planesParts v₀ fo₀) := by
  unfold planesParts
  dsimp only
  rw [S.y, h, hb]
  simp only [tabAt_skel S.skel, U3at_eq S]
  refine optRel_bind_same fun tB0 => optRel_bind_same fun tB1 => optRel_bind_same fun tP =>
    optRel_bind_same fun _ => ?_
  refine optRel_bind (planesAt_rel h _ _ _) fun a0 a0' h0 => ?_
  refine optRel_bind (planesAt_rel h _ _ _) fun a1 a1' h1 => ?_
  refine optRel_bind_same fun count => ?_
  exact optRel_pure ⟨SameSh.scale h0 _ _,
    .cons (SameSh.sub (SameSh.refl _) h1) (.cons (SameSh.refl _) .nil)⟩

/-- Group 12, in the first group. -/
theorem embeddingForm_rel (S : EnvKeys v v₀) (H H₀ : Heard) (sVE : Nat) :
    OptRel SameSh (embeddingForm v H sVE) (embeddingForm v₀ H₀ sVE) := by
  unfold embeddingForm
  dsimp only
  rw [S.y]
  simp only [tabAt_skel S.skel]
  refine optRel_bind_same fun t => ?_
  refine optRel_bind (S := SameSh) (sumForms_rel _ fun kh => ?_) fun s s' hs => ?_
  · simp only [xbA_eq S]
    exact pair_rel _ _ _
  · exact optRel_pure (SameSh.add (SameSh.refl _) hs)

/-! ## What K4's hearing leaves, twice, of one shape -/

/-- Two records of what the hearing leaves: one shape, one layout, one table of scales. -/
structure OwnAlike (o o₀ : Own) : Prop where
  sh : ownSh o = ownSh o₀
  y : o.v.y = o₀.v.y
  sc : o.v.sc = o₀.v.sc

namespace OwnAlike
variable {o o₀ : Own}

theorem g (h : OwnAlike o o₀) : o.v.g = o₀.v.g := congrArg OwnSh.g h.sh

theorem tab (h : OwnAlike o o₀) : o.v.tab = o₀.v.tab := by
  have e : (o.v.tab.map fun x => (x.name, x.first, x.len)) =
      o₀.v.tab.map fun x => (x.name, x.first, x.len) := congrArg OwnSh.tab h.sh
  refine List.map_injective_iff.2 (fun a b hab => ?_) e
  cases a
  cases b
  simp only [Prod.mk.injEq] at hab
  obtain ⟨rfl, rfl, rfl⟩ := hab
  rfl

theorem keys (h : OwnAlike o o₀) : EnvKeys o.v o₀.v :=
  ⟨h.y, h.tab, congrArg OwnSh.K3 h.sh, congrArg OwnSh.iU3 h.sh⟩

theorem H (h : OwnAlike o o₀) : normsSh o.H = normsSh o₀.H := congrArg OwnSh.H h.sh

theorem wpl (h : OwnAlike o o₀) : LevelAlike o.H.wpl o₀.H.wpl := congrArg NormsSh.wpl h.H

theorem hd (h : OwnAlike o o₀) : LevelAlike o.hd o₀.hd := congrArg OwnSh.hd h.sh

theorem hd2 (h : OwnAlike o o₀) : OptRel LevelAlike o.hd2 o₀.hd2 := by
  have e : o.hd2.map levelSh = o₀.hd2.map levelSh := congrArg OwnSh.hd2 h.sh
  cases h1 : o.hd2 <;> cases h2 : o₀.hd2 <;> rw [h1, h2] at e
  · trivial
  · cases e
  · cases e
  · exact Option.some.inj e

theorem fo (h : OwnAlike o o₀) : heardAll o.H.fo = heardAll o₀.H.fo := congrArg NormsSh.fo h.H

theorem tV (h : OwnAlike o o₀) : tscSh o.H.tV = tscSh o₀.H.tV := congrArg NormsSh.tV h.H

theorem tT (h : OwnAlike o o₀) : o.H.tT.map (·.sEnd) = o₀.H.tT.map (·.sEnd) := by
  have e : o.H.tT.map tscSh = o₀.H.tT.map tscSh := congrArg NormsSh.tT h.H
  have e' := congrArg (Option.map TscSh.sEnd) e
  rw [Option.map_map, Option.map_map] at e'
  exact e'

theorem K (h : OwnAlike o o₀) : stackSh o.K = stackSh o₀.K := congrArg OwnSh.K h.sh

end OwnAlike

/-- **THE CLAIMS IN FRONT OF THE SMALLNESS TEST's, at two records of one shape**: both lists are
missing, or neither is and the forms have one shape, member by member. rowV, rowL: the two late
claims. -/
theorem front_rel (P : Pub) (g : Nat) {o o₀ : Own} (h : OwnAlike o o₀) {rowV rowV₀ rowL rowL₀ : Aff}
    (hV : SameSh rowV rowV₀) (hL : SameSh rowL rowL₀) :
    OptRel (All2 SameSh) (front false P g o rowV rowL) (front false P g o₀ rowV₀ rowL₀) := by
  unfold front
  have S := h.keys
  refine optRel_bind (normsForms_rel P S h.wpl) fun g2 g2' h2 => ?_
  rw [rowsForms_eq S h.sc h.g (congrArg TscSh.sEnd h.tV) (congrArg NormsSh.sW h.H)
    (congrArg NormsSh.sPv h.H), termsForms_eq S h.tT, oneHotForms_eq S]
  refine optRel_bind_same fun g46 => optRel_bind_same fun g7 => ?_
  refine optRel_bind (gatedForms_rel P S h.hd h.hd2) fun g89 g89' h89 => ?_
  refine optRel_bind_same fun g10 => ?_
  refine optRel_bind (planesParts_rel S (congrArg HeardAll.shape h.fo)
    (congrArg HeardAll.sBit h.fo)) fun g11 g11' h11 => ?_
  have key : ∀ g12 g12' : List Aff, All2 SameSh g12 g12' →
      All2 SameSh ((if false = true then o.H.fo.rows.toList else []) ++ g2 ++
        [rowBatchForm P.y o.H, rowV] ++ g46 ++ g7 ++ g89 ++ g10 ++ rowL :: g11.2 ++ g12)
        ((if false = true then o₀.H.fo.rows.toList else []) ++ g2' ++
        [rowBatchForm P.y o₀.H, rowV₀] ++ g46 ++ g7 ++ g89' ++ g10 ++ rowL₀ :: g11'.2 ++ g12') := by
    intro g12 g12' h12
    simp only [Bool.false_eq_true, if_false, List.nil_append]
    exact ((((((h2.append (.cons (rowBatchForm_rel P.y (congrArg NormsSh.sPv h.H)
      (congrArg TscSh.sCl h.tV)) (.cons hV .nil))).append (all2_refl g46)).append
      (all2_refl g7)).append h89).append (all2_refl g10)).append (.cons hL h11.2)).append h12
  have eVE : o.sVE = o₀.sVE := congrArg OwnSh.sVE h.sh
  dsimp only
  refine optRel_ite ?_ ?_
  · refine optRel_bind (S := All2 SameSh) ?_ fun g12 g12' h12 => optRel_pure (key _ _ h12)
    rw [eVE]
    have e := embeddingForm_rel S o.H o₀.H o₀.sVE
    cases h1 : embeddingForm o.v o.H o₀.sVE <;> cases h2 : embeddingForm o₀.v o₀.H o₀.sVE <;>
      rw [h1, h2] at e
    · trivial
    · exact e.elim
    · exact e.elim
    · exact .cons e .nil
  · exact optRel_pure (key [] [] .nil)

/-- **THE CLAIMS BEHIND THE SMALLNESS TEST's, at two records of one shape.** rowM: the merge's late
claim. -/
theorem back_rel {o o₀ : Own} (h : OwnAlike o o₀) {rowM rowM₀ : Aff} (hM : SameSh rowM rowM₀) :
    All2 SameSh (back o rowM) (back o₀ rowM₀) := by
  unfold back
  have k := h.K
  refine .cons (congrArg StackSh.rowS k) (.cons ?_ (.cons ?_ (.cons hM .nil)))
  · have e : o.K.sA0 = o₀.K.sA0 := congrArg StackSh.sA0 k
    rw [e]
    exact SameSh.sub (SameSh.refl _) (congrArg StackSh.Alin k)
  · have e : o.K.sB0 = o₀.K.sB0 := congrArg StackSh.sB0 k
    rw [e]
    exact SameSh.sub (SameSh.refl _) (congrArg StackSh.Blin k)

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.SameSh.refl
#print axioms OnBytes.Desc.First.K4.Rt.SameSh.addMul
#print axioms OnBytes.Desc.First.K4.Rt.SameSh.add
#print axioms OnBytes.Desc.First.K4.Rt.SameSh.sub
#print axioms OnBytes.Desc.First.K4.Rt.SameSh.scale
#print axioms OnBytes.Desc.First.K4.Rt.SameSh.const
#print axioms OnBytes.Desc.First.K4.Rt.shapes_eq
#print axioms OnBytes.Desc.First.K4.Rt.all2_refl
#print axioms OnBytes.Desc.First.K4.Rt.foldl_rel
#print axioms OnBytes.Desc.First.K4.Rt.foldlM_rel
#print axioms OnBytes.Desc.First.K4.Rt.pair_rel
#print axioms OnBytes.Desc.First.K4.Rt.sumForms_rel
#print axioms OnBytes.Desc.First.K4.Rt.rowCells_eq
#print axioms OnBytes.Desc.First.K4.Rt.rowAt_eq
#print axioms OnBytes.Desc.First.K4.Rt.row5At_eq
#print axioms OnBytes.Desc.First.K4.Rt.rowR_eq
#print axioms OnBytes.Desc.First.K4.Rt.digitsAt_eq
#print axioms OnBytes.Desc.First.K4.Rt.twoM_eq
#print axioms OnBytes.Desc.First.K4.Rt.LevelAlike.r
#print axioms OnBytes.Desc.First.K4.Rt.LevelAlike.sL
#print axioms OnBytes.Desc.First.K4.Rt.LevelAlike.sR
#print axioms OnBytes.Desc.First.K4.Rt.LevelAlike.row
#print axioms OnBytes.Desc.First.K4.Rt.normsForms_rel
#print axioms OnBytes.Desc.First.K4.Rt.rowBatchForm_rel
#print axioms OnBytes.Desc.First.K4.Rt.rowsForms_eq
#print axioms OnBytes.Desc.First.K4.Rt.termsForms_eq
#print axioms OnBytes.Desc.First.K4.Rt.endsForms_rel
#print axioms OnBytes.Desc.First.K4.Rt.gatedForms_rel
#print axioms OnBytes.Desc.First.K4.Rt.oneHotForms_eq
#print axioms OnBytes.Desc.First.K4.Rt.planesAt_rel
#print axioms OnBytes.Desc.First.K4.Rt.planesParts_rel
#print axioms OnBytes.Desc.First.K4.Rt.embeddingForm_rel
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.g
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.tab
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.keys
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.H
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.wpl
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.hd
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.hd2
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.fo
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.tV
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.tT
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike.K
#print axioms OnBytes.Desc.First.K4.Rt.front_rel
#print axioms OnBytes.Desc.First.K4.Rt.back_rel
#print axioms OnBytes.Desc.First.K4.Rt.SameSh
#print axioms OnBytes.Desc.First.K4.Rt.LevelAlike
#print axioms OnBytes.Desc.First.K4.Rt.OwnAlike
