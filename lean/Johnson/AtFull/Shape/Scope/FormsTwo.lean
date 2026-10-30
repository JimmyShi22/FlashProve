-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FormsTwo.lean: THE LAYERS' TWO LISTINGS ON SHAPES, "front" AND "back", ARE
ONE FUNCTION AT TWO PUBLIC RECORDS THAT DIFFER IN THE TABLE OF SCALES AND THE LAYOUT's THREE eps.

  lines_rel, rowsForms_turn   groups 4 to 6: eps and 2^(M + 1) are constants of the forms.
  front_turn   the listing at the two blank records.
  **frontG_turn**, **backG_turn**.

Limits. Equations of functions: nothing is evaluated, no run is shown to return.
-/
import Johnson.AtFull.Shape.Scope.K4Turn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt.Two
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.RtPub (optRel_pure optRel_ite)
open VerifiableInference.Desc.First.Shape

set_option maxHeartbeats 1000000

local macro "samesh" : tactic => `(tactic| repeat' first
  | with_reducible assumption
  | with_reducible exact SameSh.refl _
  | with_reducible exact SameSh.const _ _
  | with_reducible refine SameSh.add ?_ ?_
  | with_reducible refine SameSh.sub ?_ ?_)

theorem lines_rel (r : P6.Row) (P : Nat → P6.Form) (eps eps' : E) {two two' : P6.Form}
    (h : SameSh two two') : All2 SameSh (P6.lines r P eps two) (P6.lines r P eps' two') := by
  unfold P6.lines P6.root P6.reciprocal
  refine .cons (SameSh.refl _) (.cons ?_ (.cons (SameSh.refl _) (.cons (SameSh.refl _)
    (.cons (SameSh.refl _) (.cons (SameSh.refl _) (.cons ?_ (.cons (SameSh.refl _) .nil)))))))
  · samesh
  · samesh

theorem flatten_rel {α : Type} {f f' : α → List Aff} (hf : ∀ x, All2 SameSh (f x) (f' x)) :
    ∀ l : List α, All2 SameSh (l.map f).flatten (l.map f').flatten
  | [] => .nil
  | x :: l => by
    simp only [List.map_cons, List.flatten_cons]
    exact (hf x).append (flatten_rel hf l)

theorem rowsForms_turn (v : Env) (e1 e2 eF : Nat) (s : Scales) (H : Heard) :
    OptRel (All2 SameSh) (rowsForms { v with y := turnY v.y e1 e2 eF, sc := s } H)
      (rowsForms v H) := by
  unfold rowsForms
  refine optRel_bind_same fun ends => optRel_bind_same fun Ds => optRel_pure ?_
  exact ((all2_refl _).append (all2_refl _)).append
    (flatten_rel (fun x => lines_rel _ _ _ _ (SameSh.const _ _)) _)

theorem front_turn (P : Pub) (e1 e2 eF : Nat) (s : Scales) (g : Nat) (ow : OwnSh) (rV rL : Aff) :
    OptRel (All2 SameSh)
      (front false (pT P e1 e2 eF s) g (ow.blank (turnY P.y e1 e2 eF) s []) rV rL)
      (front false P g (ow.blank P.y P.sc []) rV rL) := by
  unfold front
  refine optRel_bind_same fun g2 => ?_
  refine optRel_bind (S := All2 SameSh)
    (rowsForms_turn (ow.blank P.y P.sc []).v e1 e2 eF s _) fun g46 g46' h46 => ?_
  refine optRel_bind_same fun g7 => optRel_bind_same fun g89 => optRel_bind_same fun g10 =>
    optRel_bind_same fun g11 => ?_
  have key : ∀ g12 g12' : List Aff, All2 SameSh g12 g12' →
      All2 SameSh ((if false = true then (ow.blank (turnY P.y e1 e2 eF) s []).H.fo.rows.toList
          else []) ++ g2 ++
          [rowBatchForm (pT P e1 e2 eF s).y (ow.blank (turnY P.y e1 e2 eF) s []).H, rV] ++
          g46 ++ g7 ++ g89 ++ g10 ++ rL :: g11.2 ++ g12)
        ((if false = true then (ow.blank P.y P.sc []).H.fo.rows.toList else []) ++ g2 ++
          [rowBatchForm P.y (ow.blank P.y P.sc []).H, rV] ++
          g46' ++ g7 ++ g89 ++ g10 ++ rL :: g11.2 ++ g12') := by
    intro g12 g12' h12
    simp only [Bool.false_eq_true, if_false, List.nil_append]
    exact ((((((all2_refl g2).append (all2_refl _)).append h46).append (all2_refl g7)).append
      (all2_refl g89)).append (all2_refl g10)).append (all2_refl _) |>.append h12
  dsimp only
  refine optRel_ite ?_ ?_
  · refine optRel_bind (S := All2 SameSh) ?_ fun g12 g12' h12 => optRel_pure (key _ _ h12)
    exact OptRel.refl (fun l => all2_refl l) _
  · exact optRel_pure (key [] [] .nil)

theorem map_of_rel {β : Type} {x y : Option (List Aff)} (h : OptRel (All2 SameSh) x y)
    (F : List AffSh → β) :
    x.map (fun fs => F (fs.map affSh)) = y.map (fun fs => F (fs.map affSh)) := by
  cases x <;> cases y
  · rfl
  · exact h.elim
  · exact h.elim
  · exact congrArg (fun z => some (F z)) (shapes_eq h)

theorem bind_of {α β : Type} {x : Option α} {f f' : α → Option β} (h : ∀ a, f a = f' a) :
    x.bind f = x.bind f' := by
  cases x
  · rfl
  · exact h _

/-- **"front" ON SHAPES IS ONE FUNCTION AT THE TWO RECORDS.** -/
theorem frontG_turn (P : Pub) (e1 e2 eF : Nat) (s : Scales) (g : Nat) :
    frontG (pT P e1 e2 eF s) g = frontG P g := by
  funext ow L
  unfold frontG
  have e : 4 * (pT P e1 e2 eF s).y.NI = 4 * P.y.NI := rfl
  rw [e]
  by_cases hc : ((List.range (4 * P.y.NI)).all (fun i => shownB L (ow.H.tV.sEnd + i)) &&
      openB ow.H.tV.p L && openB ow.H.fo.leaves (filledBy ow.H.tV.p L)) = true
  · rw [if_pos hc, if_pos hc]
    have hp : planesParts (ow.blank (pT P e1 e2 eF s).y (pT P e1 e2 eF s).sc []).v
        (ow.blank (pT P e1 e2 eF s).y (pT P e1 e2 eF s).sc []).H.fo =
        planesParts (ow.blank P.y P.sc []).v (ow.blank P.y P.sc []).H.fo := rfl
    rw [hp]
    refine bind_of fun pp => ?_
    have r := front_turn P e1 e2 eF s g ow (rowOfSh ow.H.tV.p (AffSh.mk [] [])).blank
      (rowOfSh ow.H.fo.leaves (affSh pp.1)).blank
    exact map_of_rel r fun z =>
      (z, (filledBy ow.H.fo.leaves (filledBy ow.H.tV.p L)).setOwed
        (paidB (filledBy ow.H.fo.leaves (filledBy ow.H.tV.p L)).owed ow.H.fo.owedPlanes))
  · rw [if_neg hc, if_neg hc]

/-- **"back" ON SHAPES READS NEITHER.** -/
theorem backG_turn (y : Lay) (sc s : Scales) (e1 e2 eF : Nat) :
    backG (turnY y e1 e2 eF) s = backG y sc := rfl

end OnBytes.Desc.First.K4.Rt.Two

#print axioms OnBytes.Desc.First.K4.Rt.Two.lines_rel
#print axioms OnBytes.Desc.First.K4.Rt.Two.rowsForms_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.front_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.frontG_turn
#print axioms OnBytes.Desc.First.K4.Rt.Two.backG_turn
