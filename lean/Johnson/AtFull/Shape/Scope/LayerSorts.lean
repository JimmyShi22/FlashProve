-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/LayerSorts.lean: AT A LAYERS' LINK (l EVEN, l < 24) THE FIRST HALVES OF THE
TABLE's CELLS ARE ONE FUNCTION AT TWO PUBLIC RECORDS THAT ARE ALIKE IN THE SENSE OF SameRead
(Rel.lean). So there the relation of Rel.lean stays equality: no law on strip is needed.

  layers_pT         the layers' record of X is X₀'s with three eps and the scales set.
  testsWhere_eq, lookAt_eq, lookOf_eq   what the cells read at both records (the other letters:
                    LettersSame.lean).
  **lookCalls_eq**, **lookDigits_eq**, **k4_eq**, **reads_eq**, **batch_eq**, **behind_eq**.

Limits. Equations of functions: no step is shown to return at any shape. hN: the link is not the
head's. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.Rel
import Johnson.AtFull.Shape.Scope.FormsTwo
import Johnson.AtFull.Shape.Scope.LettersSame
import Johnson.AtFull.Shape.LettersAtX

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Rt (ownOf frontG backG)
open OnBytes.Desc.First.K4.Rt.Two (pT turnY)
open VerifiableInference.Desc.K9 (testsWhere)
open VerifiableInference.Desc.First.Look (placeAt lookAt)

variable {X X₀ : Verify.Public}

/-- The layers' record of X is X₀'s with three eps and the scales set. -/
theorem layers_pT (S : SameRead X X₀) :
    X.layers = pT X₀.layers X.layers.y.h.eps1 X.layers.y.h.eps2 X.layers.y.h.epsF X.layers.sc := by
  have h1 := S.layersRest
  have h2 : turnY X₀.layers.y X.layers.y.h.eps1 X.layers.y.h.eps2 X.layers.y.h.epsF = X.layers.y :=
    S.layRest.symm
  show X.layers = { X₀.layers with
    y := turnY X₀.layers.y X.layers.y.h.eps1 X.layers.y.h.eps2 X.layers.y.h.epsF, sc := X.layers.sc }
  rw [h2]
  exact h1

/-! ## 1 What the cells read -/

theorem testsWhere_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0) (i : Nat) :
    testsWhere X l i = testsWhere X₀ l i := by
  have SP := S.toSamePlans
  unfold testsWhere
  dsimp only
  rw [SP.p4, SP.NGr, S.H, S.G]
  generalize hst : (if X₀.p4 = true then 2 else 1) = st
  have hm : (l % st == 0) = true := by
    subst hst
    split <;> simp [he, Nat.mod_one]
  by_cases hh : (l == st * X₀.NGr) = true
  · rw [if_pos hh, if_pos hh]
  · rw [if_neg hh, if_neg hh, if_pos hm, if_pos hm]

theorem y_eq (S : SameRead X X₀) {β : Type} (f : Layer.Lay → β)
    (hf : ∀ e1 e2 eF y, f (turnY y e1 e2 eF) = f y) : f X.layers.y = f X₀.layers.y := by
  have h2 : X.layers.y = turnY X₀.layers.y X.layers.y.h.eps1 X.layers.y.h.eps2 X.layers.y.h.epsF :=
    S.layRest
  rw [h2]
  exact hf _ _ _ _

theorem lookAt_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0)
    (hN : l ≠ (if X₀.p4 = true then 2 else 1) * X₀.NGr) (d : Bool) :
    lookAt X l d = lookAt X₀ l d := by
  have SP := S.toSamePlans
  have e1 : X.y.cl = X₀.y.cl := y_eq S (·.cl) fun _ _ _ _ => rfl
  have e2 : X.y.fo = X₀.y.fo := y_eq S (·.fo) fun _ _ _ _ => rfl
  have e3 : X.y.h.lidb = X₀.y.h.lidb := y_eq S (·.h.lidb) fun _ _ _ _ => rfl
  have e4 : X.y.h.lmb = X₀.y.h.lmb := y_eq S (·.h.lmb) fun _ _ _ _ => rfl
  unfold lookAt
  dsimp only
  rw [SP.p4, SP.NGr]
  generalize hst : (if X₀.p4 = true then 2 else 1) = st at hN ⊢
  have hm : (l % st == 0) = true := by
    subst hst
    split <;> simp [he, Nat.mod_one]
  have hh : ¬ (l == st * X₀.NGr) = true := by simpa using hN
  rw [if_neg hh, if_neg hh, if_pos hm, if_pos hm, S.G, e1, e2, e3, e4]

theorem lookOf_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0)
    (hN : l ≠ (if X₀.p4 = true then 2 else 1) * X₀.NGr) (d : Bool) :
    lookOf X l d = lookOf X₀ l d := by
  have e2 : X.y.fo = X₀.y.fo := y_eq S (·.fo) fun _ _ _ _ => rfl
  have hp : ∀ d, placeAt X l d = placeAt X₀ l d := by
    intro d
    unfold placeAt
    rw [lookAt_eq S he hN, S.frame]
  unfold lookOf
  rw [hp, hp, e2]

/-! ## 2 The cells -/

theorem lookCalls_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0)
    (hN : l ≠ (if X₀.p4 = true then 2 else 1) * X₀.NGr) :
    (TabL.lookCalls (LW X) l).1 = (TabL.lookCalls (LW X₀) l).1 := by
  have e : (LW X).look l false = (LW X₀).look l false := lookOf_eq S he hN false
  unfold TabL.lookCalls
  rw [e]

theorem lookDigits_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0)
    (hN : l ≠ (if X₀.p4 = true then 2 else 1) * X₀.NGr) :
    (TabL.lookDigits (LW X) l).1 = (TabL.lookDigits (LW X₀) l).1 := by
  have e : (LW X).look l true = (LW X₀).look l true := lookOf_eq S he hN true
  have e2 : lookUC (LW X).XZ l = lookUC (LW X₀).XZ l := by
    show lookUC X l = lookUC X₀ l
    unfold lookUC
    have hb : (l % 2 == 0) = true := by simp [he]
    rw [if_pos hb, if_pos hb, S.G]
  unfold TabL.lookDigits
  rw [e, e2]

theorem k4_some {X : Verify.Public} {hp : Layer.HPlan2} {g : Nat} (h : X.G[g]? = some hp) :
    (TabL.k4 (LW X) g).1 = liftO (k4StepW (k4Par X hp g)) := by
  have e0 : (LW X).XG.G[g]? = some hp := h
  have e1 : (LW X).k4pub g = k4PubB (k4Par X hp g) := by
    show k4pubX X g = _
    unfold k4pubX
    rw [h]
    rfl
  have e2 : (LW X).k4own g = ownOf (k4Par X hp g) := by
    show k4ownX X g = _
    unfold k4ownX
    rw [h]
  unfold TabL.k4
  rw [e0]
  show liftO (k4StepL ((LW X).k4pub g) ((LW X).k4own g) (k4Par X hp g)) = _
  rw [e1, e2, ← k4StepW_eq]

theorem k4Par_pT (S : SameRead X X₀) (hp : Layer.HPlan2) (g : Nat) :
    k4Par X hp g = { k4Par X₀ hp g with
      P := pT X₀.layers X.layers.y.h.eps1 X.layers.y.h.eps2 X.layers.y.h.epsF X.layers.sc } := by
  unfold k4Par
  rw [← layers_pT S]

theorem k4_eq (S : SameRead X X₀) (g : Nat) :
    (TabL.k4 (LW X) g).1 = (TabL.k4 (LW X₀) g).1 := by
  cases hG : X₀.G[g]? with
  | none =>
    have h1 : (LW X).XG.G[g]? = none := by
      show X.G[g]? = none
      rw [S.G]
      exact hG
    have h2 : (LW X₀).XG.G[g]? = none := hG
    unfold TabL.k4
    rw [h1, h2]
  | some hp =>
    have hX : X.G[g]? = some hp := by
      rw [S.G]
      exact hG
    rw [k4_some hX, k4_some hG, k4Par_pT S]
    exact congrArg liftO (OnBytes.Desc.First.K4.Rt.Two.k4StepW_turn _ _ _ _ (k4Par X₀ hp g))

theorem reads_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0) :
    (TabL.reads (LW X) l).1 = (TabL.reads (LW X₀) l).1 := by
  have hb : (l % 2 == 0) = true := by simp [he]
  have eG : (LW X).XG.G[l / 2]? = (LW X₀).XG.G[l / 2]? := by
    show X.G[l / 2]? = X₀.G[l / 2]?
    rw [S.G]
  unfold TabL.reads
  rw [nums_same S l]
  cases (LW X₀).nums l with
  | none => rfl
  | some q =>
    obtain ⟨a, b, rd, d⟩ := q
    simp only [if_pos hb]
    rw [eG]
    cases (LW X₀).XG.G[l / 2]? with
    | none => rfl
    | some hp => rfl

theorem lookup_g {rows rows' : List ((Nat × String) × Row)}
    (h : rows.map (fun r => (r.1, r.2.g)) = rows'.map (fun r => (r.1, r.2.g))) (o : Nat × String) :
    (tabOf rows o).g = (tabOf rows' o).g := by
  unfold tabOf
  induction rows generalizing rows' with
  | nil =>
    cases rows' with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases rows' with
    | nil => cases h
    | cons x' xs' =>
      obtain ⟨k, r⟩ := x
      obtain ⟨k', r'⟩ := x'
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, h2⟩, h3⟩ := h
      simp only [List.lookup]
      split
      · exact h2
      · exact ih h3

theorem rowsLay_g (S : SameRead X X₀) (g : Nat) :
    (rowsLay X g).map (fun r => (r.1, r.2.g)) = (rowsLay X₀ g).map (fun r => (r.1, r.2.g)) := by
  have hf : frontG X.layers g = frontG X₀.layers g := by
    rw [layers_pT S]
    exact OnBytes.Desc.First.K4.Rt.Two.frontG_turn _ _ _ _ _ _
  have hb : backG X.layers.y X.layers.sc = backG X₀.layers.y X₀.layers.sc := by
    have h2 : X.layers.y = turnY X₀.layers.y X.layers.y.h.eps1 X.layers.y.h.eps2
        X.layers.y.h.epsF := S.layRest
    rw [h2]
    exact OnBytes.Desc.First.K4.Rt.Two.backG_turn _ _ _ _ _ _
  simp only [rowsLay, List.map_cons, List.map_nil, hf, hb]

theorem batch_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0) (h24 : l ≠ 24) :
    (TabL.batch (LW X) l).1 = (TabL.batch (LW X₀) l).1 := by
  have hb : (l % 2 == 0) = true := by simp [he]
  have h2 : (l == 24) = false := by simpa using h24
  have ew : testsWhere (LW X).XZ l 0 = testsWhere (LW X₀).XZ l 0 := testsWhere_eq S he 0
  have ek : (LW X).k9 l = (LW X₀).k9 l := rfl
  unfold TabL.batch
  rw [ew, ek]
  cases (LW X₀).k9 l with
  | none => rfl
  | some p =>
    cases testsWhere (LW X₀).XZ l 0 with
    | none => rfl
    | some w =>
      simp only [h2, Bool.false_eq_true, if_false, if_pos hb]
      show cellG p w.1 (rowsLay X (l / 2)) _ = cellG p w.1 (rowsLay X₀ (l / 2)) _
      unfold cellG
      rw [show (fun o => (tabOf (rowsLay X (l / 2)) o).g) =
        (fun o => (tabOf (rowsLay X₀ (l / 2)) o).g) from
        funext fun o => lookup_g (rowsLay_g S _) o]

theorem behind_eq (S : SameRead X X₀) {l : Nat} (he : l % 2 = 0) :
    (TabL.behind (LW X) l).1 = (TabL.behind (LW X₀) l).1 := by
  have ew : testsWhere (LW X).XZ l 0 = testsWhere (LW X₀).XZ l 0 := testsWhere_eq S he 0
  have eG : (LW X).XG.G[l / 2]? = (LW X₀).XG.G[l / 2]? := by
    show X.G[l / 2]? = X₀.G[l / 2]?
    rw [S.G]
  unfold TabL.behind
  rw [k8_same S l, ew, eG]

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.layers_pT
#print axioms Johnson.AtFull.Shape.Scope.lookCalls_eq
#print axioms Johnson.AtFull.Shape.Scope.lookDigits_eq
#print axioms Johnson.AtFull.Shape.Scope.k4_eq
#print axioms Johnson.AtFull.Shape.Scope.reads_eq
#print axioms Johnson.AtFull.Shape.Scope.batch_eq
#print axioms Johnson.AtFull.Shape.Scope.behind_eq
