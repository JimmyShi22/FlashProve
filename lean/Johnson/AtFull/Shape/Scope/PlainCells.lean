-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/PlainCells.lean: THE PLAIN CELLS OF THE TABLE AND ITS BACK ROW GO ALIKE AT
TWO PUBLIC RECORDS THAT MEET SameRead (Scope/Rel.lean). For each of the sorts front, laid, opening,
switch, draw, digits, equation, close, shut, cleared, finish, test, batching, sendW, sealing: the
law ‹sort›_rel at the place of the sort in Table.lean's rows, in the form CellRel (Scope/Join.lean).

* alike_blind, alike_drop: the two ways in which a cell's law closes at an attention link.

Limits. Laws on terms; nothing is evaluated; nothing says that a step returns. The head's link is not
here, though its plain cells read the same first halves (draw_first, digits_first, close_first,
cleared_first). Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.PlainSteps
import Johnson.AtFull.Shape.Scope.Join
import Johnson.AtFull.Shape.Scope.LettersSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K1 (linkNumbers qFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2)
open HonestTraceRun.SetUp (SamePlans links_same rounds_same)

variable {X X₀ : Verify.Public}

/-! ## How a law closes -/

theorem alike_blind {f f' : ShA → Except String ShA} (e : f = f') (hB : Blind f) {n : Nat}
    (hn : oddAt (n + 1) = oddAt n) {a a' : ShA} (h : RelAt X X₀ n a a') :
    Alike (RelAt X X₀ (n + 1)) (f a) (f' a') := by
  subst e
  unfold RelAt at h
  by_cases ho : oddAt n = true
  · rw [if_pos ho] at h
    have m := hB a a' h
    have r : ∀ b b', strip b = strip b' → RelAt X X₀ (n + 1) b b' := by
      intro b b' eb
      unfold RelAt
      rw [hn, if_pos ho]
      exact eb
    cases h1 : f a with
    | error w =>
      cases h2 : f a' with
      | error w' => exact Or.inr ⟨rfl, rfl⟩
      | ok b' =>
        rw [h1, h2] at m
        cases m
    | ok b =>
      cases h2 : f a' with
      | error w' =>
        rw [h1, h2] at m
        cases m
      | ok b' =>
        rw [h1, h2] at m
        exact Or.inl ⟨b, b', rfl, rfl, r b b' (Option.some.inj m)⟩
  · rw [if_neg ho] at h
    subst h
    cases h1 : f a with
    | error w => exact Or.inr ⟨rfl, rfl⟩
    | ok b => exact Or.inl ⟨b, b, rfl, rfl, relAt_of_eq rfl⟩

theorem alike_drop {f f' : ShA → Except String ShA} (e : f = f') (hD : Drop f) {n m : Nat}
    {a a' : ShA} (h : RelAt X X₀ n a a') : Alike (RelAt X X₀ m) (f a) (f' a') := by
  subst e
  have s : strip a = strip a' := by
    unfold RelAt at h
    split at h
    · exact h
    · rw [h]
  have d := hD.same s
  cases h1 : f a with
  | error w =>
    cases h2 : f a' with
    | error w' => exact Or.inr ⟨rfl, rfl⟩
    | ok b' =>
      rw [h1, h2] at d
      cases d
  | ok b =>
    cases h2 : f a' with
    | error w' =>
      rw [h1, h2] at d
      cases d
    | ok b' =>
      rw [h1, h2] at d
      exact Or.inl ⟨b, b', rfl, rfl, relAt_of_eq (Option.some.inj d)⟩

/-! ## The cells, at any letters -/

theorem draw_blind (L : TabLetters) (l : Nat) : Blind (TabL.draw L l).1 := by
  unfold TabL.draw
  split
  · exact (keep_liftQ (keep_draw _)).blind
  · exact (keep_no _).blind

theorem digits_blind (L : TabLetters) (l : Nat) : Blind (TabL.digits L l).1 := by
  unfold TabL.digits
  split
  · exact (keep_digits _ _ _).blind
  · exact (keep_no _).blind

theorem close_blind (L : TabLetters) (l : Nat) : Blind (TabL.close L l).1 := by
  unfold TabL.close
  split
  · exact (keep_close _).blind
  · exact (keep_no _).blind

theorem switch_blind (L : TabLetters) (l : Nat) : Blind (TabL.switch L l).1 := by
  unfold TabL.switch
  split
  · split
    · split
      · exact (keep_switch _ _ _ _ (keepP_quiet (keep_openAtt _))).blind
      · exact (keep_no _).blind
    · split
      · exact (keep_switch _ _ _ _ (keepP_quiet (keep_openLay _))).blind
      · exact (keep_no _).blind
  · exact (keep_no _).blind

theorem cleared_drop (L : TabLetters) (l : Nat) : Drop (TabL.cleared L l).1 := by
  unfold TabL.cleared
  split
  · split
    · exact drop_clearHead _ _ _
    · split
      · split
        · exact drop_clearAtt _ _
        · exact drop_no _
      · split
        · exact drop_clearLay _ _ _ _
        · exact drop_no _
  · exact drop_no _

/-! ## The first halves at the two records -/

theorem draw_first (S : SameRead X X₀) (l : Nat) :
    (TabL.draw (LW X) l).1 = (TabL.draw (LW X₀) l).1 := by
  unfold TabL.draw
  rw [k8_same S l]

theorem digits_first (S : SameRead X X₀) (l : Nat) :
    (TabL.digits (LW X) l).1 = (TabL.digits (LW X₀) l).1 := by
  unfold TabL.digits
  rw [nums_same S l]
  rfl

theorem finish_first (S : SameRead X X₀) :
    (TabL.finish (LW X)).1 = (TabL.finish (LW X₀)).1 := by
  unfold TabL.finish
  rw [k2n_same S none]
  rfl

theorem close_first (l : Nat) : (TabL.close (LW X) l).1 = (TabL.close (LW X₀) l).1 := by
  unfold TabL.close
  rw [show (LW X).close l = (LW X₀).close l from rfl]

theorem opening_first (S : SameRead X X₀) :
    (TabL.opening (LW X)).1 = (TabL.opening (LW X₀)).1 := by
  unfold TabL.opening
  rw [show (LW X).links = (LW X₀).links from links_same S,
    show (LW X).XZ.G = (LW X₀).XZ.G from S.G,
    show (LW X).XZ.layers.y.h.p4 = (LW X₀).XZ.layers.y.h.p4 from S.toSamePlans.p4]
  rfl

theorem layPar_same (S : SameRead X X₀) (Y : Stages.LinkH) (hp : Layer.HPlan2) (l : Nat) :
    layPar X Y hp l = layPar X₀ Y hp l := by
  unfold layPar
  rw [show X.layers.y.h.p4 = X₀.layers.y.h.p4 from S.toSamePlans.p4]

theorem switch_first (S : SameRead X X₀) (l : Nat) :
    (TabL.switch (LW X) l).1 = (TabL.switch (LW X₀) l).1 := by
  unfold TabL.switch
  rw [show (LW X).k2n (some l) = (LW X₀).k2n (some l) from k2n_same S _, hpL_same S l,
    show (LW X).links = (LW X₀).links from links_same S,
    show (LW X).XZ.G = (LW X₀).XZ.G from S.G,
    show (LW X).ft = (LW X₀).ft from rfl]
  split
  · rename_i n HP Y _ _ _
    split
    · generalize e1 : (LW X).XZ.A[Y.g]? = o1
      generalize e2 : (LW X₀).XZ.A[Y.g]? = o2
      have hA : o1.map stripPlan = o2.map stripPlan := by
        rw [← e1, ← e2]
        exact S.atA Y.g
      cases o1 with
      | none =>
        cases o2 with
        | none => rfl
        | some p₀ => cases hA
      | some p =>
        cases o2 with
        | none => cases hA
        | some p₀ =>
          have hs : stripPlan p = stripPlan p₀ := Option.some.inj hA
          have hP : attPar Y p l = attPar Y p₀ l := by
            unfold attPar
            rw [show p.ns = p₀.ns from congrArg (·.ns) hs,
              show p.seam.tl = p₀.seam.tl from congrArg (·.seam.tl) hs]
          simp only [hP]
    · split
      · rename_i hp _
        simp only [show layPar (LW X).XZ Y hp l = layPar (LW X₀).XZ Y hp l from layPar_same S Y hp l]
      · rfl
  · rfl

theorem cleared_first (S : SameRead X X₀) (l : Nat) :
    (TabL.cleared (LW X) l).1 = (TabL.cleared (LW X₀) l).1 := by
  unfold TabL.cleared
  rw [show (LW X).links = (LW X₀).links from links_same S,
    show (LW X).XZ.G = (LW X₀).XZ.G from S.G,
    show (LW X).XZ.layers.wsLay = (LW X₀).XZ.layers.wsLay from S.wsLay,
    show (LW X).lin = (LW X₀).lin from rfl]
  split
  · rename_i Y _
    split
    · rfl
    · split
      · generalize e1 : (LW X).XZ.A[Y.g]? = o1
        generalize e2 : (LW X₀).XZ.A[Y.g]? = o2
        have hA : o1.map stripPlan = o2.map stripPlan := by
          rw [← e1, ← e2]
          exact S.atA Y.g
        cases o1 with
        | none =>
          cases o2 with
          | none => rfl
          | some p₀ => cases hA
        | some p =>
          cases o2 with
          | none => cases hA
          | some p₀ =>
            have hs : stripPlan p = stripPlan p₀ := Option.some.inj hA
            simp only [show p.nLin = p₀.nLin from congrArg (·.nLin) hs]
      · rfl
  · rfl

/-! ## The laws at the table's places -/

theorem cell_blind {n : Nat} {c c' : Cell} (e : c.1 = c'.1) (hB : Blind c.1)
    (hn : oddAt (n + 1) = oddAt n) : CellRel X X₀ n c c' :=
  fun _ _ h => alike_blind e hB hn h

theorem cell_drop {n : Nat} {c c' : Cell} (e : c.1 = c'.1) (hD : Drop c.1) :
    CellRel X X₀ n c c' :=
  fun _ _ h => alike_drop e hD h

/-- Place 0: "laid". -/
theorem laid_rel {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 0 + 1)
    ((TabL.linkRow (LW X) l).at 0) ((TabL.linkRow (LW X₀) l).at 0) := by
  show CellRel X X₀ _ (TabL.laid l) (TabL.laid l)
  exact cell_blind rfl (keep_liftQ (keep_laid l)).blind (oddAt_inside (j := 0) hl (by omega))

/-- Place 1: the opening at link 0, else the switch. -/
theorem first_rel (S : SameRead X X₀) {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 1 + 1)
    ((TabL.linkRow (LW X) l).at 1) ((TabL.linkRow (LW X₀) l).at 1) := by
  show CellRel X X₀ _ (if l == 0 then TabL.opening (LW X) else TabL.switch (LW X) l)
    (if l == 0 then TabL.opening (LW X₀) else TabL.switch (LW X₀) l)
  split
  · rename_i h0
    obtain rfl : l = 0 := by simpa using h0
    exact cellRel_of_eq (by decide) (opening_first S)
  · exact cell_blind (switch_first S l) (switch_blind _ l) (oddAt_inside (j := 1) hl (by omega))

/-- Place 5: the draw. -/
theorem draw_rel (S : SameRead X X₀) {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 5 + 1)
    ((TabL.linkRow (LW X) l).at 5) ((TabL.linkRow (LW X₀) l).at 5) := by
  show CellRel X X₀ _ (TabL.draw (LW X) l) (TabL.draw (LW X₀) l)
  exact cell_blind (draw_first S l) (draw_blind _ l) (oddAt_inside (j := 5) hl (by omega))

/-- Place 6: the digits' commitment. -/
theorem digits_rel (S : SameRead X X₀) {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 6 + 1)
    ((TabL.linkRow (LW X) l).at 6) ((TabL.linkRow (LW X₀) l).at 6) := by
  show CellRel X X₀ _ (TabL.digits (LW X) l) (TabL.digits (LW X₀) l)
  exact cell_blind (digits_first S l) (digits_blind _ l) (oddAt_inside (j := 6) hl (by omega))

/-- Place 10: the one equation. -/
theorem equation_rel {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 10 + 1)
    ((TabL.linkRow (LW X) l).at 10) ((TabL.linkRow (LW X₀) l).at 10) := by
  show CellRel X X₀ _ TabL.equation TabL.equation
  exact cell_blind rfl keep_equation.blind (oddAt_inside (j := 10) hl (by omega))

/-- Place 11: the closing. -/
theorem close_rel {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 11 + 1)
    ((TabL.linkRow (LW X) l).at 11) ((TabL.linkRow (LW X₀) l).at 11) := by
  show CellRel X X₀ _ (TabL.close (LW X) l) (TabL.close (LW X₀) l)
  exact cell_blind (close_first l) (close_blind _ l) (oddAt_inside (j := 11) hl (by omega))

/-- Place 12: "shut". -/
theorem shut_rel {l : Nat} (hl : l < 24) : CellRel X X₀ (14 * l + 12 + 1)
    ((TabL.linkRow (LW X) l).at 12) ((TabL.linkRow (LW X₀) l).at 12) := by
  show CellRel X X₀ _ TabL.shut TabL.shut
  exact cell_blind rfl (keep_liftQ keep_shut).blind (oddAt_inside (j := 12) hl (by omega))

/-- Place 13: "cleared": what it returns holds no lookup's record, so the relation behind it may be
plain equality. -/
theorem cleared_rel (S : SameRead X X₀) (l : Nat) : CellRel X X₀ (14 * l + 13 + 1)
    ((TabL.linkRow (LW X) l).at 13) ((TabL.linkRow (LW X₀) l).at 13) := by
  show CellRel X X₀ _ (TabL.cleared (LW X) l) (TabL.cleared (LW X₀) l)
  exact cell_drop (cleared_first S l) (cleared_drop _ l)

/-- The front. -/
theorem front_rel : CellRel X X₀ 0 (liftQ .ok, noVals) (liftQ .ok, noVals) :=
  cellRel_of_eq oddAt_zero rfl

/-- **The five members behind the links**: equal first halves. -/
theorem back_rel (S : SameRead X X₀) (j : Nat) (hj : j < 5) :
    CellRel X X₀ (353 + j) ((TabL.backRow (LW X)).at j) ((TabL.backRow (LW X₀)).at j) := by
  have ho : oddAt (353 + j) = false := oddAt_behind (by omega)
  match j, hj with
  | 0, _ => exact cellRel_of_eq ho (finish_first S)
  | 1, _ => exact cellRel_of_eq ho rfl
  | 2, _ => exact cellRel_of_eq ho rfl
  | 3, _ => exact cellRel_of_eq ho rfl
  | 4, _ => exact cellRel_of_eq ho rfl

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.laid_rel
#print axioms Johnson.AtFull.Shape.Scope.first_rel
#print axioms Johnson.AtFull.Shape.Scope.draw_rel
#print axioms Johnson.AtFull.Shape.Scope.digits_rel
#print axioms Johnson.AtFull.Shape.Scope.equation_rel
#print axioms Johnson.AtFull.Shape.Scope.close_rel
#print axioms Johnson.AtFull.Shape.Scope.shut_rel
#print axioms Johnson.AtFull.Shape.Scope.cleared_rel
#print axioms Johnson.AtFull.Shape.Scope.front_rel
#print axioms Johnson.AtFull.Shape.Scope.back_rel
