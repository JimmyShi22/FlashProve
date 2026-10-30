-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/Tie.lean: the library's reduction in which the verifier draws the matrix of a
smallness test has the list of rounds that the planner lays for that draw, and the error "one part
in 2 ^ tau of all values" is the planner's bound for it.

The planner (OnBytes/Params/) plans the draw of the matrix by planSmall x 0, where x holds the
number of columns of all matrices together and the number tau of combinations.
OnBytes/Tie/Pv/Tail/Plan.lean says what that routine adds, for every x and every setting. Here the
library's one-round reduction that draws a value (IOR.draw, Ior/Draw.lean) is laid beside it. D is
the set drawn from: any finite set that is, up to a bijection, a coefficient (two bits) for each of
the x.columns * x.tau entries of the matrix. Definitions, statements and proofs.

Main names:
  `draw_shape`, `draw_err`: the list of rounds of IOR.draw D is the one round IOR.drawRound D, and
    the list of errors of its numbers IOR.Nums.draw, at the error below, is drawErr D x.
  `round_at`: from an idle state, if planSmall x 0 ends well: the state is idle again; one round
    is added; the round that draws from D is the round of its entry (RngIs,
    OnBytes/Tie/Pv/Tail/Rng.lean); with one instance the error below, divided by the number of
    values, is at most its bound, and with a column or more it is its bound.
  `rounds_are`: the list of rounds, of whatever plan the planner's finish makes of planSmall x 0.
  `drawErr D x`: the error "of all values, one part in 2 ^ tau".
  `planVal b`: the rational number that a bound of the planner stands for.
  `errors_are`: with one instance and a column or more: that error, divided by the number of
    values, is the bound of the round in that plan: one equation of two lists. `errors_le`:
    without the premise on the columns it is at most that.
  `card_drawn`, `err_list`, `chal_list`, `rngCount_val`, `rngCount_val_le`: the numbers.

Limits: nothing here says that a reduction is sound at this error: IOR.Nums.draw takes any number
as its error, and draw_err only says which number is meant. Nothing is said on the other
rounds of a smallness test. The shape is the one before proof of work is added.
-/
import OnBytes.Tie.Pv.Tail.Plan
import OnBytes.Tie.Pv.Tail.Rng
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes.Params

/-- A round that sends nothing, has no oracle position and draws a coefficient for each of
x.columns * x.tau entries is the round that the planner lays for the matrix. -/
theorem rngIs_plan (s : Setting) (x : SmallSize) (r : Round) (hP : Nonempty (r.Plain ≃ Unit))
    (hC : Nonempty (r.Chal ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (hO : IsEmpty r.Pos) :
    RngIs r (rngRound s x).entry :=
  ⟨hP, hC, hO, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rational number that a bound of the planner stands for. -/
def planVal (b : Binary) : ℚ := (b.m : ℚ) * (2 : ℚ) ^ b.e

/-- With one instance: rngCount out of all challenges is at most the planner's bound. -/
theorem rngCount_val_le (s : Setting) (x : SmallSize) (hi : s.instances ≤ 1) :
    (rngCount x.columns x.tau : ℚ) / (4 ^ (x.columns * x.tau) : ℕ) ≤
      planVal (rngRound s x).error := by
  rw [rngRound_error s x hi, planVal]
  have h4 : (0 : ℚ) < ((4 ^ (x.columns * x.tau) : ℕ) : ℚ) := by positivity
  have h2 : (0 : ℚ) < (2 : ℚ) ^ x.tau := by positivity
  have hle : (rngCount x.columns x.tau : ℚ) * (2 : ℚ) ^ x.tau ≤
      ((4 ^ (x.columns * x.tau) : ℕ) : ℚ) := by
    exact_mod_cast rngCount_le x.columns x.tau
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_mul, div_le_iff₀ h4, inv_mul_eq_div,
    le_div_iff₀ h2]
  exact hle

/-- With one instance and a column or more: it is exactly the planner's bound. -/
theorem rngCount_val (s : Setting) (x : SmallSize) (hi : s.instances ≤ 1) (hc : 1 ≤ x.columns) :
    (rngCount x.columns x.tau : ℚ) / (4 ^ (x.columns * x.tau) : ℕ) =
      planVal (rngRound s x).error := by
  rw [rngRound_error s x hi, planVal]
  have h4 : ((4 ^ (x.columns * x.tau) : ℕ) : ℚ) ≠ 0 := by positivity
  have h2 : (2 : ℚ) ^ x.tau ≠ 0 := by positivity
  have he : (rngCount x.columns x.tau : ℚ) * (2 : ℚ) ^ x.tau =
      ((4 ^ (x.columns * x.tau) : ℕ) : ℚ) := by
    exact_mod_cast rngCount_mul x.columns x.tau hc
  rw [zpow_neg, zpow_natCast, Nat.cast_one, one_mul, div_eq_iff h4, inv_mul_eq_div,
    eq_div_iff h2]
  exact he

variable (D : Type) [Fintype D] [Nonempty D] (x : SmallSize)

/-- The list of rounds of the reduction that draws from D. -/
theorem draw_shape {X X' : Type} (nx : X → D → X') (E : ExtSpec) :
    (IOR.draw D nx E).shape = [IOR.drawRound D] := rfl

/-- The round that draws from D is the round that the planner lays. -/
theorem round_is (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting) :
    RngIs (IOR.drawRound D) (rngRound st x).entry :=
  rngIs_plan st x _ ⟨Equiv.refl _⟩ hD (inferInstanceAs (IsEmpty Empty))

/-- The list of rounds, of the planner's finish. -/
theorem rounds_are (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting)
    (P : Planned) (h : finish st .request (planSmall x 0) = .ok P) :
    List.Forall₂ RngIs [IOR.drawRound D] (P.rounds.map (·.entry)) := by
  obtain ⟨_, hr, _⟩ := small_finish st _ P h
  rw [hr]
  exact List.Forall₂.cons (round_is D x hD st) List.Forall₂.nil

omit [Nonempty D] in
/-- The number of values drawn from. -/
theorem card_drawn (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) :
    Fintype.card D = 4 ^ (x.columns * x.tau) := by
  obtain ⟨f⟩ := hD
  rw [Fintype.card_congr f, ← Nat.card_eq_fintype_card, card_coefs]

/-- The error: of all values, one part in 2 ^ tau. -/
def drawErr : Err [IOR.drawRound D] := ((Fintype.card D / 2 ^ x.tau, ()) : ℕ × Unit)

/-- It is the list of errors of the numbers of the reduction that draws from D, at that error. -/
theorem draw_err (K : Type) {X X' : Type} (nx : X → D → X') (E : ExtSpec) :
    (IOR.Nums.draw K D nx E (Fintype.card D / 2 ^ x.tau)).err = drawErr D x := rfl

/-- The errors as a plain list. -/
theorem err_list (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) :
    (drawErr D x).toList = [rngCount x.columns x.tau] := by
  show [Fintype.card D / 2 ^ x.tau] = _
  rw [card_drawn D x hD, rngCount]

/-- The numbers of values of the challenges as a plain list. -/
theorem chal_list (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) :
    Shape.chalList [IOR.drawRound D] = [4 ^ (x.columns * x.tau)] := by
  show [Fintype.card D] = _
  rw [card_drawn D x hD]

/-- From an idle state of a plan in writing: the round and its error. -/
theorem round_at (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting)
    (p q : PlanState) (hp : Idle st p) (h : planSmall x 0 p = .ok ((), q)) :
    Idle st q ∧ q.rounds = p.rounds.push (rngRound st x) ∧
      RngIs (IOR.drawRound D) (rngRound st x).entry ∧
      (st.instances ≤ 1 →
        ((Fintype.card D / 2 ^ x.tau : ℕ) : ℚ) / (Fintype.card D : ℚ) ≤
          planVal (rngRound st x).error) ∧
      (st.instances ≤ 1 → 1 ≤ x.columns →
        ((Fintype.card D / 2 ^ x.tau : ℕ) : ℚ) / (Fintype.card D : ℚ) =
          planVal (rngRound st x).error) := by
  obtain ⟨a, r⟩ := small_adds st x p q hp h
  refine ⟨a, r, round_is D x hD st, fun hi => ?_, fun hi hc => ?_⟩
  · rw [card_drawn D x hD]
    exact rngCount_val_le st x hi
  · rw [card_drawn D x hD]
    exact rngCount_val st x hi hc

/-- The list of errors, of the planner's finish. -/
theorem errors_are (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting)
    (P : Planned) (h : finish st .request (planSmall x 0) = .ok P) (hi : st.instances ≤ 1)
    (hc : 1 ≤ x.columns) :
    List.zipWith (fun e c : ℕ => (e : ℚ) / (c : ℚ)) (drawErr D x).toList
        (Shape.chalList [IOR.drawRound D]) =
      P.rounds.map fun r => planVal r.error := by
  obtain ⟨_, hr, _⟩ := small_finish st _ P h
  rw [hr, err_list D x hD, chal_list D x hD]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.map_cons, List.map_nil]
  rw [← rngCount_val st x hi hc]

/-- Without the premise on the columns: each error is at most the plan's bound. -/
theorem errors_le (hD : Nonempty (D ≃ (Fin (x.columns * x.tau) → Prob.Coef))) (st : Setting)
    (P : Planned) (h : finish st .request (planSmall x 0) = .ok P) (hi : st.instances ≤ 1) :
    List.Forall₂ (· ≤ ·)
      (List.zipWith (fun e c : ℕ => (e : ℚ) / (c : ℚ)) (drawErr D x).toList
        (Shape.chalList [IOR.drawRound D]))
      (P.rounds.map fun r => planVal r.error) := by
  obtain ⟨_, hr, _⟩ := small_finish st _ P h
  rw [hr, err_list D x hD, chal_list D x hD]
  simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (rngCount_val_le st x hi) List.Forall₂.nil

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.round_at
#print axioms OnBytes.Tie.Pv.Tail.rounds_are
#print axioms OnBytes.Tie.Pv.Tail.errors_are
#print axioms OnBytes.Tie.Pv.Tail.errors_le
#print axioms OnBytes.Tie.Pv.Tail.draw_err
