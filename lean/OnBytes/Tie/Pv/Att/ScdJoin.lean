-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/ScdJoin.lean: the block of Cb/Pv/Att/Scd.lean has, round by round, the numbers of
scalars and of drawn elements that the port's planner writes for attentionScd, and its errors are
the numerators of the bounds that the planner hands to close.

Main names:
  `scd_fits`: the record attentionScd lt lgk pairs Lam has the numbers of the block's parameters
    (PlainSc.Fits, OnBytes/Tie/Pv/Att/PlanJoin.lean), from the four equations of
    OnBytes/Tie/Pv/Att/ScdTie.lean.
  `scd_planPsc`: for every setting and every state of the planner in a request's scope with 24 n
    bytes and no root or answer open (At, OnBytes/Tie/Pv/Att/PlanCalc.lean): if planPsc at that
    record ends well, the rounds that it has added have entries of which the block's shape is an
    instance (ShapeIs).
  `scd_errs`: the block's errors, as a list of numbers, are the numerators of the plan's bounds.

Limits: as in OnBytes/Tie/Pv/Att/Shape.lean and PlanJoin.lean: ShapeIs counts; nothing says that the
setting's cardE is the number of elements of E. "The plan's bounds" are the bounds that planPsc
hands to close (bPsc, OnBytes/Tie/Pv/Att/PlanOwnW.lean); close counts them once for each instance
and rounds; nothing here says that the factor is 1.
-/
import OnBytes.Tie.Pv.Att.PlanJoin
import OnBytes.Tie.Pv.Att.ScdTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb Cb.Pv.Att TWhole OnBytes OnBytes.G4 OnBytes.Params
open OnBytes.Tie.Pv.Att.Plan

variable {E : Type} [Field E] [Fintype E] {s : ScdSize} (T : Scd E s)

theorem scd_fits : T.plain.Fits (attentionScd s.lt s.lgk s.pairs s.Lam) :=
  ⟨scd_withY_plan s, scd_degs_plan s, scd_degY_plan s, scd_values_plan s⟩

theorem scd_planPsc (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec)
    (t : Setting) (p q : PlanState) (hp : At t (24 * n) p)
    (h : planPsc (attentionScd s.lt s.lgk s.pairs s.Lam) p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (scdR T n cl Ex).shape (l.map (·.entry)) :=
  plain_planPsc T.plain _ (scd_fits T) n T.plain.fix cl Ex t p q hp h

theorem scd_errs (n c : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) :
    errList (scdE T n cl Ex) = numsOf (qPsc c (attentionScd s.lt s.lgk s.pairs s.Lam)) :=
  plain_errs T.plain _ (scd_fits T) n c Ex

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.scd_fits
#print axioms OnBytes.Tie.Pv.Att.scd_planPsc
#print axioms OnBytes.Tie.Pv.Att.scd_errs
