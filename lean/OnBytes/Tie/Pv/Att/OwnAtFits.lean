-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/OwnAtFits.lean: the chain of an attention sub-proof's own rounds at the value of
Cb/Pv/Att/OwnSteps.lean has, round by round, the numbers of scalars and of drawn elements of the
rounds that the port's planAttentionOwn adds, and its errors are the numerators of that plan's
bounds (at the draw of the point: the count with the same ratio).

OnBytes/Tie/Pv/Att/OwnShape.lean proves this of all letters that have the numbers of a record of the
planner (OwnFits). Here the condition is proved at the value, for the record made of the value's own
sizes.

Main names:
  `recOf P rows`: the record: lt, lgk, pairs and Lam are D.lT, D.lg, D.nb and D.nl; the numbers of
    variables are those of the description's steps; planeMessages is P.npl.
  `ownAt_fits`: OwnFits (P.own Mn) (recOf P rows), where P.kap = 4.
  `ownAt_planned`: so the shape of the chain's reduction is an instance of the entries of the rounds
    that planAttentionOwn (recOf P rows) adds, wherever it ends well from a state p of the planner
    with At s 0 p.
  `ownAt_nums`: the chain's errors are the numerators of the plan's bounds, but at the draw of the
    point, where the chain counts v * |E| ^ (v - 1) bad points, for v = g1 + g2 coordinates
    (zero_ratio, OnBytes/Tie/Pv/Att/OwnShape.lean, says that this is the ratio v over |E|).

Limits: those of OnBytes/Tie/Pv/Att/OwnShape.lean. The premise P.kap = 4 is needed: the plan's point
has 2 lgk + 2 lt + 4 coordinates. That recOf P rows is the record that the verifier on bytes makes
from its parameter files is not said here: that record has one score unit for each unit of its list
of calls, each with its own number of pieces, where recOf has two units of D.nb pairs; and no
statement compares the description's numbers of variables with the verifier's. Nothing is said on
hiding.
-/
import OnBytes.Tie.Pv.Att.OwnShape
import Cb.Pv.Att.OwnSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb Cb.Pv.Att TWhole Inst.Model OnBytes OnBytes.G4 OnBytes.Params
open OnBytes.Tie.Pv.Att.Plan

variable {E M X : Type} [Field E] [Fintype E] (P : OwnPar E M X)

/-- The planner's record of the sizes at the value. rows is read by no round of these. -/
def recOf (rows : ℕ) : AttentionRounds where
  lt := P.D.lT
  lgk := P.D.lg
  pairs := P.D.nb
  Lam := P.D.nl
  planeMessages := P.npl
  score := [(AttSeg.Step.s6b.g P.D, P.D.nb), (AttSeg.Step.s6d.g P.D, P.D.nb)]
  e := AttSeg.Step.s8.g P.D
  valueM := AttSeg.Step.s11.g P.D
  valueD := AttSeg.Step.s12.g P.D
  attained := AttSeg.Step.s16.g P.D
  bits := P.D.lT + P.D.lg + P.kap
  rows := rows

variable (Mn : Means E P.D P.C P.kap)

/-- The letters at the value have the record's numbers, where 4 variables number a bit. -/
theorem ownAt_fits (hk : P.kap = 4) (rows : ℕ) : OwnFits (P.own Mn) (recOf P rows) where
  units := ⟨⟨sc3_fits _, by show 24 * (3 * P.npl) + 24 * 7 = 24 * (3 * P.npl + 7); omega⟩,
    ⟨sc3_fits _, rfl⟩, trivial⟩
  sE := ⟨sc3_fits _, by show 0 + 24 * (5 + P.D.lT + 2) = 24 * (5 + P.D.lT + 2); omega⟩
  sVM := ⟨sc3_fits _, rfl⟩
  sVD := ⟨sc3_fits _, rfl⟩
  nz := by
    show P.D.lg + P.D.lT + (P.kap + P.D.lg + P.D.lT) = 2 * P.D.lg + 2 * P.D.lT + 4
    omega
  np := rfl
  sF := ⟨sc3_fits _, rfl⟩
  sD := ⟨⟨(scd_fits (step18 P.D P.rd (fun _ _ => 0) P.w18 P.c18)).withY,
    (scd_fits (step18 P.D P.rd (fun _ _ => 0) P.w18 P.c18)).degs,
    (scd_fits (step18 P.D P.rd (fun _ _ => 0) P.w18 P.c18)).degY,
    (scd_fits (step18 P.D P.rd (fun _ _ => 0) P.w18 P.c18)).vals⟩, rfl⟩
  sH := ⟨sc3_fits _, rfl⟩

/-- The shape of the chain at the value is what the port's own planAttentionOwn adds. -/
theorem ownAt_planned (hk : P.kap = 4) (rows : ℕ) (Ex : ExtSpec) (s : Setting)
    (p q : PlanState) (hp : At s 0 p) (hq : planAttentionOwn (recOf P rows) p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E ((P.own Mn).ch.R Ex).shape (l.map (·.entry)) :=
  own_planned (P.own Mn) (recOf P rows) (ownAt_fits P Mn hk rows) Ex s p q hp hq

/-- The chain's errors at the value are the numerators of the plan's bounds, but at the draw of the
point, where the chain counts v * |E| ^ (v - 1) bad points among all, for v coordinates. -/
theorem ownAt_nums (hk : P.kap = 4) (rows : ℕ) (Ex : ExtSpec) :
    errList ((P.own Mn).ch.eps Ex) =
      numsZ ((P.g1 + P.g2) * Fintype.card E ^ (P.g1 + P.g2 - 1)) (recOf P rows) :=
  own_nums (P.own Mn) (recOf P rows) (ownAt_fits P Mn hk rows) Ex

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.ownAt_fits
#print axioms OnBytes.Tie.Pv.Att.ownAt_planned
#print axioms OnBytes.Tie.Pv.Att.ownAt_nums
