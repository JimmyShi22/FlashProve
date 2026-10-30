-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/PlanJoin.lean: the plain sumcheck with n further scalars has, round by round, the
numbers of scalars and of drawn elements that the port's planner writes for a masked sumcheck, and
its errors are the numerators of the bounds that the planner hands to close.

The port plans a masked sumcheck by planPsc x, for a record x : PscSize
(OnBytes/Params/Planner.lean). Scalars that were planned before it and have no round of their own
stand in the message of its first round.

Definitions. PlainSc.Fits T x: the record x has the numbers of the parameters T: it has the further
variable; its degrees, each less 1, are T's; its degree in the further variable is DY; it shows as
many values as T has maps. (A record's degree g stands for a polynomial with g coefficients, of
which g - 1 are sent.)

Statements. lPsc_entries: the closed list of a masked sumcheck's entries, with 24 n bytes open, is
pscEntries. plain_plan: so the block's shape is that list. plain_planPsc: for every setting, every
record that fits and every state of the planner in a request's scope with 24 n bytes and no root or
answer open (At, OnBytes/Tie/Pv/Att/PlanCalc.lean): if planPsc x ends well, the rounds that it has
added have entries of which the block's shape is an instance (ShapeIs). plain_errs: the block's
errors, as a list of numbers, are the numerators of the plan's bounds, round by round; plain_bounds:
the plan's bounds are these numerators over the setting's cardE, and over cardE - 1 in the round of
the further variable; where the verifier says nothing the plan has no bound and the block the error
0. sc3_fits, sc3_planPsc, sc3_errs: the sumcheck of products fits attentionSc3 nv nb.

Limits. As in OnBytes/Tie/Pv/Att/Shape.lean: ShapeIs counts. Nothing says that the setting's cardE
is the number of elements of E, nor what a bound is as a number. "The plan's bounds" are the bounds
that planPsc hands to close (bPsc, OnBytes/Tie/Pv/Att/PlanOwnW.lean); close counts them once for
each instance and rounds; nothing here says that the factor is 1.
-/
import OnBytes.Tie.Pv.Att.Shape
import OnBytes.Tie.Pv.Att.PlanNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb Cb.Pv.Att TWhole Johnson.L5.Layers OnBytes OnBytes.G4 OnBytes.Params
open OnBytes.Tie.Pv.Att.Plan

theorem lPsc_entries (w n : ℕ) (x : PscSize) (h : x.withY = true) :
    lPsc w (24 * n) x = pscEntries w n (x.degree.map (· - 1)) x.degreeY x.values := by
  simp [lPsc, pscEntries, h, eDraw, eY, eValues, Function.comp_def]

variable {E : Type} [Field E] [Fintype E]

/-- The record has the parameters' numbers. -/
structure _root_.Cb.Pv.Att.PlainSc.Fits (T : PlainSc E) (x : PscSize) : Prop where
  withY : x.withY = true
  degs : x.degree.map (· - 1) = List.ofFn T.deg
  degY : x.degreeY = T.DY
  vals : x.values = Fintype.card T.A

theorem plain_plan (T : PlainSc E) (x : PscSize) (hx : T.Fits x) (w n : ℕ) :
    ShapeIs E (shapeRN T.our.par n) (lPsc w (24 * n) x) := by
  rw [lPsc_entries w n x hx.withY, hx.degs, hx.degY, hx.vals]
  exact plain_shape T w n

/-- The block's shape has the three numbers of each entry that the port's own planPsc adds. -/
theorem plain_planPsc (T : PlainSc E) (x : PscSize) (hx : T.Fits x) (n : ℕ)
    (F : ∀ st, HFixs (T.our.par.vars st)) {X : Type} (cl : X → (Fin n → E) → E × T.St)
    (Ex : ExtSpec) (s : Setting) (p q : PlanState) (hp : At s (24 * n) p)
    (h : planPsc x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (rideNR T.our.par n F cl Ex).shape (l.map (·.entry)) :=
  ⟨wPsc s (24 * n) x, (addsW_psc s (24 * n) x p q hp h).2, by
    rw [wPsc_entries]
    exact plain_plan T x hx _ n⟩

/-- The block's errors are the numerators of the plan's bounds. -/
theorem plain_errs (T : PlainSc E) (x : PscSize) (hx : T.Fits x) (n c : ℕ) (Ex : ExtSpec) :
    errList (rideNE T.our.par n Ex) = numsOf (qPsc c x) := by
  rw [plain_nums, nums_psc, hx.degs, hx.degY, hx.withY]
  simp

/-- The plan's bounds: the pairs of qPsc, read as the port's ratios; the denominators. -/
theorem plain_bounds (x : PscSize) (h : x.withY = true) (s : Setting) :
    bPsc s x = (qPsc s.cardE x).map boundOf ∧
      (qPsc s.cardE x).map (fun o => o.map (·.2)) =
        some s.cardE :: (x.degree.map (fun _ => some s.cardE) ++ [some (s.cardE - 1), none]) :=
  ⟨bPsc_ratios s x, dens_psc s.cardE x h⟩

theorem sc3_fits (T : Sc3 E) : T.plain.Fits (attentionSc3 T.nv T.nb) where
  withY := rfl
  degs := by
    show (List.replicate T.nv 4).map (· - 1) = List.ofFn fun _ : Fin T.nv => 3
    rw [List.map_replicate, List.ofFn_const]
  degY := rfl
  vals := by
    show 2 * T.nb = Fintype.card (Fin T.nb × Bool)
    simp [Nat.mul_comm]

theorem sc3_planPsc (T : Sc3 E) (n : ℕ) (F : ∀ st, HFixs (T.plain.our.par.vars st)) {X : Type}
    (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) (s : Setting) (p q : PlanState)
    (hp : At s (24 * n) p) (h : planPsc (attentionSc3 T.nv T.nb) p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (rideNR T.plain.our.par n F cl Ex).shape (l.map (·.entry)) :=
  plain_planPsc T.plain _ (sc3_fits T) n F cl Ex s p q hp h

theorem sc3_errs (T : Sc3 E) (n c : ℕ) (Ex : ExtSpec) :
    errList (rideNE T.plain.our.par n Ex) = numsOf (qPsc c (attentionSc3 T.nv T.nb)) :=
  plain_errs T.plain _ (sc3_fits T) n c Ex

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.plain_planPsc
#print axioms OnBytes.Tie.Pv.Att.plain_errs
#print axioms OnBytes.Tie.Pv.Att.plain_bounds
#print axioms OnBytes.Tie.Pv.Att.sc3_planPsc
#print axioms OnBytes.Tie.Pv.Att.sc3_errs
