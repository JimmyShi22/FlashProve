-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/TestOf.lean: a whole proximity test on a group of sent oracle messages as a function
of the group's data and of the list of its later stages, with the conditions of all its blocks.

The group, its shape and the switch behind the first fold are those of
Johnson/Top/H/GroupRows.lean and Johnson/Top/H/FirstRows.lean; the stages behind the first are
made by `towOf` (Johnson/Top/H/TowerOf.lean). Where sizes do not fit, or where there is no later
stage, the maker returns nothing. Also the list of stages from the planner's own records.
Definitions, statements and proofs.
Main names:
  `Rows.towOf R bC bZ c₁ z₁ Sb sl Z l`: the data of the test: the first stage on the group, at the
    counts c₁ and z₁, then the stages l.
  `Rows.goodT R l`: the test on numbers for the stages: the first stage's radius is below the
    Johnson radius, it fits the next stage, and `goodL` holds behind it.
  `Rows.towOf_some`, `Rows.towOf_hypK`, `Rows.towOf_reads`: under `Rows.goodT` the maker returns a
    test; with `Rows.Good`, `CountsAt` at the first stage and `CntL` behind it, the conditions
    of all blocks hold; what locality asks holds.
  `Rows.testOf`, `Rows.testOf_know`: the arrangement and the test, from the joint at which the
    round before the test ends; it is knowledge sound under the same.
  `stagesOf σ L`: the stages and radii of a list of the planner's sized stages.
Limits: the limits of the files named hold here. A test of one stage alone, whose last step would
stand on the group, is not laid. `CountsAt` and `CntL` are not proved here. That `stagesOf` gives
the numbers by which a plan is priced is not shown. The makers are evaluated at no list here.

-/
import Johnson.Top.H.FirstRows
import Johnson.Top.H.TowerOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Pv.Tower

namespace Rows
variable {S : Sig GE} (R : Rows S) (bC bZ : Sg → ℕ → ℕ) (c₁ z₁ : ℕ) {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))

/-- The data of the test: the first stage on the group, then the stages l. -/
noncomputable def towOf : List (Sg × ℕ) →
    Option (TowR (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) R.Sh.par.Cw.nat)
  | [] => none
  | x :: l =>
    if hf : CsFit R.s x.1 then
      (Johnson.Top.H.towOf bC bZ l x.1 x.2 ((R.sw Sb sl Z hf).D R.G.e).sl').map fun r =>
        TowR.step R.Sh.par (R.Sh.form Sb sl Z) R.G.e (1, 1) (R.sw Sb sl Z hf) r.Cw x.1.Ps
          (Sum.elim id id) r.lfW R.s.d (fun _ => lstJ R.s R.e) (fun _ => c₁) (fun _ => z₁)
          (fun _ => z₁) x.2 (lstJ x.1 x.2) r.T
    else none

/-- The test on numbers for the stages. -/
def goodT : List (Sg × ℕ) → Bool
  | [] => false
  | x :: l => decide (CsFit R.s x.1) && inJB R.s R.e && goodL l x.1 x.2

theorem towOf_some : ∀ l, R.goodT l = true → (R.towOf bC bZ c₁ z₁ Sb sl Z l).isSome = true
  | [], h => absurd h Bool.false_ne_true
  | x :: l, h => by
    simp only [goodT, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [towOf, dif_pos h.1.1, Option.isSome_map]
    exact Johnson.Top.H.towOf_some bC bZ l x.1 x.2 _ h.2

theorem towOf_hypK (hg : R.Good) (hc : CountsAt R.s R.e c₁ z₁) :
    ∀ l, R.goodT l = true → (∀ x l', l = x :: l' → CntL bC bZ l' x.1 x.2) →
    ∀ T, R.towOf bC bZ c₁ z₁ Sb sl Z l = some T → T.HypK
  | [], h, _, _, _ => absurd h Bool.false_ne_true
  | x :: l, h, hl, T, hT => by
    simp only [goodT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs', hj'⟩ := good_head h.2
    rw [towOf, dif_pos h.1.1] at hT
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hT
    exact And.intro (R.hypK Sb sl Z hg (inJ_of h.1.2) hc)
      (And.intro (R.sw_hypK Sb sl Z h.1.1 _ hg.sized hs' hj')
        (Johnson.Top.H.towOf_hypK bC bZ l x.1 x.2 _ h.2 (hl x l rfl) r hr))

theorem towOf_reads : ∀ l, R.goodT l = true →
    ∀ T, R.towOf bC bZ c₁ z₁ Sb sl Z l = some T → T.Reads
  | [], h, _, _ => absurd h Bool.false_ne_true
  | x :: l, h, T, hT => by
    simp only [goodT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hs', _⟩ := good_head h.2
    rw [towOf, dif_pos h.1.1] at hT
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hT
    exact And.intro (R.sw_reads Sb sl Z h.1.1 _ hs')
      (Johnson.Top.H.towOf_reads bC bZ l x.1 x.2 _ h.2 r hr)

/-- The arrangement and the test, from the joint at which the round before the test ends. -/
noncomputable def testOf (l : List (Sg × ℕ)) :
    Option (EndR (R.G.joint Sb sl Z) R.Sh.par.Cw.nat) :=
  (R.towOf bC bZ c₁ z₁ Sb sl Z l).map (R.test Sb sl Z)

theorem testOf_know (hg : R.Good) (hc : CountsAt R.s R.e c₁ z₁) (l : List (Sg × ℕ))
    (h : R.goodT l = true) (hl : ∀ x l', l = x :: l' → CntL bC bZ l' x.1 x.2)
    (W : EndR (R.G.joint Sb sl Z) R.Sh.par.Cw.nat)
    (hW : R.testOf bC bZ c₁ z₁ Sb sl Z l = some W) : W.Know := by
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hW
  exact R.test_know Sb sl Z T hg (R.towOf_hypK bC bZ c₁ z₁ Sb sl Z hg hc l h hl T hT)

end Rows

/-- The stages and radii of a list of the planner's sized stages. -/
def stagesOf (σ : Setting) (L : List StageSize) : List (Sg × ℕ) :=
  L.map fun x => (stageOf x.g x.t, radiusOf σ x.g)

end Johnson.Top.H

#print axioms Johnson.Top.H.Rows.towOf_some
#print axioms Johnson.Top.H.Rows.towOf_hypK
#print axioms Johnson.Top.H.Rows.testOf_know
