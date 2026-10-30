-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/FoldValues.lean: the folds of a list of places, as values of the library's record,
and the conditions of their knowledge soundness at these values, clause by clause.

A place is a stage of a proximity test, in numbers (`Sg`, OnBytes/Slice/Stage.lean), a radius and
two counts. The library's parameters at a stage are `Sg.par` (OnBytes/Slice/FoldPeel.lean). The
statement and its conditions are those of Cb/Pv/Tower/Fold.lean (`FoldSize.HOwn`,
`FoldSize.HRide`, `FoldSize.OK`). Definitions, statements and proofs.
Main names:
  `par_inj`, `par_deg`, `par_qw`: three clauses of `SumPar.HypK` hold at every stage.
  `par_codes`: the clause on the codes, from `Sg.Sized` and a radius below the stage's distance.
  `par_errs`: the clause on lists and counts: the lists by the Johnson bound, which is a theorem;
    the counts from `CountsAt` (Johnson/Top/H/StageJ.lean), which is asked.
  `par_hypK`: the five together.
  `FoldPlace`, `FoldPlace.good`, `FoldPlace.size`, `sizesFold`: a place, data alone; its two
    tests; its record; the list of records.
  `FoldPlace.size_pick`: at every place the choice of the coefficient is lawful (`FoldSize.Pick`).
  `CFoldCounts L`: the one condition that is asked: at every place of L a line through two
    words has at most bC exceptional points for one main row and at most bZ for one mask row.
  `cFold`, `hFoldOwn`, `hFoldRide`: under it, and if every place is good, every record meets the
    conditions, and the statement holds in both forms.
Limits: `CFoldCounts` is not proved here; where `CountsAt` is proved or derived is said in the
limits of Johnson/Top/H/StageJ.lean. That the places of a given file are good is a test on
numbers, not made here. The radius and the counts are the caller's. The number n0 of `Sg.par` is
the caller's; the conditions hold at every n0. What Johnson/Top/H/StageJ.lean says of the base
field and of slots holds here too.

-/
import Cb.Pv.Tower.Fold
import Cb.Ent.FoldShortProofs
import Johnson.Top.H.StageJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Pv.Tower

theorem par_inj (s : Sg) (n0 : ℕ) : Function.Injective (s.par n0).val := Function.injective_id

theorem par_deg (s : Sg) (n0 : ℕ) : 2 ≤ (s.par n0).n := le_rfl

theorem par_qw (s : Sg) (n0 : ℕ) : (s.par n0).QwDeg := fun j => hideW_deg s.h s.g n0 j.val

theorem par_codes {s : Sg} (n0 : ℕ) (hs : s.Sized) {e : ℕ} (he : e < s.d) :
    Spec.CodesOK GE s.Ps (s.par n0).C (s.par n0).Z (s.par n0).Zw s.d e := Sg.codesOK hs he

theorem par_errs {s : Sg} (n0 : ℕ) (hs : s.Sized) {e bC bZ : ℕ} (hj : InJ s e)
    (hc : CountsAt s e bC bZ) :
    (s.par n0).ErrOK e (fun _ => lstJ s e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) :=
  have h := foldNums_joh hs hj hc
  ⟨h.list, h.mcaC, h.mcaS, h.mcaW⟩

/-- The conditions of the fold, at the library's parameters for a stage. -/
theorem par_hypK {s : Sg} (n0 : ℕ) (hs : s.Sized) {e bC bZ : ℕ} (hj : InJ s e)
    (hc : CountsAt s e bC bZ) :
    (s.par n0).HypK s.d e (fun _ => lstJ s e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) :=
  ⟨par_codes n0 hs hj.1, par_errs n0 hs hj hc, par_inj s n0, par_deg s n0, par_qw s n0⟩

/-- A place: a stage, the number n0 of `Sg.par`, a radius, two counts. -/
structure FoldPlace where
  s : Sg
  n0 : ℕ
  e : ℕ
  bC : ℕ
  bZ : ℕ

/-- The two tests. -/
def FoldPlace.good (x : FoldPlace) : Bool := sizedB x.s && inJB x.s x.e

/-- The record at a place. The linear coefficient is the one that is left out. -/
noncomputable def FoldPlace.size (x : FoldPlace) : FoldSize GE where
  P := x.s.Ps
  Y := x.s.par x.n0
  fx := (1, 1)
  d := x.s.d
  e := x.e
  Lst := fun _ => lstJ x.s x.e
  mC := fun _ => x.bC
  mS := fun _ => x.bZ
  mW := fun _ => x.bZ

/-- At every place no check of the fold's is left: the "sum" of X over 0 and 1 is 1. -/
theorem FoldPlace.size_pick (x : FoldPlace) : x.size.Pick := ldEnt_foldS_lin GE 1

/-- The records of a list of places. -/
noncomputable def sizesFold (L : List FoldPlace) : List (FoldSize GE) := L.map FoldPlace.size

/-- The condition that is asked: the counts of exceptional points. -/
def CFoldCounts (L : List FoldPlace) : Prop := ∀ x ∈ L, CountsAt x.s x.e x.bC x.bZ

theorem cFold (L : List FoldPlace) (h : ∀ x ∈ L, x.good = true) (hc : CFoldCounts L) :
    ∀ z ∈ sizesFold L, z.OK := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
  have hg := h x hx
  simp only [FoldPlace.good, Bool.and_eq_true] at hg
  exact par_hypK x.n0 (sized_of hg.1) (inJ_of hg.2) (hc x hx)

theorem hFoldOwn (L : List FoldPlace) (h : ∀ x ∈ L, x.good = true) (hc : CFoldCounts L) :
    ∀ z ∈ sizesFold L, z.HOwn := fun z hz => z.hOwn (cFold L h hc z hz)

theorem hFoldRide (L : List FoldPlace) (h : ∀ x ∈ L, x.good = true) (hc : CFoldCounts L) :
    ∀ z ∈ sizesFold L, z.HRide := fun z hz => z.hRide (cFold L h hc z hz)

end Johnson.Top.H

#print axioms Johnson.Top.H.par_hypK
#print axioms Johnson.Top.H.cFold
