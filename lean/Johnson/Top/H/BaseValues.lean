-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BaseValues.lean: the last steps of a list of places, as values of the library's
record, and the conditions of their knowledge soundness at these values.

A place is the last stage of a proximity test, in numbers (`Sg`, OnBytes/Slice/Stage.lean), a
radius and two counts. The joint before the last step has the stage's two tables as its code. The
statement and its conditions are those of Cb/Pv/Tower/Base.lean (`BaseSize.H`, `BaseSize.OK`).
Definitions, statements and proofs.
Main names:
  `jointOf s e`: the joint: the code `Sg.cIn`, a form given as its vector of coefficients, the
    radius e.
  `joint_hypK`: `LdJoint.BaseHypK` at that joint, at the stage's distance, the count bC + bZ and
    the Johnson bound on lists of pairs: from `Sg.Sized`, `InJ` and `CountsAt`
    (Johnson/Top/H/StageJ.lean).
  `BasePlace`, `BasePlace.good`, `BasePlace.size`, `sizesBase`: a place, data alone; its two
    tests; its record; the list of records.
  `CBaseCounts L`: the one condition that is asked: `CountsAt` at every place of L.
  `cBase`, `hBase`: under it, and if every place is good, every record meets the conditions, and
    the statement holds.
Limits: `CBaseCounts` is not proved here; where `CountsAt` is proved or derived is said in the
limits of Johnson/Top/H/StageJ.lean. That the places of a given file are good is a test on
numbers, not made here. A native position of either table is read at the tree's position of the
same number: that this is the program's layout is not shown, and the conditions do not read it.
That a last stage has no row variable is not asked here.

-/
import Cb.Pv.Tower.Base
import Johnson.Top.H.StageJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Pv.Tower

/-- The joint before the last step. -/
noncomputable def jointOf (s : Sg) (e : ℕ) : LdJoint GE where
  P := s.Ps
  C := s.cIn
  St := s.cIn.J → GE
  sl := Slf.idf
  e := e

/-- The conditions of the last step, at the joint of a stage. -/
theorem joint_hypK {s : Sg} (hs : s.Sized) {e bC bZ : ℕ} (hj : InJ s e)
    (hc : CountsAt s e bC bZ) : (jointOf s e).BaseHypK s.d (bC + bZ) (lstJ s e) :=
  have h := baseCodes_joh hs hj hc
  ⟨h.laws, hj.1, h.mca, h.list⟩

/-- A place: a stage, a radius, two counts. -/
structure BasePlace where
  s : Sg
  e : ℕ
  bC : ℕ
  bZ : ℕ

/-- The two tests. -/
def BasePlace.good (x : BasePlace) : Bool := sizedB x.s && inJB x.s x.e

/-- The record at a place. -/
noncomputable def BasePlace.size (x : BasePlace) : BaseSize GE where
  a := jointOf x.s x.e
  t := x.s.t
  cov := Sum.elim id id
  d := x.s.d
  bad := x.bC + x.bZ
  L2 := lstJ x.s x.e

/-- The records of a list of places. -/
noncomputable def sizesBase (L : List BasePlace) : List (BaseSize GE) := L.map BasePlace.size

/-- The condition that is asked: the counts of exceptional points. -/
def CBaseCounts (L : List BasePlace) : Prop := ∀ x ∈ L, CountsAt x.s x.e x.bC x.bZ

theorem cBase (L : List BasePlace) (h : ∀ x ∈ L, x.good = true) (hc : CBaseCounts L) :
    ∀ z ∈ sizesBase L, z.OK := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
  have hg := h x hx
  simp only [BasePlace.good, Bool.and_eq_true] at hg
  exact joint_hypK (sized_of hg.1) (inJ_of hg.2) (hc x hx)

theorem hBase (L : List BasePlace) (h : ∀ x ∈ L, x.good = true) (hc : CBaseCounts L) :
    ∀ z ∈ sizesBase L, z.H := fun z hz => z.h (cBase L h hc z hz)

end Johnson.Top.H

#print axioms Johnson.Top.H.joint_hypK
#print axioms Johnson.Top.H.cBase
