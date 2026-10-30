-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/CsValues.lean: the code switches of a list of places, as values of the library's
record, and the conditions of their knowledge soundness at these values.

A place is two neighbouring stages of a proximity test, in numbers (`Sg`,
OnBytes/Slice/Stage.lean), and two radii. The library's data at a place is `csSw`
(OnBytes/Slice/CsData.lean). The statement and its conditions are those of Cb/Pv/Tower/Cs.lean
(`CsSize.H`, `CsSize.OK`). The tests on numbers are those of Johnson/Top/H/StageJ.lean.
Definitions, statements and proofs.
Main names:
  `csSw_hypK`: for all stages: if the sizes fit (`CsFit`), both stages have their sizes in order
    and the radius after the switch is below the Johnson radius of the new stage, then `csSw`
    meets `LdSw.HypK` at the Johnson bound on the new stage's lists. No count of agreement is
    asked.
  `CsPlace`, `CsPlace.good`: a place, data alone; the four tests together.
  `CsPlace.sizeMid`, `CsPlace.sizeLast`, `CsPlace.size`: the record `CsSize` at a place. The rider
    is the new stage's fresh mask rows or, where the new stage has no row variable, its masking
    word.
  `CsPlace.size_ok`, `CsPlace.size_local`: at a good place the record meets `CsSize.OK` and
    `CsSize.OKLocal`.
  `sizesCs`, `CCs`, `cCs`, `sizesCs_length`, `hCs`: the list of records; the condition at every
    member; it holds if every place is good; then no place is left out; and the statement holds at
    every member.
Limits: that the places of a given file are good is not shown here: it is a test on numbers. The
radii are the caller's. A leaf of the new tree is a position of the new stage, and holds the
symbols of both tables and of the rider at that position: that this is the program's layout is not
shown, and the conditions do not read it. A main code over the base field is read as a code over
the extension field. A group's number of slots is not read: `stageOf` is the group's stage only
where that number is 1.

-/
import Cb.Pv.Tower.Cs
import Johnson.Top.H.StageJ
import OnBytes.Slice.CsSmp
import OnBytes.Slice.CloseKnow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Pv.Tower

/-- The conditions of the code switch, at the library's data for two stages. -/
theorem csSw_hypK {s s' : Sg} (hf : CsFit s s') (hs : s.Sized) (hs' : s'.Sized) {e' : ℕ}
    (hj : InJ s' e') : (csSw hf).HypK e' (lstJ s' e') :=
  ⟨(Sg.fit_cMid hs).laws, listJ_of (Sg.fit_cIn hs') hj, csSample_ok hf,
    ok_powers_comap _ _ (csRowNo_inj s)⟩

/-- A place: two stages and two radii. -/
structure CsPlace where
  s : Sg
  s' : Sg
  e : ℕ
  e' : ℕ

/-- The four tests. -/
def CsPlace.good (x : CsPlace) : Bool :=
  decide (CsFit x.s x.s') && sizedB x.s && sizedB x.s' && inJB x.s' x.e'

/-- The record at a place whose new stage is folded: the rider is its fresh mask rows. -/
noncomputable def CsPlace.sizeMid (x : CsPlace) (hf : CsFit x.s x.s') : CsSize GE where
  P := x.s.Ps
  P' := x.s'.Ps
  Pw := x.s'.Ps
  St := x.s.cMid.J → GE
  D := csSw hf
  Cw := x.s'.cFr
  Pt := x.s'.Ps
  lf := Sum.elim id id
  lfW := id
  e := x.e
  e' := x.e'
  L := lstJ x.s' x.e'

/-- The record at a place whose new stage is the last: the rider is its masking word. -/
noncomputable def CsPlace.sizeLast (x : CsPlace) (hf : CsFit x.s x.s') : CsSize GE where
  P := x.s.Ps
  P' := x.s'.Ps
  Pw := x.s'.Ps
  St := x.s.cMid.J → GE
  D := csSw hf
  Cw := x.s'.cIn
  Pt := x.s'.Ps
  lf := Sum.elim id id
  lfW := Sum.elim id id
  e := x.e
  e' := x.e'
  L := lstJ x.s' x.e'

/-- The record at a place. -/
noncomputable def CsPlace.size (x : CsPlace) (hf : CsFit x.s x.s') : CsSize GE :=
  if x.s'.h + x.s'.g = 0 then x.sizeLast hf else x.sizeMid hf

theorem CsPlace.size_ok (x : CsPlace) (hf : CsFit x.s x.s') (h : x.good = true) :
    (x.size hf).OK := by
  simp only [CsPlace.good, Bool.and_eq_true] at h
  have k := csSw_hypK hf (sized_of h.1.1.2) (sized_of h.1.2) (inJ_of h.2)
  unfold CsPlace.size
  split
  · exact k
  · exact k

/-- At a good place the new code reads what it declares. -/
theorem CsPlace.size_local (x : CsPlace) (hf : CsFit x.s x.s') (h : x.good = true) :
    (x.size hf).OKLocal := by
  simp only [CsPlace.good, Bool.and_eq_true] at h
  have k : x.s'.cIn.Reads := (Sg.fit_cIn (sized_of h.1.2)).laws.loc
  unfold CsPlace.size
  split
  · exact k
  · exact k

/-- The records of a list of places. -/
noncomputable def sizesCs (L : List CsPlace) : List (CsSize GE) :=
  L.filterMap fun x => if hf : CsFit x.s x.s' then some (x.size hf) else none

/-- The condition at every record. -/
def CCs (L : List CsPlace) : Prop := ∀ z ∈ sizesCs L, z.OK

theorem cCs (L : List CsPlace) (h : ∀ x ∈ L, x.good = true) : CCs L := by
  intro z hz
  obtain ⟨x, hx, hxz⟩ := List.mem_filterMap.1 hz
  by_cases hf : CsFit x.s x.s'
  · rw [dif_pos hf] at hxz
    rw [← Option.some.inj hxz]
    exact x.size_ok hf (h x hx)
  · rw [dif_neg hf] at hxz
    cases hxz

/-- No place is left out. -/
theorem sizesCs_length : ∀ L : List CsPlace, (∀ x ∈ L, x.good = true) →
    (sizesCs L).length = L.length
  | [], _ => rfl
  | x :: L, h => by
    have hx := h x (List.mem_cons_self ..)
    simp only [CsPlace.good, Bool.and_eq_true, decide_eq_true_eq] at hx
    have ih := sizesCs_length L fun y hy => h y (List.mem_cons_of_mem _ hy)
    unfold sizesCs at ih ⊢
    rw [List.filterMap_cons, dif_pos hx.1.1.1, List.length_cons, List.length_cons, ih]

/-- The statement holds at every record. -/
theorem hCs (L : List CsPlace) (h : ∀ x ∈ L, x.good = true) : ∀ z ∈ sizesCs L, z.H :=
  fun z hz => z.h (cCs L h z hz)

end Johnson.Top.H

#print axioms Johnson.Top.H.csSw_hypK
#print axioms Johnson.Top.H.cCs
#print axioms Johnson.Top.H.hCs
