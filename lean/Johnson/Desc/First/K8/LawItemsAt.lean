--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawItemsAt.lean: THE SMALLNESS TEST'S ITEMS OF THE TABLE OF JOINTS: THE TABLE
OF CELLS BY THE SEGMENT'S NUMBER; AND "THE DIGITS ARE IN THEIR TABLES" AT THE PLAN'S RECORD.

  (IN Johnson/Desc/First/K8/TieAtSegment.lean, a file of its own over LawItems.lean alone:)
  `tieK8At A`, `tieK8At_eq`: A RIGHTING OF `tieK8` (Johnson/Desc/First/K8/LawItems.lean), WHICH
    DROPS THE SEGMENT'S NUMBER: an array's number is the link's own (the link's table of arrays):
    ONE table of cells A cannot serve two segments. Here A takes the segment's number first: at
    segment m the sentence is `TieAt (A m)`. At one m it is `tieK8 (A m)`.
  (IN Johnson/Desc/First/K8/DigitsOf.lean, a light file over the library alone:)
  `DigitsOf tl A`: the sentence of `DigitsAt` at a record tl and a table of cells A.
  `digitsAt_iff`: `DigitsAt A s w` says: a link is open, and `DigitsOf` holds at its record.
  `digitsOf_congr`: **two records with the same `wideOf`
    (Johnson/Desc/First/K8/LawWide.lean) have the same sentence**: it reads the number of matrices,
    the matrices' rows, the number of combinations, the digits' array's number and the digits'
    columns: all fields of `wideOf`.
  `digitsAt_congr`: **so, where `wide s` is the plan's record's, `DigitsAt A s w` is `DigitsOf` at
    the plan's record.**
  `wide_of_tests`: `wide s` from the public item "K8.lay7" (`Ready.lay7`, Cond.lean) and three
    equations more (the number of combinations, the mark "closed", the list).
  `colsTest_of_seven`: the lookup's public test on the digits' columns reads four of these seven
    fields: at the run's value it says what it says at the plan's.
Definitions, statements and proofs.
Limits. WHICH TABLE OF CELLS A m IS stays a letter: that it reads the witness's messages at the
link's own list's seats is an equation owed where it is filled. Nothing on soundness.

-/
import Johnson.Desc.First.K8.TieAtSegment
import Johnson.Desc.First.K8.LawWide
import Johnson.Desc.First.K8.DigitsOf
import OnBytes.Tie.Pv.Lookup.Digits.PortCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes OnBytes.Model

theorem digitsAt_iff {W : Type} (A : W → ℕ → ℕ → ℕ → Cb.Gl.E) (s : S) (w : W) :
    DigitsAt A s w ↔ ∃ tl, s.tl? = some tl ∧ DigitsOf tl (A w) := Iff.rfl

/-- **Two records with the same reading have the same sentence.** -/
theorem digitsOf_congr {tl tl' : HTailF2} (h : wideOf tl = wideOf tl')
    (A : ℕ → ℕ → ℕ → Cb.Gl.E) : DigitsOf tl A ↔ DigitsOf tl' A := by
  have hs := (wide_congr h).1
  simp only [wideOf, Ready.seven, Prod.mk.injEq] at h
  obtain ⟨⟨_, a2, a3, a4, a5, _, a7⟩, a8, _, _⟩ := h
  have hz : ∀ μ q i, tl.zzCol μ q i = tl'.zzCol μ q i := fun μ q i => by
    simp only [HTailF2.zzCol, a5, a7, a3, a4]
  unfold DigitsOf
  simp only [hs, a2, a5, a7, a8, hz]

/-- **At the plan's record.** -/
theorem digitsAt_congr {W : Type} (A : W → ℕ → ℕ → ℕ → Cb.Gl.E) (s : S) (w : W) (tlP : HTailF2)
    (h : wide s = some (wideOf tlP)) : DigitsAt A s w ↔ DigitsOf tlP (A w) := by
  unfold wide at h
  cases ht : s.tl? with
  | none => rw [ht] at h; exact nomatch h
  | some tl =>
    rw [ht] at h
    have e : wideOf tl = wideOf tlP := Option.some.inj h
    rw [digitsAt_iff, ht]
    constructor
    · rintro ⟨tl', e', hd⟩
      obtain rfl := Option.some.inj e'
      exact (digitsOf_congr e _).1 hd
    · exact fun hd => ⟨tl, rfl, (digitsOf_congr e _).2 hd⟩

/-- `wide s` from the public item on seven fields and three equations more. -/
theorem wide_of_tests {s : S} {tlP tl : HTailF2} (ht : s.tl? = some tl)
    (h7 : Ready.lay7 s = some (Ready.seven tlP)) (h8 : tl.tau = tlP.tau)
    (h9 : tl.funClosed = tlP.funClosed) (h10 : tl.funs = tlP.funs) :
    wide s = some (wideOf tlP) := by
  unfold Ready.lay7 at h7
  rw [ht] at h7
  have e7 : Ready.seven tl = Ready.seven tlP := Option.some.inj h7
  unfold wide wideOf
  rw [ht, Option.map_some, e7, h8, h9, h10]

/-- The lookup's public test on the digits' columns (`OnBytes.DgP.colsTest`,
OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean) reads four of the seven fields of the public item
"K8.lay7": so at the run's value it says what it says at the plan's. -/
theorem colsTest_of_seven {tl tlP : HTailF2} (h : Ready.seven tl = Ready.seven tlP) :
    OnBytes.DgP.colsTest tl = OnBytes.DgP.colsTest tlP := by
  simp only [Ready.seven, Prod.mk.injEq] at h
  obtain ⟨_, _, a3, a4, a5, _, a7⟩ := h
  rw [Bool.eq_iff_iff]
  simp only [OnBytes.DgP.colsTest, Bool.and_eq_true, decide_eq_true_eq, OnBytes.DgP.offOf,
    OnBytes.DgP.mOf, a3, a4, a5, a7]

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.digitsOf_congr
#print axioms VerifiableInference.Desc.First.K8.digitsAt_congr
#print axioms VerifiableInference.Desc.First.K8.wide_of_tests
#print axioms VerifiableInference.Desc.First.K8.colsTest_of_seven
