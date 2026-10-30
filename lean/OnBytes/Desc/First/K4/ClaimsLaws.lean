-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/ClaimsLaws.lean: what a run of claims of the layers' own rounds is made of.

`formsFront`, `formsFrontNoRows` and `formsBack` (OnBytes/Desc/First/K4/Plain.lean) return a list of
forms and a ledger. Here a run that returns is cut into its parts, so that "every form of the run is
worth 0" gives "every form of group n is worth 0", and each of the three own claims that are made
only then is known as the sumcheck's `rowForm`.

  `ownClaim_some`: the own claim is p.rowForm S0 kept; the sumcheck's four conditions hold; the
      ledger behind is the ledger in front with the hiding coefficients laid.
  `front_some`: the seven groups' lists are there, and the list is they, in the protocol's order.
  `formsFrontWith_some`: the shown values; the two own claims; `front` at them; and ALL THAT THE RUN
      DOES TO THE LEDGER: two layings of hiding coefficients (`Fork.hideRun`) and one or two marks
      (`Fork.paid`).
  `formsBack_some`: the merge's own claim; the four forms; one laying and one mark.
  `mem_front_*`: each group's forms are members of the run's list.

Limits. Equations between data: nothing on what a form is worth, on a draw, on soundness.

-/
import OnBytes.Desc.First.K4.Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc

theorem ownClaim_some {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {a : Aff}
    (h : ownClaim p S0 kept F = some (a, G)) :
    a = p.rowForm S0 kept ∧
      (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G := by
  unfold ownClaim at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp h
  have hx' : Fl.andThen
      (Fl.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size))
      (fun _ => Fl.andThen
        (Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)))
        (fun _ => Fl.ret (p.rowForm S0 kept, { p with rowMade := true }))) F [] = some x := hx
  unfold Fl.andThen Fl.must at hx'
  by_cases hb : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true
  · rw [if_pos hb] at hx'
    simp only [Fl.change, Fl.ret] at hx'
    cases hh : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) with
    | none => simp [hh] at hx'
    | some G' =>
      simp only [hh, Option.map_some, Option.some.injEq] at hx'
      subst hx'
      simp only [Prod.mk.injEq] at e
      exact ⟨e.1.symm, hb, by rw [e.2]⟩
  · rw [if_neg hb] at hx'
    simp at hx'

theorem front_some {rows : Bool} {P : Pub} {g : Nat} {o : Own} {rowV rowL : Aff} {l : List Aff}
    (h : front rows P g o rowV rowL = some l) :
    ∃ g2 g46 g7 g89 g10 g11 g12,
      normsForms P o.v o.H = some g2 ∧ rowsForms o.v o.H = some g46 ∧
      termsForms o.v o.H = some g7 ∧ gatedForms P o.v o.hd o.hd2 = some g89 ∧
      oneHotForms o.v = some g10 ∧ planesParts o.v o.H.fo = some g11 ∧
      (if g == 0 then (embeddingForm o.v o.H o.sVE).map ([·]) else some []) = some g12 ∧
      l = (if rows then o.H.fo.rows.toList else []) ++ g2 ++ [rowBatchForm P.y o.H, rowV] ++ g46 ++
        g7 ++ g89 ++ g10 ++ rowL :: g11.2 ++ g12 := by
  unfold front at h
  obtain ⟨g2, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g46, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g7, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g89, a4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g10, a5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨g11, a6, h⟩ := Option.bind_eq_some_iff.mp h
  cases hg : (g == 0) with
  | true =>
    simp only [hg, if_true] at h
    obtain ⟨g12, a7, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨g2, g46, g7, g89, g10, g11, g12, a1, a2, a3, a4, a5, a6, by simpa using a7,
      (Option.some.inj h).symm⟩
  | false =>
    simp only [hg, Bool.false_eq_true, if_false] at h
    obtain ⟨g12, a7, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨g2, g46, g7, g89, g10, g11, g12, a1, a2, a3, a4, a5, a6, by simpa using a7,
      (Option.some.inj h).symm⟩

theorem formsFrontWith_some {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G)) :
    ∃ sh pp l F1 F2,
      ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh ∧
      planesParts o.v o.H.fo = some pp ∧
      front rows P g o (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {})
        (o.H.fo.leaves.rowForm oneE pp.1) = some l ∧
      fs = l.toArray ∧
      F.hideRun o.H.tV.p.first (Array.replicate o.H.tV.p.walk.1.length zeroE)
        (subE zeroE oneE) = some F1 ∧
      F1.hideRun o.H.fo.leaves.first (Array.replicate o.H.fo.leaves.walk.1.length zeroE)
        (subE zeroE oneE) = some F2 ∧
      G = (if rows then F2.paid o.H.fo.owedObjects else F2).paid o.H.fo.owedPlanes := by
  unfold formsFrontWith at h
  obtain ⟨sh, a1, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨rowV, F1⟩, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  dsimp only at h2
  obtain ⟨pp, a3, h3⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨rowL, F2⟩, a4, h4⟩ := Option.bind_eq_some_iff.mp h3
  dsimp only at h4
  obtain ⟨l, a5, h5⟩ := Option.bind_eq_some_iff.mp h4
  obtain ⟨e2, -, r2⟩ := ownClaim_some a2
  obtain ⟨e4, -, r4⟩ := ownClaim_some a4
  have e := Option.some.inj h5
  rw [e2, e4] at a5
  exact ⟨sh, pp, l, F1, F2, a1, a3, a5, (congrArg Prod.fst e).symm, r2, r4,
    (congrArg Prod.snd e).symm⟩

theorem formsBack_some {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsBack o F = some (fs, G)) :
    ∃ F1, fs = (back o (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {})).toArray ∧
      F.hideRun o.wo.toWsMerged.p.first
        (Array.replicate o.wo.toWsMerged.p.walk.1.length zeroE) (subE zeroE oneE) = some F1 ∧
      G = F1.paid o.H.fo.owedJoin := by
  unfold formsBack at h
  obtain ⟨⟨rowM, F1⟩, a1, h1⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h1
  obtain ⟨e1, -, r1⟩ := ownClaim_some a1
  have e := Option.some.inj h1
  rw [e1] at e
  exact ⟨F1, (congrArg Prod.fst e).symm, r1, (congrArg Prod.snd e).symm⟩

/-- Every form of each group is a member of the list. -/
theorem mem_front {rows : Bool} {P : Pub} {g : Nat} {o : Own} {rowV rowL : Aff} {l : List Aff}
    (h : front rows P g o rowV rowL = some l) :
    (∀ g2, normsForms P o.v o.H = some g2 → ∀ f ∈ g2, f ∈ l) ∧
      rowBatchForm P.y o.H ∈ l ∧ rowV ∈ l ∧
      (∀ x, rowsForms o.v o.H = some x → ∀ f ∈ x, f ∈ l) ∧
      (∀ x, termsForms o.v o.H = some x → ∀ f ∈ x, f ∈ l) ∧
      (∀ x, gatedForms P o.v o.hd o.hd2 = some x → ∀ f ∈ x, f ∈ l) ∧
      (∀ x, oneHotForms o.v = some x → ∀ f ∈ x, f ∈ l) ∧
      rowL ∈ l ∧
      (∀ x, planesParts o.v o.H.fo = some x → ∀ f ∈ x.2, f ∈ l) ∧
      (g = 0 → ∀ f, embeddingForm o.v o.H o.sVE = some f → f ∈ l) := by
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := front_some h
  refine ⟨?_, by simp, by simp, ?_, ?_, ?_, ?_, by simp, ?_, ?_⟩
  · intro x hx f hf
    rw [a1] at hx; cases hx; simp [hf]
  · intro x hx f hf
    rw [a2] at hx; cases hx; simp [hf]
  · intro x hx f hf
    rw [a3] at hx; cases hx; simp [hf]
  · intro x hx f hf
    rw [a4] at hx; cases hx; simp [hf]
  · intro x hx f hf
    rw [a5] at hx; cases hx; simp [hf]
  · intro x hx f hf
    rw [a6] at hx; cases hx; simp [hf]
  · intro hg f hf
    subst hg
    rw [hf] at a7
    simp at a7
    subst a7
    simp

end OnBytes.Desc.First.K4
