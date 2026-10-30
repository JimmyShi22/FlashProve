-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WorthGroups.lean: CONDITIONAL: "every form that K4's two runs leave is worth 0", cut
into the format's groups of claims. Two definitions of hypotheses, their fields in the groups'
order, at a FREE world W; and the two statements that these fields give the worth of every form of a
run's list. By the library's equations on the two lists (`front_some`, `formsFrontWith_some`,
`formsBack_some`, OnBytes/Desc/First/K4/ClaimsLaws.lean).

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: every field is a hypothesis. Nothing on soundness,
on completeness or on any other property.

  `FrontWorth W P g o sh pp`   TEN FIELDS, in the order of the run "front" without the format's
      group 1 (the lookup's claims on its objects): groups 2 to 12. sh: the end values of the token
      sumcheck on the row products, as shown. pp: the lookup's parts on its planes.
      * norms (group 2) · batch, rowV (group 3: the row products' batch; that sumcheck's own claim)
      * rows (groups 4 to 6) · terms (7) · gated (8, 9) · hot (10)
      * rowL, planes (11: the own claim of the lookup's sumcheck over its leaves; two on its planes)
      * emb (12: in the first group alone)
  `BackWorth W o`   FOUR FIELDS, the run "back" (groups 14 and 15): stack (the batched sumcheck's
      own claim) · sideA, sideB (its two sides' end values) · merge (the merge's own claim).
  `front_worth`: where "front" returns a list, FrontWorth at what it has read gives the worth 0 of
      every form of the list.
  `back_worth`: the like for "back".
No property is claimed.
-/
import OnBytes.Desc.First.K4.ClaimsLaws
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Desc.First.K4 (normsForms rowBatchForm rowsForms termsForms gatedForms oneHotForms
  planesParts embeddingForm rowsSummand formsFrontWith formsBack front_some formsFrontWith_some
  formsBack_some back)

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- **The worths of the run "front", group by group.** A hypothesis's form. Nothing is claimed by
the definition. -/
structure FrontWorth (P : Pub) (g : Nat) (o : Own) (sh : Array E) (pp : Aff × List Aff) : Prop where
  norms : ∀ x, normsForms P o.v o.H = some x → ∀ f ∈ x, f.value ρ W = 0
  batch : (rowBatchForm P.y o.H).value ρ W = 0
  rowV : (o.H.tV.p.rowForm (rowsSummand P.y o.H sh) {}).value ρ W = 0
  rows : ∀ x, rowsForms o.v o.H = some x → ∀ f ∈ x, f.value ρ W = 0
  terms : ∀ x, termsForms o.v o.H = some x → ∀ f ∈ x, f.value ρ W = 0
  gated : ∀ x, gatedForms P o.v o.hd o.hd2 = some x → ∀ f ∈ x, f.value ρ W = 0
  hot : ∀ x, oneHotForms o.v = some x → ∀ f ∈ x, f.value ρ W = 0
  rowL : (o.H.fo.leaves.rowForm oneE pp.1).value ρ W = 0
  planes : ∀ f ∈ pp.2, f.value ρ W = 0
  emb : (g == 0) = true → ∀ f, embeddingForm o.v o.H o.sVE = some f → f.value ρ W = 0

/-- **The worths of the run "back".** A hypothesis's form. Nothing is claimed by the definition. -/
structure BackWorth (o : Own) : Prop where
  stack : o.K.rowS.value ρ W = 0
  sideA : (Aff.slot o.K.sA0 - o.K.fin.Alin).value ρ W = 0
  sideB : (Aff.slot o.K.sB0 - o.K.fin.Blin).value ρ W = 0
  merge : (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}).value ρ W = 0

/-- **Every form of "front"'s list is worth 0**, from the groups. -/
theorem front_worth {P : Pub} {g : Nat} {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsFrontWith false P g o F = some (fs, G))
    (hw : ∀ sh pp, ((Array.range (4 * P.y.NI)).mapM fun i => F.shown (o.H.tV.sEnd + i)) = some sh →
      planesParts o.v o.H.fo = some pp → FrontWorth ρ W P g o sh pp) :
    ∀ f ∈ fs.toList, f.value ρ W = 0 := by
  obtain ⟨sh, pp, l, _, _, hsh, hpp, hl, rfl, _, _, _⟩ := formsFrontWith_some h
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := front_some hl
  have Wd := hw sh pp hsh hpp
  obtain rfl : g11 = pp := Option.some.inj (a6.symm.trans hpp)
  intro f hf
  rw [List.toList_toArray] at hf
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with ((((((hf | hf | hf) | hf) | hf) | hf) | hf) | hf | hf) | hf
  · exact Wd.norms g2 a1 f hf
  · rw [hf]; exact Wd.batch
  · rw [hf]; exact Wd.rowV
  · exact Wd.rows g46 a2 f hf
  · exact Wd.terms g7 a3 f hf
  · exact Wd.gated g89 a4 f hf
  · exact Wd.hot g10 a5 f hf
  · rw [hf]; exact Wd.rowL
  · exact Wd.planes f hf
  · cases hg : (g == 0) with
    | true =>
      rw [hg, if_pos rfl] at a7
      obtain ⟨f', e1, e2⟩ := Option.map_eq_some_iff.mp a7
      rw [← e2] at hf
      obtain rfl := List.mem_singleton.1 hf
      exact Wd.emb hg f e1
    | false =>
      rw [hg, if_neg (by decide)] at a7
      rw [← Option.some.inj a7] at hf
      cases hf

/-- **Every form of "back"'s list is worth 0**, from its four. -/
theorem back_worth {o : Own} {F G : Fork} {fs : Array Aff} (h : formsBack o F = some (fs, G))
    (Wd : BackWorth ρ W o) : ∀ f ∈ fs.toList, f.value ρ W = 0 := by
  obtain ⟨_, rfl, _, _⟩ := formsBack_some h
  intro f hf
  rw [List.toList_toArray] at hf
  simp only [back, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with hf | hf | hf | hf
  · rw [hf]; exact Wd.stack
  · rw [hf]; exact Wd.sideA
  · rw [hf]; exact Wd.sideB
  · rw [hf]; exact Wd.merge

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.front_worth
#print axioms OnBytes.Road.K4.back_worth
