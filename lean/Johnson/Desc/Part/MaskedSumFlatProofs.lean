-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumFlatProofs.lean: THE PART "THE MASKED SUMCHECK": ITS TEXT AND THE FLAT
TEXT TIED: the proofs of the five statements of Johnson/Desc/Part/MaskedSumFlat.lean, to the letter.

  `flatWeight`, `flatWeights`   by the flat text's maker of a weight, which has two arms
  `flatEnded`                   by the fields of `Ended` and `after_read`
  `flat_rowForm`                the part's two texts of the row's form are one
  `flat_walk`                   at the same letters the flat record's walk is `verify-on-bytes`'s at
                                the part's variables and challenges
  `flatRowTie`                  by `Psc.rowForm_value`, `rowAff_value`, `hidingAt_read`
  `flat_pscRow`, `flat_row`     each text's row is one run of layings, and what it hands back
  `flatRowLaid`                 by these two; the two runs are as long by `hidingAt_read`

Limits. Those of the statements' file. Nothing on soundness, on an honest prover or on any property.

-/
import Johnson.Desc.Part.MaskedSumFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes (E addE mulE subE zeroE oneE)
open OnBytes.Model (Reading World Aff Fork Psc RoundForm)
open OnBytes.Model.Road (Ended)
open OnBytes.K.Kc (Fl Tape weightT atPointT valuesT)

theorem flatWeight : FlatWeight := by
  intro form z d w h
  unfold weightT at h
  split at h
  · have h' := Option.some.inj h
    subst h'
    by_cases hp : atPointT form = true
    · exact ⟨.point z (valuesT form d + 1), by simp [hp, Var.weight]⟩
    · exact ⟨.plain (valuesT form d + 1), by simp [hp, Var.weight]⟩
  · exact absurd h (by simp)

theorem flatWeights : FlatWeights := by
  intro ws
  induction ws with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons w ws ih =>
    intro h
    obtain ⟨form, z, d, hw⟩ := h w List.mem_cons_self
    obtain ⟨v, hv⟩ := flatWeight form z d w hw
    obtain ⟨vs, hvs⟩ := ih fun w' hw' => h w' (List.mem_cons_of_mem _ hw')
    exact ⟨v :: vs, by rw [List.map_cons, ← hv, ← hvs]⟩

theorem flatEnded : FlatEnded := by
  intro p C τ mu eps first vs rs dY sentY beta hE hL
  have hw : (vs ++ [Var.point zeroE (dY + 1)]).map Var.weight =
      vs.map Var.weight ++ [OnBytes.Psc.Weight.atZero (dY + 1)] := by
    rw [List.map_append]
    rfl
  refine ⟨hE.start, hE.target, hE.eps, hE.first, ?_, hE.r, ?_⟩
  · rw [hE.vars]
    exact hw.symm
  · intro K _ ρ
    rw [hE.claim, ← hw]
    exact (after_read ρ _ _ _ _ hL rfl).symm

/-- The part's two texts of the row's form are one. -/
theorem flat_rowForm (h : Heard) (S0 : E) (kept : Aff) : rowForm h S0 kept = rowAff h S0 kept := rfl

/-- At the same letters the flat record's walk is `verify-on-bytes`'s at the part's variables and
challenges. -/
theorem flat_walk {p : Psc} {h : Heard} (hS : SameLetters p h) :
    p.walk = OnBytes.Psc.hidingWalk ((h.vars.zip h.r).map asW) := by
  unfold Psc.walk
  rw [OnBytes.zipT_eq, hS.vars, hS.r, zip_weight]

theorem flatRowTie : FlatRowTie := by
  intro K _ ρ W p h S0 kept hS
  obtain ⟨a1, a2⟩ := hidingAt_read ρ (h.vars.zip h.r)
  rw [flat_rowForm, rowAff_value, Psc.rowForm_value, flat_walk hS, sumFrom_congr ρ W _ _ _ a1, a2,
    hS.first, hS.eps, hS.target, hS.start, hS.claim K ρ]

/-- Where its test passes, the flat text's row is one run of layings. -/
theorem flat_pscRow {p : Psc} (S0 : E) (kept : Aff) (F : Fork) (t : Tape)
    (hm : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true) :
    Fl.pscRow p S0 kept F t =
      (F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)).map fun G =>
        ((p.rowForm S0 kept, { p with rowMade := true }), G, t) := by
  unfold Fl.pscRow
  show Fl.andThen (Fl.must _) _ F t = _
  unfold Fl.andThen Fl.must
  rw [hm]
  show Fl.andThen (Fl.change _) _ F t = _
  unfold Fl.andThen Fl.change
  cases hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) with
  | none =>
    simp only [hG, Option.map_none]
  | some G =>
    simp only [hG, Option.map_some]
    rfl

/-- The part's row is one run of layings. -/
theorem flat_row (h : Heard) (S0 : E) (kept : Aff) (F : Fork) :
    row h S0 kept F =
      (F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
        (subE zeroE oneE)).map fun G => (rowAff h S0 kept, G) := by
  unfold row
  cases ho : F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
      (subE zeroE oneE) with
  | none => simp [ho]
  | some G =>
    simp only [ho, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some]
    rfl

theorem flatRowLaid : FlatRowLaid := by
  intro p h S0 kept F G t hS h1 h2 h3 h4
  have hlen : p.walk.1.length = (hidingAt (h.vars.zip h.r)).1.length := by
    have a1 := congrArg List.length (hidingAt_read Reading.gl (h.vars.zip h.r)).1
    rw [List.length_map, List.length_map] at a1
    rw [flat_walk hS, a1]
  have hm : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true := by
    simp [h1, h2, h3, h4]
  rw [flat_pscRow S0 kept F t hm, flat_row, flat_rowForm, hS.first, hlen]
  cases F.hideRun h.first (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE)
      (subE zeroE oneE) with
  | none => simp
  | some G' => simp

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.flatWeight
#print axioms VerifiableInference.Desc.Part.MaskedSum.flatWeights
#print axioms VerifiableInference.Desc.Part.MaskedSum.flatEnded
#print axioms VerifiableInference.Desc.Part.MaskedSum.flatRowTie
#print axioms VerifiableInference.Desc.Part.MaskedSum.flatRowLaid
#print axioms VerifiableInference.Desc.Part.MaskedSum.flat_rowForm
#print axioms VerifiableInference.Desc.Part.MaskedSum.flat_walk
#print axioms VerifiableInference.Desc.Part.MaskedSum.flat_pscRow
#print axioms VerifiableInference.Desc.Part.MaskedSum.flat_row
