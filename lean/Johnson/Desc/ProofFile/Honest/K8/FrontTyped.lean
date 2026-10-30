-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontTyped.lean: THE SMALLNESS TEST: THE TEST `allLive`
(Johnson/Desc/ProofFile/Honest/K8/FrontCount.lean) ON DATA THAT HOLD THE SEQUENCE OF A TYPED MATRIX
IS THE TYPED EVENT OF Johnson/Desc/K8/Honest/DeadColumn.lean. Statements and proofs. No state, no
prover. LEMMAS; NONE OF THE LIBRARY's GOALS. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR
HIDING.

  `TypedAt sz β tl`   the data tl hold the sequence that the typed matrix β stands for, each
      matrix's first column, and the sizes sz: matrices, columns, combinations
  **`allLive_iff`**   then `allLive tl` says no just if some column of β is all 0
  `cols_eq`           and `cols tl` is the sizes' number of columns
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontCount
import Johnson.Desc.K8.Honest.DeadColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference.Desc.First.K8.Honest

/-- The data hold the typed matrix's sequence and the sizes. -/
structure TypedAt (sz : Size) (β : Dr sz) (tl : HTailF2) : Prop where
  cfF : tl.cfF = listOf β
  tau : tl.tau = sz.tau
  NM : tl.NM = sz.NM
  first : ∀ μ : Fin sz.NM, tl.cfFirst.getD μ.val 0 = firstCol sz μ
  k : ∀ μ : Fin sz.NM, (tl.mats.getD μ.val {}).k = sz.k μ

/-- **The test says no just if some column of the typed matrix is all 0.** -/
theorem allLive_iff {sz : Size} {β : Dr sz} {tl : HTailF2} (h : TypedAt sz β tl) :
    allLive tl = false ↔ ∃ (μ : Fin sz.NM) (c : Fin (sz.k μ)), ∀ u, (β μ u c).val = 0 := by
  constructor
  · intro hf
    by_contra hne
    have ht : allLive tl = true := by
      simp only [allLive, List.all_eq_true, List.mem_range]
      intro mu hmu c hc
      by_contra hl
      have hl' : columnLive tl mu c = false := by simpa using hl
      rw [h.NM] at hmu
      have e : (tl.mats.getD mu {}).k = sz.k mu := h.k ⟨mu, hmu⟩
      have hc' : c < sz.k mu := by omega
      exact hne ⟨⟨mu, hmu⟩, ⟨c, hc'⟩,
        (live_iff sz β tl ⟨mu, hmu⟩ ⟨c, hc'⟩ h.cfF h.tau (h.first _)).1 hl'⟩
    rw [ht] at hf
    cases hf
  · rintro ⟨μ, c, hz⟩
    have hl := (live_iff sz β tl μ c h.cfF h.tau (h.first μ)).2 hz
    by_contra hne
    have ht : allLive tl = true := by simpa using hne
    simp only [allLive, List.all_eq_true, List.mem_range] at ht
    have h2 := ht μ.val (by rw [h.NM]; exact μ.isLt) c.val (by rw [h.k μ]; exact c.isLt)
    rw [hl] at h2
    cases h2

theorem cols_eq {sz : Size} {β : Dr sz} {tl : HTailF2} (h : TypedAt sz β tl) :
    cols tl = sz.columns := by
  unfold cols Size.columns
  rw [h.NM, Finset.sum_range]
  exact Finset.sum_congr rfl fun μ _ => h.k μ

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.allLive_iff
#print axioms ProofFile.Honest.K8.cols_eq
#print axioms ProofFile.Honest.K8.TypedAt
