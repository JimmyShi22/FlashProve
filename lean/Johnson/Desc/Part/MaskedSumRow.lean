-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumRow.lean: THE PART "THE MASKED SUMCHECK": THE ROW OF AN HONEST RUN IS
WORTH 0 IN EVERY WORLD THAT FITS. Statements and proofs, in the part's letters.
WHAT IT DOES NOT SHOW. That there is such a world; that a kind's end term makes up its summand; that
the hearing returns (Part/MaskedSumReturns.lean). Nothing on soundness, probabilities or hiding.
WHAT IT IS. Part/MaskedSumMember.lean's run_of_chain takes the world, the end term and the kept form
IN FRONT of the rounds. A kind's world is read off the ledger BEHIND its rounds. Here the value of
the row stands alone, of any record of the hearing's make:
  rowForm_value   the value of rowForm (Part/MaskedSumMore.lean), as row_value has it for row.
  rowForm_zero    a record whose variables and challenges are a Lens's, whose claim reads as the
                  masked summand at the challenges (hid + eps S + eps (T - sigma) psiProd), in a
                  world that gives the start form sigma and the own slots the hiding coefficients,
                  with an end term and a kept form that make up the summand: rowForm is worth 0.

-/
import Johnson.Desc.Part.MaskedSumMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

theorem rowForm_value (W : World K) (h : Heard) (S0 : E) (kept : Aff) :
    (rowForm h S0 kept).value ρ W =
      dotFrom ρ (fun i => W.slot (h.first + i)) (hidingAt (h.vars.zip h.r)).1 +
        ρ.val h.eps * ρ.val (hidingAt (h.vars.zip h.r)).2 *
          (ρ.val h.target - h.start.value ρ W) +
        ρ.val h.eps * kept.value ρ W - (ρ.val h.claim - ρ.val h.eps * ρ.val S0) := by
  unfold rowForm
  simp only [Aff.value_addMul, onSlots_value, Aff.value_sub, Aff.value_ofConst, ρ.sub, ρ.mul,
    ρ.zero]
  ring

/-- **THE ROW OF AN HONEST RUN IS WORTH 0.** -/
theorem rowForm_zero (vs : List Var) (hcoef : ℕ → K) (S : List K → K) (sigma : K) (W : World K)
    (h : Heard) (l : List (List E × E)) (S0 : E) (kept : Aff) (hvars : h.vars = vs)
    (hlens : Lens vs l) (hr : h.r = l.map (·.2))
    (hclaim : ρ.val h.claim =
      hid (vs.map (Var.wt ρ)) hcoef (h.r.map ρ.val) + ρ.val h.eps * S (h.r.map ρ.val) +
        ρ.val h.eps * (ρ.val h.target - sigma) * psiProd (vs.map (Var.wt ρ)) (h.r.map ρ.val))
    (hC : h.start.value ρ W = sigma)
    (hslots : ∀ i, i < ownSlots vs → W.slot (h.first + i) = hcoef i)
    (hend : S (h.r.map ρ.val) = ρ.val S0 + kept.value ρ W) :
    (rowForm h S0 kept).value ρ W = 0 := by
  have hle := hidingAt_length_le (h.vars.zip h.r)
  rw [hvars, hr, zip_fst _ l hlens] at hle
  obtain ⟨hu1, hu2⟩ := hidingAt_val ρ (h.vars.zip h.r) hcoef
  have e1 : (h.vars.zip h.r).map (fun x => x.1.wt ρ) = vs.map (Var.wt ρ) := by
    rw [hvars, hr]
    exact zip_wt ρ _ l hlens
  have e2 : (h.vars.zip h.r).map (fun x => ρ.val x.2) = h.r.map ρ.val := by
    rw [hvars, hr]
    exact zip_val ρ _ l hlens
  rw [e1, e2] at hu1 hu2
  have hdot : dotFrom ρ (fun i => W.slot (h.first + i)) (hidingAt (h.vars.zip h.r)).1 =
      dotFrom ρ hcoef (hidingAt (h.vars.zip h.r)).1 :=
    dotFrom_congr ρ _ _ _ fun i hi => hslots i (by
      rw [hvars, hr] at hi
      omega)
  rw [rowForm_value, hdot, hu1, hu2, hclaim, hC]
  linear_combination (-(ρ.val h.eps)) * hend

end VerifiableInference.Desc.Part.MaskedSum

end
