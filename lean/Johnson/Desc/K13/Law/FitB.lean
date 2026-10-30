-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FitB.lean: the rounds of the batching's sumcheck, read: the library's loop on
the short transcript gives the reading of the verifier's running claim, and the point of challenges.
Lemmas with their proofs.
Main names:
  `wsOf k`: the verifier's weights: k times `Psc.Weight.plain 3`. `vOf`: the library's loop `vFin`.
  `vOf_fin`: its last value is the reading of `Psc.claimAfter`.
  `vOf_pt`: its point is the reading of the challenges.
  `vOf_match`: weights and challenges match the library's variables and point (`Match`).
Used of `verify-on-bytes`, pure functions and lemmas on them: `Psc.Weight.plain`,
`Psc.claimAfter`, `Psc.polyAt`, `Psc.Weight.complete`; `fit_plain`
(OnBytes/Tie/Pv/Psc/PscFit.lean), `step_read` (OnBytes/Tie/Pv/Psc/PscTie.lean), `Match`
(OnBytes/Tie/Pv/Psc/StepWalk.lean).

What is not claimed. The statements ask that there are k rounds, each with two coefficients sent.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.FitA
import OnBytes.Tie.Pv.Psc.PscTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.L5.Layers (rd sRounds Fit1 fit_plain step_read)
open OnBytes.Road.Hd (Match)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The weights of the batching's sumcheck. -/
abbrev wsOf (k : ℕ) : List Psc.Weight := List.replicate k (Psc.Weight.plain 3)

/-- The library's loop at the short transcript. -/
noncomputable abbrev vOf (k : ℕ) (σ : K) (rs : List (List E × E)) : K × PPt (fmtOf K k) :=
  TWhole.vFin (fmtOf K k) (pdPlains K 2 k) (Cb.Pv.BattShort.fix1 (varsOf K k)) σ (trRounds ρ k rs)

/-- The last value is the reading of the verifier's running claim. -/
theorem vOf_fin : ∀ (k : ℕ) (rs : List (List E × E)) (c0 : E), rs.length = k →
    (∀ p ∈ rs, p.1.length = 2) →
    (vOf ρ k (ρ.val c0) rs).1 = ρ.val (Psc.claimAfter (wsOf k) rs c0)
  | 0, [], _, _, _ => rfl
  | k + 1, (q, g) :: rs, c0, hl, h2 => by
    have e := step_read ρ (fit_plain ρ 1) q c0 g (h2 (q, g) List.mem_cons_self)
    have ih := vOf_fin k rs (Psc.polyAt ((Psc.Weight.plain 3).complete q c0) g)
      (by simpa using hl) (fun p hp => h2 p (List.mem_cons_of_mem _ hp))
    rw [e] at ih
    exact ih
  | 0, _ :: _, _, hl, _ => by simp at hl
  | _ + 1, [], _, hl, _ => by simp at hl

/-- The point is the reading of the challenges. -/
theorem vOf_pt : ∀ (k : ℕ) (rs : List (List E × E)) (σ : K), rs.length = k →
    hFnOf (pfCube K 2) k (pdPlains K 2 k) (pH (fmtOf K k) (pdPlains K 2 k) (vOf ρ k σ rs).2) =
      rd ρ k (rs.map (·.2))
  | 0, [], _, _ => funext fun i => i.elim0
  | k + 1, (q, g) :: rs, σ, hl => by
    rw [List.map_cons, rd_cons]
    exact congrArg (fun f : Fin k → K => (Fin.cons (ρ.val g) f : Fin (k + 1) → K))
      (vOf_pt k rs _ (by simpa using hl))
  | 0, _ :: _, _, hl => by simp at hl
  | _ + 1, [], _, hl => by simp at hl

/-- The weights with the challenges match the library's variables and point. -/
theorem vOf_match : ∀ (k : ℕ) (rs : List (List E × E)) (σ : K), rs.length = k →
    Match ρ ((wsOf k).zip (rs.map (·.2))) (varsOf K k)
      (pH (fmtOf K k) (pdPlains K 2 k) (vOf ρ k σ rs).2)
  | 0, [], _, _ => trivial
  | k + 1, (q, g) :: rs, σ, hl =>
    ⟨(fit_plain ρ 1).len.symm, (fit_plain ρ 1).plen, fun i => (congrFun (fit_plain ρ 1).psi i).symm,
      rfl, vOf_match k rs _ (by simpa using hl)⟩
  | 0, _ :: _, _, hl => by simp at hl
  | _ + 1, [], _, hl => by simp at hl

end VerifiableInference.Desc.K13.Law
