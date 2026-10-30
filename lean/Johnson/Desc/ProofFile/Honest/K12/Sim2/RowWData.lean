-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: what W's data reads of a front.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowWData.lean: the data of W's sending (wJob, E2E/KeySendJobs.lean)
reads of a front the challenges heard alone, and of these only the ones that the batching's numbers name
and that the letter points reads. So trees_at_plain_job's hdata holds at wJob where these lie in front of
W's sender.

  elemAt_take, wWeights_reads, wJob_data_reads

Limits. hp, hs, he, hf are premises on the letters points and a: not paid here. Nothing on completeness,
soundness or hiding.
-/
import E2E.KeySendJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open AtPublicFiles.Key (elemAt BattAt wWeights wJob)
open OnBytes OnBytes.Params
open OnBytes.Slice (GF GE)
open ProofFile.Honest (Front)
open ProofFile.Honest.K1 (SendJob Ride)
open VerifiableInference.Desc.Key (Pieces)

theorem elemAt_take (h h' : List Fmt.Drawn) (N i : ℕ) (e : h.take N = h'.take N) (hi : i < N) :
    elemAt h i = elemAt h' i := by
  unfold elemAt
  have g : h[i]? = h'[i]? := by
    rw [← List.getElem?_take_of_lt hi (l := h), e, List.getElem?_take_of_lt hi]
  rw [g]

theorem wWeights_reads (one : OneTime) (points : List Fmt.Drawn → ℕ → ℕ → List E) (a : BattAt) (N : ℕ)
    (hp : ∀ h h' : List Fmt.Drawn, h.take N = h'.take N → points h = points h')
    (hs : a.sigma < N) (he : a.eps < N) (hf : a.first + (Wf.matrixOf one.lin).kCol ≤ N)
    (h h' : List Fmt.Drawn) (e : h.take N = h'.take N) :
    wWeights one points a h = wWeights one points a h' := by
  unfold wWeights
  rw [hp h h' e, elemAt_take h h' N _ e hs, elemAt_take h h' N _ e he]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  exact elemAt_take h h' N _ e (by have := List.mem_range.1 hi; omega)

/-- **hdata at wJob.** -/
theorem wJob_data_reads {W X : Type} (entry : W → ℕ → ℕ → GF) (one : OneTime) (Np : Pieces)
    (groups : List (List ℕ)) (first : ℕ) (ride : ℕ → Option Ride)
    (points : List Fmt.Drawn → ℕ → ℕ → List E) (a : BattAt) (J : SendJob W X)
    (hJ : wJob entry one Np groups first ride points a = some J) (N : ℕ)
    (hp : ∀ h h' : List Fmt.Drawn, h.take N = h'.take N → points h = points h')
    (hs : a.sigma < N) (he : a.eps < N) (hf : a.first + (Wf.matrixOf one.lin).kCol ≤ N)
    (w : W) (fr fr' : Front X) (e : fr.heard.take N = fr'.heard.take N) :
    J.data w fr = J.data w fr' := by
  unfold wJob at hJ
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hJ
  have e2 := wWeights_reads one points a N hp hs he hf _ _ e
  dsimp only
  rw [e2]

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.elemAt_take
#print axioms ProofFile.Honest.K12.Sim2.wWeights_reads
#print axioms ProofFile.Honest.K12.Sim2.wJob_data_reads
