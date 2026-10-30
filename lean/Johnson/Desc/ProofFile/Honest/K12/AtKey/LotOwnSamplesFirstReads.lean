-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnSamplesFirstReads.lean: CAN `SendersReadInFront` (LotOwnWords.lean) BE MET: its two
fields on the sendings' data, at the library's own written jobs `idxJob` and `wJob` (E2E/KeySendJobs.lean).

  `elemAt_of_front`           a challenge's first element, below j, is read off the first j challenges
  `wWeights_of_front`         the weights that the batching passes on, the same
  `idxJob_reads_in_front`     `idxJob`: its data reads nothing of the front: at every j, no premise
  `WeightsReadInFront`        what `wJob`'s letters must meet: the three numbers lie below j; `points` reads the first j
  `wJob_reads_in_front`       `wJob`: under that
  `elemAt_beyond_front`       A CONTROL THAT SAYS NO: `elemAt_of_front`'s bound i < j cannot be dropped

Limits.
- No value of `KeyParts` is named: that a prover's K.idx, K.w are these jobs is the caller's.
- `WeightsReadInFront` is shown of no letters.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeySendJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open OnBytes.Params (OneTime)
open VerifiableInference.Desc.Key (Pieces)
open ProofFile.Honest.K1 (SendJob Ride)
open AtPublicFiles.Key (elemAt BattAt wWeights idxJob wJob)

variable {W X : Type}

/-- A challenge's first element, below j, is read off the first j challenges. -/
theorem elemAt_of_front {h h' : List Fmt.Drawn} {j : ℕ} (e : h.take j = h'.take j) {i : ℕ}
    (hi : i < j) : elemAt h i = elemAt h' i := by
  have g : h[i]? = h'[i]? := by
    rw [← List.getElem?_take_of_lt hi, e, List.getElem?_take_of_lt hi]
  unfold elemAt
  rw [g]

/-- **What `wJob`'s letters must meet**, at j challenges in front of W's sending. -/
structure WeightsReadInFront (one : OneTime) (points : List Fmt.Drawn → ℕ → ℕ → List OnBytes.E)
    (a : BattAt) (j : ℕ) : Prop where
  sigma : a.sigma < j
  eps : a.eps < j
  columns : a.first + (OnBytes.Wf.matrixOf one.lin).kCol ≤ j
  points : ∀ h h' : List Fmt.Drawn, h.take j = h'.take j → points h = points h'

/-- The weights that the batching passes on are read off the first j challenges. -/
theorem wWeights_of_front {one : OneTime} {points : List Fmt.Drawn → ℕ → ℕ → List OnBytes.E}
    {a : BattAt} {j : ℕ} (H : WeightsReadInFront one points a j) {h h' : List Fmt.Drawn}
    (e : h.take j = h'.take j) : wWeights one points a h = wWeights one points a h' := by
  unfold wWeights
  rw [H.points h h' e, elemAt_of_front e H.sigma, elemAt_of_front e H.eps]
  congr 1
  refine List.map_congr_left fun i hi => elemAt_of_front e ?_
  have := List.mem_range.1 hi
  have := H.columns
  omega

/-- **`idxJob`: its data reads nothing of the front.** -/
theorem idxJob_reads_in_front (one : OneTime) (N : Pieces) (groups : List (List ℕ)) (first j : ℕ) :
    ∀ x (fr fr' : Front X), fr.heard.take j = fr'.heard.take j →
      (idxJob (W := W) (X := X) one N groups first).data x fr =
        (idxJob (W := W) (X := X) one N groups first).data x fr' :=
  fun _ _ _ _ => rfl

/-- **`wJob`: its data reads of the front the first j challenges alone**, under `WeightsReadInFront`. -/
theorem wJob_reads_in_front (entry : W → ℕ → ℕ → OnBytes.Slice.GF) (one : OneTime) (N : Pieces)
    (groups : List (List ℕ)) (first : ℕ) (ride : ℕ → Option Ride)
    (points : List Fmt.Drawn → ℕ → ℕ → List OnBytes.E) (a : BattAt) (j : ℕ)
    (H : WeightsReadInFront one points a j) {J : SendJob W X}
    (hJ : wJob entry one N groups first ride points a = some J) :
    ∀ x (fr fr' : Front X), fr.heard.take j = fr'.heard.take j → J.data x fr = J.data x fr' := by
  intro x fr fr' e
  unfold wJob at hJ
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hJ
  funext m r c
  show (if m = 0 then _ else _) = (if m = 0 then _ else _)
  rw [wWeights_of_front H e]

/-- **A control that says no**: at a number that is not below j the two lists can differ there. -/
theorem elemAt_beyond_front :
    ∃ (h h' : List Fmt.Drawn), h.take 0 = h'.take 0 ∧ elemAt h 0 ≠ elemAt h' 0 := by
  refine ⟨[⟨[(1, 0, 0)], [], [], none⟩], [], rfl, ?_⟩
  decide

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.elemAt_of_front
#print axioms ProofFile.Honest.K12.AtKey.WeightsReadInFront
#print axioms ProofFile.Honest.K12.AtKey.wWeights_of_front
#print axioms ProofFile.Honest.K12.AtKey.idxJob_reads_in_front
#print axioms ProofFile.Honest.K12.AtKey.wJob_reads_in_front
#print axioms ProofFile.Honest.K12.AtKey.elemAt_beyond_front
