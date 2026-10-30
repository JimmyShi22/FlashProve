-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
Johnson/Desc/ProofFile/Honest/K3/Key/LookupRecordReadsAsTheSentences.lean: (K-P2) THE TWO TIES between what the honest side's
letters come to at the key's record `hidK` and the sums in machine elements that the table's sentences read. Theorems with
proofs.

  `cornerWeightIsThePairsEntry`: the two texts of a vector of product form are one
  `planesOfTheKeyRecordAreThePlaneSum`: `Spec.planesOf` at the key's record is `planeSum` of the bits, read, where the bits
      read 0 at the planes that are not real
  `keysOfTheKeyRecordAreTheKeySum`: alpha less `keysOfP` at the key's record is the sum over the part's keys of the equality
      weight times alpha less the key, read, at a part of at least one level

By what. `read_planeSum` and `sum_grid` (Johnson/RunOne/Law/TieReadP.lean) for the planes; `read_keySum`
(Johnson/RunOne/Law/TieReadK.lean) and `eqW_eq` (Honest/K3/Parts/KeyFace.lean) for the keys.

Limits. The premise `idle` is paid at the honest array elsewhere (`bitVec_full`, E2E/KeyPlanesRead.lean). A part without a
level has two keys on the left of the last statement and one on the right: hence the premise `positive`.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyMid
import Johnson.RunOne.Law.TieReadP
import Johnson.RunOne.Law.TieReadK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Key
open OnBytes
open OnBytes.Slice (readE)
open OnBytes.Params (WfLookup)
open ProofFile.Honest.K3.Parts
open ProofFile.Honest.K3.Parts.Key
open VerifiableInference.Desc.K3.KeyLaw (pairsF)
open VerifiableInference.Desc.Key (planeSum sumE)

/-- **The two texts of a vector of product form are one.** -/
theorem cornerWeightIsThePairsEntry : ∀ (pairs : List (E × E)) (X : Nat),
    ProofFile.Honest.K3.Law.Spec.cornerW pairs X = Lk6.Mid.pairsAt (pairsF pairs) X
  | [], _ => rfl
  | _ :: pairs, X => by
    show (if X % 2 = 1 then _ else _) * ProofFile.Honest.K3.Law.Spec.cornerW pairs (X / 2) =
      (if X % 2 = 1 then _ else _) * Lk6.Mid.pairsAt (pairsF pairs) (X / 2)
    rw [cornerWeightIsThePairsEntry pairs (X / 2)]

/-- **What the planes come to at the key's record is `planeSum` of the bits, read.** -/
theorem planesOfTheKeyRecordAreThePlaneSum (id : Nat) (m : Wf.Matrix) (l : WfLookup)
    (kvec : Nat → Nat → E) (bvec : Nat → E) (points : Pts) (pairs : List (E × E))
    (planes : 2 ≤ (faceK id m l).planes)
    (idle : ∀ u, u < 2 ^ l.d → ∀ j, (faceK id m l).planes ≤ j → j < 2 ^ l.mu →
      readE (bvec (j + 2 ^ l.mu * u)) = 0) :
    ProofFile.Honest.K3.Law.Spec.planesOf (dataAt (numsK id m l) (hidK l kvec bvec) points) pairs =
      readE (planeSum (faceK id m l) pairs bvec) := by
  rw [Johnson.RunOne.Law.TieReadP.read_planeSum]
  show ∑ X ∈ Finset.range (2 ^ (l.mu + l.d)), ProofFile.Honest.K3.Law.Spec.cornerW pairs X *
      (dataAt (numsK id m l) (hidK l kvec bvec) points).bitAt X = _
  rw [Nat.pow_add, Johnson.RunOne.Law.TieReadP.sum_grid, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j inPlanes => Finset.sum_congr rfl fun t inRows => ?_
  have belowPlanes : j < 2 ^ l.mu := Finset.mem_range.1 inPlanes
  have belowRows : t < 2 ^ l.d := Finset.mem_range.1 inRows
  have row : (j + 2 ^ l.mu * t) / 2 ^ l.mu = t := by
    rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt belowPlanes, Nat.zero_add]
  have place : (j + 2 ^ l.mu * t) % 2 ^ l.mu = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt belowPlanes]
  rw [cornerWeightIsThePairsEntry]
  congr 1
  show (dataAt (numsK id m l) (hidK l kvec bvec) points).bits ((j + 2 ^ l.mu * t) / 2 ^ l.mu)
      ((j + 2 ^ l.mu * t) % 2 ^ l.mu) = _
  rw [row, place]
  by_cases real : j < (faceK id m l).planes
  · exact if_pos (show j < (faceK id m l).planes - 2 + 2 by omega)
  · have zero : readE (bvec (j + 2 ^ (faceK id m l).mu * t)) = 0 :=
      idle t belowRows j (Nat.le_of_not_lt real) belowPlanes
    rw [zero]
    exact if_neg (show ¬ j < (faceK id m l).planes - 2 + 2 by omega)

/-- **Alpha less what a part's keys come to at the key's record is the table's sum, read.** -/
theorem keysOfTheKeyRecordAreTheKeySum (id : Nat) (m : Wf.Matrix) (l : WfLookup)
    (kvec : Nat → Nat → E) (bvec : Nat → E) (points : Pts) (part : Nat)
    (positive : 1 ≤ (faceK id m l).parts.getD part 0) (point : Array E)
    (size : point.size = (faceK id m l).parts.getD part 0) (alpha : E) :
    readE alpha - keysOfP (dataP (numsK id m l) (faceK id m l).parts (faceK id m l).orders
        (hidK l kvec bvec) points) part point =
      readE (sumE (2 ^ (faceK id m l).parts.getD part 0) fun k =>
        mulE ((Tensor.eq point.toList.reverse).entry k) (subE alpha (kvec part k))) := by
  have length : point.toList.reverse.length = (faceK id m l).parts.getD part 0 := by
    rw [List.length_reverse, Array.length_toList, size]
  have sum := Johnson.RunOne.Law.TieReadK.read_keySum alpha point.toList.reverse (kvec part)
    (fun n => readE (kvec part n)) (fun _ _ => rfl)
  rw [length] at sum
  rw [sum]
  congr 1
  show OnBytes.HonestTrace.Look.ext ((faceK id m l).parts.getD part 0 - 1 + 1)
    (fun x => readE (kvec part x)) (byBit point) = _
  rw [Nat.sub_add_cancel positive]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [eqW_eq]
  rfl

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.cornerWeightIsThePairsEntry
#print axioms ProofFile.Honest.K3.Key.planesOfTheKeyRecordAreThePlaneSum
#print axioms ProofFile.Honest.K3.Key.keysOfTheKeyRecordAreTheKeySum
