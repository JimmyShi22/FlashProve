-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Deterministic.lean: from an algorithm of the library (`ZKCP.OComp 256`) to a
deterministic algorithm of VerifiableInference/RandomOracleModel.lean.
An algorithm that samples no randomness is one deterministic algorithm, with the same queries
(`toUpload_deterministicOf`).
An algorithm whose result under a hash function is a single value has a deterministic algorithm with
that value under that hash function (`evaluate_deterministicOf`).
The bound on the number of queries is kept (`queryBound_deterministicOf`).
-/
import VerifiableInference.Bridge
import ZKCP.Main

set_option autoImplicit false

namespace VerifiableInference

/-- The deterministic algorithm that makes the queries of `algorithm` and continues with the number
0 wherever `algorithm` samples a number. -/
def deterministicOf {α : Type} : ZKCP.OComp 256 α → DeterministicAlgorithm α
  | .pure result => .done result
  | .query input next => .query input fun answer => deterministicOf (next answer)
  | .sample _ next => deterministicOf (next 0)

/-- An algorithm that samples no randomness equals its deterministic algorithm, taken back to the
library's type (`toRandomized.toUpload`). -/
theorem toUpload_deterministicOf {α : Type} : ∀ algorithm : ZKCP.OComp 256 α, algorithm.DrawsNoCoin
    →
    (deterministicOf algorithm).toRandomized.toUpload = algorithm
  | .pure _, _ => rfl
  | .query input next, h => by
      show ZKCP.OComp.query input (fun answer =>
          (deterministicOf (next answer)).toRandomized.toUpload) = ZKCP.OComp.query input next
      exact congrArg _ (funext fun answer => toUpload_deterministicOf (next answer) (h answer))
  | .sample _ _, h => h.elim

/-- A distribution whose support is contained in one point is the point mass there. -/
theorem eq_pure_of_support_subset {α : Type} (distribution : PMF α) (value : α)
    (h : distribution.support ⊆ {value}) :
    distribution = PMF.pure value := by
  have hs : distribution.support = {value} :=
      (Set.Nonempty.subset_singleton_iff distribution.support_nonempty).1 h
  ext a
  rw [PMF.pure_apply]
  split_ifs with ha
  · subst ha
    exact (distribution.apply_eq_one_iff a).2 hs
  · exact (distribution.apply_eq_zero_iff a).2 (by rw [hs]; exact ha)

/-- If the result of `algorithm` under `hash` is `value` with probability 1, its deterministic
algorithm evaluates to `value`. -/
theorem evaluate_deterministicOf {α : Type} (hash : Hash) : ∀ (algorithm : ZKCP.OComp 256 α)
    (value : α),
    algorithm.run hash = PMF.pure value → (deterministicOf algorithm).evaluate hash = value
  | .pure result, value, h => by
      have hm : result ∈ (PMF.pure value).support := by
        rw [← h]
        exact (PMF.mem_support_pure_iff result result).2 rfl
      exact (PMF.mem_support_pure_iff value result).1 hm
  | .query input next, value, h => evaluate_deterministicOf hash (next (hash input)) value h
  | .sample bound next, value, h => by
      refine evaluate_deterministicOf hash (next 0) value
          (eq_pure_of_support_subset _ value fun a ha => ?_)
      have hm : a ∈ ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).run
          hash).support :=
        (PMF.mem_support_bind_iff _ _ a).2 ⟨0, PMF.mem_support_uniformOfFintype 0, ha⟩
      have hm' : a ∈ (PMF.pure value).support := by
        rw [← h]
        exact hm
      exact Set.mem_singleton_iff.2 ((PMF.mem_support_pure_iff value a).1 hm')

/-- `evaluate_deterministicOf` for `toRandomized`, the algorithm as a step of an experiment. -/
theorem run_deterministicOf {α : Type} (hash : Hash) (algorithm : ZKCP.OComp 256 α) (value : α)
    (h : algorithm.run hash = PMF.pure value) :
    (deterministicOf algorithm).toRandomized.run hash = PMF.pure value := by
  rw [DeterministicAlgorithm.run_toRandomized, evaluate_deterministicOf hash algorithm value h]

/-- The deterministic algorithm makes at most as many queries. -/
theorem queryBound_deterministicOf {α : Type} : ∀ (algorithm : ZKCP.OComp 256 α) (queries : ℕ),
    algorithm.QueryBound queries →
    (deterministicOf algorithm).toRandomized.QueryBound queries
  | .pure _, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ next, queries + 1, h
      => fun answer => queryBound_deterministicOf (next answer) queries (h answer)
  | .sample _ next, queries, h => queryBound_deterministicOf (next 0) queries (h 0)

end VerifiableInference

#print axioms VerifiableInference.toUpload_deterministicOf
#print axioms VerifiableInference.eq_pure_of_support_subset
#print axioms VerifiableInference.evaluate_deterministicOf
#print axioms VerifiableInference.run_deterministicOf
#print axioms VerifiableInference.queryBound_deterministicOf
