-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bridge.lean

The hash model of VerifiableInference/RandomOracleModel.lean is that of ZKCP/Defs.lean, at 256 bits,
under other names. Below, "the library's" means: of ZKCP/. Proved here:
  * bit strings, hash values, hash functions and query logs are the library's types, and the
    distribution on hash functions is the library's (by definition);
  * a randomized algorithm corresponds to one algorithm of the library (`toUpload`, with the inverse
    `ofUpload`): the same distribution of results
    under every hash function, the same bound on its queries, the same query log;
  * `Prob` is the library's `Pr` of the corresponding algorithm.
The last section is the calculus of `run` for the renamed algorithms, which
VerifiableInference/Checks.lean and VerifiableInference/Agreement.lean use.
-/
import VerifiableInference.Statements
import ZKCP.Lemmas

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

/-! ## 1. The same types, the same distribution -/

theorem bitString_eq : BitString = ZKCP.Str := rfl
theorem digest_eq : Digest = ZKCP.Digest 256 := rfl
theorem hash_eq : Hash = ZKCP.Oracle 256 := rfl
theorem queryLog_eq : QueryLog = ZKCP.Trace 256 := rfl
theorem uniformHash_eq : uniformHash = ZKCP.U 256 := rfl
theorem eventProbability_eq {α : Type} (distribution : PMF α) (event : Set α) :
    eventProbability distribution event = ZKCP.prob distribution event := rfl
theorem statisticalDistance_eq {α : Type} (first second : Set α → ℝ≥0∞) :
    statisticalDistance first second = ZKCP.SD first second := rfl

/-! ## 2. The same algorithms -/

namespace RandomizedAlgorithm
variable {α β : Type}

/-- The same algorithm in the library's type. In the names `toUpload` and `ofUpload`, "upload" means
the library's own type of algorithms, `ZKCP.OComp 256`; nothing is uploaded. -/
def toUpload : RandomizedAlgorithm α → ZKCP.OComp 256 α
  | done result => .pure result
  | query input next => .query input fun answer => (next answer).toUpload
  | sample bound next => .sample bound fun draw => (next draw).toUpload

/-- An algorithm of the library's type, as a `RandomizedAlgorithm`. -/
def ofUpload : ZKCP.OComp 256 α → RandomizedAlgorithm α
  | .pure result => done result
  | .query input next => query input fun answer => ofUpload (next answer)
  | .sample bound next => sample bound fun draw => ofUpload (next draw)

theorem ofUpload_toUpload : ∀ algorithm : RandomizedAlgorithm α, ofUpload algorithm.toUpload =
    algorithm
  | done _ => rfl
  | query input next => by
      show query input (fun answer => ofUpload (next answer).toUpload) = query input next
      exact congrArg _ (funext fun answer => ofUpload_toUpload (next answer))
  | sample bound next => by
      show sample bound (fun draw => ofUpload (next draw).toUpload) = sample bound next
      exact congrArg _ (funext fun draw => ofUpload_toUpload (next draw))

theorem toUpload_ofUpload : ∀ algorithm : ZKCP.OComp 256 α, (ofUpload algorithm).toUpload =
    algorithm
  | .pure _ => rfl
  | .query input next => by
      show ZKCP.OComp.query input (fun answer => (ofUpload (next answer)).toUpload) =
          ZKCP.OComp.query input next
      exact congrArg _ (funext fun answer => toUpload_ofUpload (next answer))
  | .sample bound next => by
      show ZKCP.OComp.sample bound (fun draw => (ofUpload (next draw)).toUpload) = ZKCP.OComp.sample
          bound next
      exact congrArg _ (funext fun draw => toUpload_ofUpload (next draw))

/-- The same distribution of results under every hash function. -/
theorem run_toUpload (hash : Hash) : ∀ algorithm : RandomizedAlgorithm α, algorithm.toUpload.run
    hash = algorithm.run hash
  | done _ => rfl
  | query input next => run_toUpload hash (next (hash input))
  | sample bound next => by
      show (PMF.uniformOfFintype (Fin (bound + 1))).bind (fun draw => (next draw).toUpload.run hash)
        = (PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).run hash
      exact congrArg _ (funext fun draw => run_toUpload hash (next draw))

/-- The same bound on the queries. -/
theorem queryBound_toUpload : ∀ (algorithm : RandomizedAlgorithm α) (queries : ℕ),
    algorithm.toUpload.QueryBound queries ↔ algorithm.QueryBound queries
  | done _, _ => Iff.rfl
  | query _ _, 0 => Iff.rfl
  | query _ next, queries + 1 => forall_congr' fun answer => queryBound_toUpload (next answer)
      queries
  | sample _ next, queries => forall_congr' fun draw => queryBound_toUpload (next draw) queries

theorem toUpload_bind : ∀ (first : RandomizedAlgorithm α) (rest : α → RandomizedAlgorithm β),
    (first.bind rest).toUpload = first.toUpload.bind fun result => (rest result).toUpload
  | done _, _ => rfl
  | query input next, rest => by
      show ZKCP.OComp.query input (fun answer => ((next answer).bind rest).toUpload)
        = ZKCP.OComp.query input fun answer => (next answer).toUpload.bind fun result =>
            (rest result).toUpload
      exact congrArg _ (funext fun answer => toUpload_bind (next answer) rest)
  | sample bound next, rest => by
      show ZKCP.OComp.sample bound (fun draw => ((next draw).bind rest).toUpload)
        = ZKCP.OComp.sample bound fun draw => (next draw).toUpload.bind fun result =>
            (rest result).toUpload
      exact congrArg _ (funext fun draw => toUpload_bind (next draw) rest)

/-- The same query log. -/
theorem toUpload_withQueryLog : ∀ algorithm : RandomizedAlgorithm α, algorithm.withQueryLog.toUpload
    = algorithm.toUpload.withTrace
  | done _ => rfl
  | query input next => by
      show ZKCP.OComp.query input (fun answer =>
          ((next answer).withQueryLog.bind fun rest => done
              (rest.1, (input, answer) :: rest.2)).toUpload)
        = ZKCP.OComp.query input fun answer =>
          (next answer).toUpload.withTrace.bind fun out => ZKCP.OComp.pure
              (out.1, (input, answer) :: out.2)
      refine congrArg _ (funext fun answer => ?_)
      rw [toUpload_bind, toUpload_withQueryLog (next answer)]
      rfl
  | sample bound next => by
      show ZKCP.OComp.sample bound (fun draw => (next draw).withQueryLog.toUpload)
        = ZKCP.OComp.sample bound fun draw => (next draw).toUpload.withTrace
      exact congrArg _ (funext fun draw => toUpload_withQueryLog (next draw))

theorem run_ofUpload (hash : Hash) (algorithm : ZKCP.OComp 256 α) : (ofUpload algorithm).run hash =
    algorithm.run hash := by
  rw [← run_toUpload, toUpload_ofUpload]

theorem run_ofUpload_withQueryLog (hash : Hash) (algorithm : ZKCP.OComp 256 α) :
    (ofUpload algorithm).withQueryLog.run hash = algorithm.withTrace.run hash := by
  rw [← run_toUpload, toUpload_withQueryLog, toUpload_ofUpload]

theorem run_toUpload_withTrace (hash : Hash) (algorithm : RandomizedAlgorithm α) :
    algorithm.toUpload.withTrace.run hash = algorithm.withQueryLog.run hash := by
  rw [← toUpload_withQueryLog, run_toUpload]

theorem queryBound_ofUpload (algorithm : ZKCP.OComp 256 α) (queries : ℕ) :
    (ofUpload algorithm).QueryBound queries ↔ algorithm.QueryBound queries := by
  rw [← queryBound_toUpload, toUpload_ofUpload]

end RandomizedAlgorithm

open RandomizedAlgorithm

/-- `Prob` is the library's `Pr` of the corresponding algorithm, for an event that does not mention
the hash function. -/
theorem Prob_eq_Pr {α : Type} (experiment : RandomizedAlgorithm α) (event : Set α) :
    Prob experiment event = ZKCP.Pr experiment.toUpload (fun _ => event) := by
  unfold Prob ZKCP.Pr ZKCP.PrCoins
  simp only [run_toUpload]
  rfl

/-! ## 3. The calculus of `run` for the renamed algorithms -/

variable {α β : Type}

theorem run_done (hash : Hash) (result : α) : (RandomizedAlgorithm.done result).run hash = PMF.pure
    result := rfl

theorem run_bind (hash : Hash) (first : RandomizedAlgorithm α) (rest : α → RandomizedAlgorithm β) :
    (first.bind rest).run hash = (first.run hash).bind fun result => (rest result).run hash := by
  rw [← run_toUpload, toUpload_bind, ZKCP.run_bind]
  simp only [run_toUpload]

/-- The probability of an event under a hash function is a measurable function of the hash
function. -/
theorem measurable_eventProbability_run (algorithm : RandomizedAlgorithm α) (event : Set α) :
    Measurable fun hash : Hash => eventProbability (algorithm.run hash) event := by
  have h := ZKCP.measurable_prob_run algorithm.toUpload event
  simp only [run_toUpload] at h
  exact h

/-- Under a hash function, a deterministic algorithm as a step of an experiment returns `evaluate`
with probability 1. -/
theorem DeterministicAlgorithm.run_toRandomized (hash : Hash) :
    ∀ algorithm : DeterministicAlgorithm α, algorithm.toRandomized.run hash = PMF.pure
        (algorithm.evaluate hash)
  | .done _ => rfl
  | .query input next => by
      show ((next (hash input)).toRandomized).run hash = PMF.pure
          ((next (hash input)).evaluate hash)
      exact DeterministicAlgorithm.run_toRandomized hash (next (hash input))

/-- A bound on an algorithm's queries also holds if a function of its result follows it. -/
theorem queryBound_map (f : α → β) :
    ∀ (algorithm : RandomizedAlgorithm α) (queries : ℕ), algorithm.QueryBound queries →
      (algorithm.bind fun result => .done (f result)).QueryBound queries
  | .done _, _, _ => trivial
  | .query _ _, 0, h => h.elim
  | .query _ next, queries + 1, h => fun answer => queryBound_map f (next answer) queries (h answer)
  | .sample _ next, queries, h => fun draw => queryBound_map f (next draw) queries (h draw)

/-- The query log of an algorithm followed by a function of its result is the query log of the
algorithm. -/
theorem run_withQueryLog_map (f : α → β) (hash : Hash) : ∀ algorithm : RandomizedAlgorithm α,
    (algorithm.bind fun result => .done (f result)).withQueryLog.run hash
      = (algorithm.withQueryLog.run hash).bind fun out => PMF.pure (f out.1, out.2)
  | .done result => by
      show PMF.pure (f result, []) = (PMF.pure (result, [])).bind _
      rw [PMF.pure_bind]
  | .query input next => by
      show ((((next (hash input)).bind fun result => RandomizedAlgorithm.done
          (f result)).withQueryLog).bind fun rest =>
          RandomizedAlgorithm.done (rest.1, (input, hash input) :: rest.2)).run hash
        = (((next (hash input)).withQueryLog.bind fun rest => RandomizedAlgorithm.done
            (rest.1, (input, hash input) :: rest.2)).run hash).bind _
      rw [run_bind, run_bind, run_withQueryLog_map f hash (next (hash input)), PMF.bind_bind,
          PMF.bind_bind]
      refine congrArg _ (funext fun out => ?_)
      rw [PMF.pure_bind, run_done, run_done, PMF.pure_bind]
  | .sample bound next => by
      show (PMF.uniformOfFintype (Fin (bound + 1))).bind
          (fun draw => ((next draw).bind fun result => RandomizedAlgorithm.done
              (f result)).withQueryLog.run hash)
        = ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).withQueryLog.run
            hash).bind _
      rw [PMF.bind_bind]
      exact congrArg _ (funext fun draw => run_withQueryLog_map f hash (next draw))

/-- Recording the query log does not change the result. -/
theorem run_withQueryLog_fst (hash : Hash) : ∀ algorithm : RandomizedAlgorithm α,
    (algorithm.withQueryLog.run hash).bind (fun out => PMF.pure out.1) = algorithm.run hash
  | .done result => PMF.pure_bind _ _
  | .query input next => by
      show (((next (hash input)).withQueryLog.bind fun rest =>
          RandomizedAlgorithm.done (rest.1, (input, hash input) :: rest.2)).run hash).bind _ =
              (next (hash input)).run hash
      rw [run_bind, PMF.bind_bind]
      have e : ∀ rest : α × QueryLog,
          ((RandomizedAlgorithm.done (rest.1, (input, hash input) :: rest.2) : RandomizedAlgorithm
              (α × QueryLog)).run hash).bind
            (fun out => PMF.pure out.1) = PMF.pure rest.1 := fun rest => PMF.pure_bind _ _
      simp only [e]
      exact run_withQueryLog_fst hash (next (hash input))
  | .sample bound next => by
      show ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).withQueryLog.run
          hash).bind _
        = (PMF.uniformOfFintype (Fin (bound + 1))).bind fun draw => (next draw).run hash
      rw [PMF.bind_bind]
      exact congrArg _ (funext fun draw => run_withQueryLog_fst hash (next draw))

/-- The query log is a by-product: an algorithm run with its query log, followed by a step that
reads its result alone, is the algorithm followed by that step. -/
theorem run_withQueryLog_bind_fst (hash : Hash) (algorithm : RandomizedAlgorithm α)
    (rest : α → PMF β) :
    (algorithm.withQueryLog.run hash).bind (fun out => rest out.1) = (algorithm.run hash).bind rest
        := by
  conv_rhs => rw [← run_withQueryLog_fst hash algorithm]
  rw [PMF.bind_bind]
  simp only [PMF.pure_bind]

/-- Two experiments with the same distribution of results under every hash function have the same
probabilities. -/
theorem Prob_congr_run {first second : RandomizedAlgorithm α}
    (h : ∀ hash, first.run hash = second.run hash) (event : Set α) :
    Prob first event = Prob second event := by
  unfold Prob
  simp [h]

/-- An event of probability 0 under every hash function has probability 0. -/
theorem Prob_eq_zero (experiment : RandomizedAlgorithm α) (event : Set α)
    (h : ∀ hash, eventProbability (experiment.run hash) event = 0) : Prob experiment event = 0 := by
  unfold Prob
  simp [h]

/-- Indicators: if p implies q, the indicator of p is at most the indicator of q. -/
theorem ind_le {p q : Prop} {dp : Decidable p} {dq : Decidable q} (h : p → q) :
    (@ite _ p dp (1 : ℝ≥0∞) 0) ≤ (@ite _ q dq 1 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h hp)]
  · rw [if_neg hp]; simp

/-- Indicators: if p implies q or r, the indicator of p is at most the sum of the indicators of q
and r. -/
theorem ind_le_add {p q r : Prop} {dp : Decidable p} {dq : Decidable q} {dr : Decidable r}
    (h : p → q ∨ r) :
    (@ite _ p dp (1 : ℝ≥0∞) 0) ≤ (@ite _ q dq 1 0) + (@ite _ r dr 1 0) := by
  by_cases hp : p
  · rcases h hp with hq | hr
    · rw [if_pos hp, if_pos hq]; exact le_self_add
    · rw [if_pos hp, if_pos hr]; exact le_add_self
  · rw [if_neg hp]; simp

end VerifiableInference
