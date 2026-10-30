-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/CoinsFirstArg.lean: a scheme whose committer samples one number and then computes.

`Arg.coinsFirst A bound` is the scheme A (ZKCP/Defs.lean) with the committer's random choices
sampled first, as one number from 0, …, bound (ZKCP/CoinsFirst.lean). Its prover's key is the index
with that number; its verifier is A's. Its committer has the form `Arg.CommitsFromCoins`
(ZKCP/CommitsFromCoins.lean; `Arg.commitsFromCoins_coinsFirst`).
If `bound + 1` is enough for the committer at every index (`OComp.CoinsSuffice`), the new scheme
keeps these properties of A, with the same extractor, the same simulator and the same bounds:
  `HasCompletenessError.coinsFirst`        completeness
  `hasIndexBindingWith_coinsFirst_iff`     index binding; this needs no condition on `bound`
  `HasStrongIndexPrivacyWith.coinsFirst`, `HasIndexPrivacyWith.coinsFirst`    index privacy
  `HasExtractionError.coinsFirst`          the honest committer's index is the extracted one
  `IsZKCPArgWith.coinsFirst`               the first three together
Reason: under each hash function the verifier's key with the proofs, and the verifier's key with the
committer's query log, have the same distribution in both schemes (`run_realExp_coinsFirst`; for the
log `run_withTrace_C_coinsFirst` with `OComp.CoinsSuffice.run_eq`). For a finite type of indices
`coinBound A.C` is such a bound (`IsZKCPArgWith.coinsFirst_of_finite`).
Queries: the committer makes no more than A's; the prover makes the committer's and then those of
A's prover (`queryBound_C_coinsFirst`, `queryBound_P_coinsFirst`).
Soundness under an honest key (`wrongExp`, ZKCP/HonestKey.lean) does not carry over by itself: there
the cheating prover is handed both keys, and the sampled number may tell more than the prover's key
of A. If `bound + 1` is enough at every index:
  `false_instance_coinsFirst`   for a prover that is handed the number: a false instance is accepted
                                with probability at most A's extraction error plus A's binding error
                                (one extractor) at the committer's and the prover's numbers of
                                queries
  `Pr_wrongExp_coinsFirst`      for a prover that is handed the verifier's key alone: the same
                                probability as in A, for every event
Not carried over here: refined and adaptive completeness, index binding for many sessions.
Limit: all error bounds here but that of index binding are probabilities that are also over the
sampled number. They say nothing of the committer at a number that somebody has chosen.
Words: a hash function is an `Oracle`, the query log is the `Trace` that `withTrace` returns, the
verifier's key and the prover's key of A are `IVK` and `ISK`. The binder `coins` is the committer's
number, not the field `View.coins`.
-/
import ZKCP.CoinsFirst
import ZKCP.CommitsFromCoins
import ZKCP.HonestKey

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace ZKCP

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-! ## 1. The scheme -/

/-- The scheme A with the committer's random choices sampled first, as one number from 0, …,
`bound`. The prover's key is the index and that number. The prover runs A's committer again at that
number and then runs A's prover with the prover's key that it returns. If `bound + 1` is enough for
A's committer at the index (`OComp.CoinsSuffice`), its verifier's key is distributed as A's; at
another bound nothing is claimed of how the two distributions compare. -/
def Arg.coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) :
    Arg lam I X W IVK (I × Fin (bound + 1)) Pf where
  C := fun i => .sample bound fun coins =>
    ((A.C i).withCoins coins.val).mapO fun key => (key.1, (i, coins))
  P := fun secret x w => ((A.C secret.1).withCoins secret.2.val).bind fun key => A.P key.2 x w
  V := A.V

/-- The committer of `A.coinsFirst bound` samples first: it has the form `Arg.CommitsFromCoins`
(ZKCP/CommitsFromCoins.lean). -/
theorem Arg.commitsFromCoins_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) :
    (A.coinsFirst bound).CommitsFromCoins fun i coins =>
      ((A.C i).withCoins coins.val).mapO Prod.fst where
  committer := fun i => congrArg (OComp.sample bound) (funext fun coins =>
    (OComp.mapO_bind Prod.fst ((A.C i).withCoins coins.val) fun key =>
      .pure (key, (i, coins))).symm)
  noCoin := fun i coins => by
    rw [← OComp.withCoins_mapO]
    exact OComp.drawsNoCoin_withCoins _ _

/-! ## 2. Queries -/

/-- The committer makes no more queries than A's. -/
theorem queryBound_C_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I) (t : ℕ)
    (h : (A.C i).QueryBound t) : ((A.coinsFirst bound).C i).QueryBound t :=
  fun coins => OComp.QueryBound.mapO _ _ t (OComp.QueryBound.withCoins (A.C i) t coins.val h)

/-- The prover makes at most the queries of A's committer and of A's prover together; the bound on
A's prover is asked at every `isk`. -/
theorem queryBound_P_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (coins : Fin (bound + 1)) (x : X) (w : W) (tC tP : ℕ) (hC : (A.C i).QueryBound tC)
    (hP : ∀ isk, (A.P isk x w).QueryBound tP) :
    ((A.coinsFirst bound).P (i, coins) x w).QueryBound (tC + tP) :=
  OComp.QueryBound.bind (fun key : IVK × ISK => A.P key.2 x w) tP (fun key => hP key.2) _ tC
    (OComp.QueryBound.withCoins (A.C i) tC coins.val hC)

/-! ## 3. Under each hash function: the same distributions -/

/-- The committer's keys: the verifier's key of A at the sampled number, with the index and the
number. -/
theorem run_C_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (f : Oracle lam) (i : I) :
    ((A.coinsFirst bound).C i).run f = (PMF.uniformOfFintype (Fin (bound + 1))).map fun coins =>
      (((A.C i).resultWithCoins f coins.val).1, (i, coins)) := by
  show ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun coins =>
      (((A.C i).withCoins coins.val).mapO fun key => (key.1, (i, coins))).run f)
    = (PMF.uniformOfFintype (Fin (bound + 1))).bind fun coins =>
      PMF.pure (((A.C i).resultWithCoins f coins.val).1, (i, coins))
  refine congrArg _ (funext fun coins => ?_)
  rw [OComp.run_mapO, OComp.run_withCoins, PMF.pure_map]

/-- Under each hash function the prover's output is distributed as that of A's prover with the
prover's key of A at that number. -/
theorem run_P_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (f : Oracle lam) (i : I)
    (coins : Fin (bound + 1)) (x : X) (w : W) :
    ((A.coinsFirst bound).P (i, coins) x w).run f
      = (A.P ((A.C i).resultWithCoins f coins.val).2 x w).run f := by
  show (((A.C i).withCoins coins.val).bind fun key => A.P key.2 x w).run f = _
  rw [run_bind, OComp.run_withCoins, PMF.pure_bind]

theorem run_sessionExp_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (f : Oracle lam)
    (ivk : IVK) (i : I) (coins : Fin (bound + 1)) (x : X) (w : W) :
    (sessionExp (A.coinsFirst bound) ivk (i, coins) x w).run f
      = (sessionExp A ivk ((A.C i).resultWithCoins f coins.val).2 x w).run f :=
  run_bind_congr f (run_P_coinsFirst A bound f i coins x w) fun _ => rfl

theorem run_completenessExp_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (h : (A.C i).CoinsSuffice (bound + 1)) (x : X) (w : W) (f : Oracle lam) :
    (completenessExp (A.coinsFirst bound) i x w).run f = (completenessExp A i x w).run f := by
  show (((A.coinsFirst bound).C i).bind fun key =>
      sessionExp (A.coinsFirst bound) key.1 key.2 x w).run f
    = ((A.C i).bind fun key => sessionExp A key.1 key.2 x w).run f
  rw [run_bind, run_bind, run_C_coinsFirst, OComp.CoinsSuffice.run_eq f (A.C i) (bound + 1) h,
    PMF.bind_map, PMF.bind_map]
  exact congrArg _ (funext fun coins => run_sessionExp_coinsFirst A bound f _ i coins x w)

theorem run_realLoop_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ)
    (Z : ViewEnv lam IVK X W Pf) (f : Oracle lam) (i : I) (coins : Fin (bound + 1)) :
    ∀ (Vt : AdvVerifier lam X Pf) (n : ℕ) (v : View lam IVK X Pf),
      (realLoop (A.coinsFirst bound) Z (i, coins) Vt n v).run f
        = (realLoop A Z ((A.C i).resultWithCoins f coins.val).2 Vt n v).run f
  | .halt, _, _ => rfl
  | .query q k, n, v => by
      simp only [realLoop, OComp.run]
      exact run_realLoop_coinsFirst A bound Z f i coins (k (f q)) n _
  | .sample m k, n, v => by
      simp only [realLoop, OComp.run]
      exact congrArg _ (funext fun r => run_realLoop_coinsFirst A bound Z f i coins (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
      simp only [realLoop]
      cases Z v with
      | none => rfl
      | some xw =>
          exact run_bind_congr f (run_P_coinsFirst A bound f i coins xw.1 xw.2) fun π =>
            run_realLoop_coinsFirst A bound Z f i coins (k xw.1 π) n _

theorem run_realExp_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (h : (A.C i).CoinsSuffice (bound + 1)) (Vt : IVK → AdvVerifier lam X Pf)
    (Z : ViewEnv lam IVK X W Pf) (N : ℕ) (f : Oracle lam) :
    (realExp (A.coinsFirst bound) Vt Z i N).run f = (realExp A Vt Z i N).run f := by
  show (((A.coinsFirst bound).C i).bind fun key =>
      realLoop (A.coinsFirst bound) Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).run f
    = ((A.C i).bind fun key => realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩).run f
  rw [run_bind, run_bind, run_C_coinsFirst, OComp.CoinsSuffice.run_eq f (A.C i) (bound + 1) h,
    PMF.bind_map, PMF.bind_map]
  exact congrArg _ (funext fun coins => run_realLoop_coinsFirst A bound Z f i coins _ N _)

/-- The committer with its query log: the verifier's key of A and A's query log at the sampled
number. -/
theorem run_withTrace_C_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (f : Oracle lam)
    (i : I) :
    ((A.coinsFirst bound).C i).withTrace.run f
      = (PMF.uniformOfFintype (Fin (bound + 1))).map fun coins =>
        ((((A.C i).withTrace.resultWithCoins f coins.val).1.1, (i, coins)),
          ((A.C i).withTrace.resultWithCoins f coins.val).2) := by
  show ((PMF.uniformOfFintype (Fin (bound + 1))).bind fun coins =>
      (((A.C i).withCoins coins.val).mapO fun key => (key.1, (i, coins))).withTrace.run f)
    = (PMF.uniformOfFintype (Fin (bound + 1))).bind fun coins =>
      PMF.pure ((((A.C i).withTrace.resultWithCoins f coins.val).1.1, (i, coins)),
        ((A.C i).withTrace.resultWithCoins f coins.val).2)
  refine congrArg _ (funext fun coins => ?_)
  rw [OComp.withTrace_mapO, OComp.withTrace_withCoins, OComp.run_mapO, OComp.run_withCoins,
    PMF.pure_map]

/-- The experiment with the honest committer and any prover (`wrongExp`, ZKCP/HonestKey.lean).
Beside the verifier's key, a prover of the new scheme is handed the index and the sampled number,
and a prover of A is handed the prover's key of A. If `bound + 1` is enough at the index and, under
the given hash function, the two provers have the same output distribution at each number, so have
the two experiments. -/
theorem run_wrongExp_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (h : (A.C i).CoinsSuffice (bound + 1)) (f : Oracle lam)
    (Pt' : IVK × (I × Fin (bound + 1)) → OComp lam (X × Pf))
    (Pt : IVK × ISK → OComp lam (X × Pf))
    (hPt : ∀ coins : Fin (bound + 1),
      (Pt' (((A.C i).resultWithCoins f coins.val).1, (i, coins))).run f
        = (Pt ((A.C i).resultWithCoins f coins.val)).run f) :
    (wrongExp (A.coinsFirst bound) i Pt').run f = (wrongExp A i Pt).run f := by
  unfold wrongExp
  rw [run_bind, run_bind, run_C_coinsFirst, OComp.CoinsSuffice.run_eq f (A.C i) (bound + 1) h,
    PMF.bind_map, PMF.bind_map]
  exact congrArg _ (funext fun coins => run_bind_congr f (hPt coins) fun _ => rfl)

/-- For a prover that is handed the verifier's key alone, `wrongExp` gives every event the same
probability in both schemes, if `bound + 1` is enough at the index. -/
theorem Pr_wrongExp_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (h : (A.C i).CoinsSuffice (bound + 1)) (Pt : IVK → OComp lam (X × Pf)) (T : Set (Bool × X)) :
    Pr (wrongExp (A.coinsFirst bound) i fun key => Pt key.1) (fun _ => T)
      = Pr (wrongExp A i fun key => Pt key.1) fun _ => T :=
  Pr_congr (fun f => run_wrongExp_coinsFirst A bound i h f _ _ fun _ => rfl) _

/-! ## 4. What the scheme keeps -/

variable {R : IndexedRelation I X W PP} {A : Arg lam I X W IVK ISK Pf}

/-- Completeness, with the same error. -/
theorem HasCompletenessError.coinsFirst {α : ℝ≥0∞} (bound : ℕ)
    (h : ∀ i, (A.C i).CoinsSuffice (bound + 1)) (hc : HasCompletenessError R A α) :
    HasCompletenessError R (A.coinsFirst bound) α := fun i x w hr =>
  (Pr_congr (fun f => run_completenessExp_coinsFirst A bound i (h i) x w f) _).trans_le
    (hc i x w hr)

/-- Index binding is the same statement for both schemes: it is about the verifier alone. -/
theorem hasIndexBindingWith_coinsFirst_iff (bound : ℕ) (E : Extractor lam I X W IVK Pf)
    (ε : ℕ → ℕ → ℝ≥0∞) :
    HasIndexBindingWith R (A.coinsFirst bound) E ε ↔ HasIndexBindingWith R A E ε := Iff.rfl

/-- Index privacy at one index and one environment, with the same simulator and the same bound. -/
theorem PrivacyFor.coinsFirst {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞} {i : I}
    {Z : ViewEnv lam IVK X W Pf} (bound : ℕ) (h : (A.C i).CoinsSuffice (bound + 1))
    (hp : PrivacyFor R A S ζ i Z) : PrivacyFor R (A.coinsFirst bound) S ζ i Z := by
  intro tV Vt N hV
  have e : (fun T => Pr (realExp (A.coinsFirst bound) Vt Z i N) fun _ => T)
      = fun T => Pr (realExp A Vt Z i N) fun _ => T :=
    funext fun T => Pr_congr (fun f => run_realExp_coinsFirst A bound i h Vt Z N f) _
  exact ⟨(congrArg (fun F => SD F fun T => prob (idealExp R S Vt Z i N) T) e).trans_le
    (hp tV Vt N hV).1, (hp tV Vt N hV).2⟩

/-- The stronger form of index privacy, with the same simulator and the same bound. -/
theorem HasStrongIndexPrivacyWith.coinsFirst {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞}
    (bound : ℕ) (h : ∀ i, (A.C i).CoinsSuffice (bound + 1))
    (hp : HasStrongIndexPrivacyWith R A S ζ) :
    HasStrongIndexPrivacyWith R (A.coinsFirst bound) S ζ :=
  fun i Z hZ => PrivacyFor.coinsFirst bound (h i) (hp i Z hZ)

/-- Index privacy, with the same simulator and the same bound. -/
theorem HasIndexPrivacyWith.coinsFirst {S : Simulator lam PP IVK X Pf} {ζ : ℕ → ℕ → ℝ≥0∞}
    (bound : ℕ) (h : ∀ i, (A.C i).CoinsSuffice (bound + 1)) (hp : HasIndexPrivacyWith R A S ζ) :
    HasIndexPrivacyWith R (A.coinsFirst bound) S ζ :=
  fun i Z hZ => PrivacyFor.coinsFirst bound (h i) (hp i Z hZ)

/-- Under the hypotheses below, what the extractor gives from the honest committer's key and query
log is the committed index except with probability at most δ: the same extractor and the same error
as for A. -/
theorem HasExtractionError.coinsFirst {E : Extractor lam I X W IVK Pf} {δ : ℝ≥0∞} (bound : ℕ)
    (h : ∀ i, (A.C i).CoinsSuffice (bound + 1)) (he : HasExtractionError A E δ) :
    HasExtractionError (A.coinsFirst bound) E δ := by
  intro i
  refine le_trans (le_of_eq ?_) (he i)
  unfold Pr PrCoins
  refine lintegral_congr fun f => ?_
  rw [run_withTrace_C_coinsFirst,
    OComp.CoinsSuffice.run_eq f (A.C i).withTrace (bound + 1)
      (OComp.CoinsSuffice.withTrace _ _ (h i)),
    prob_map, prob_map]
  exact congrArg (prob _) (Set.ext fun _ => Iff.rfl)

/-- If `bound + 1` is enough at every index and A has, for one extractor, extraction error δ and
index binding error ε: under an honest key a prover that is handed the verifier's key, the index and
the sampled number gets a false instance accepted with probability at most δ + ε tC tP. Here the
committer makes at most tC queries and the prover at most tP; the prover returns one instance with
one proof. -/
theorem false_instance_coinsFirst {E : Extractor lam I X W IVK Pf} {δ : ℝ≥0∞} {ε : ℕ → ℕ → ℝ≥0∞}
    (bound : ℕ) (h : ∀ i, (A.C i).CoinsSuffice (bound + 1)) (he : HasExtractionError A E δ)
    (hb : HasIndexBindingWith R A E ε) (i : I) {tC tP : ℕ} (hC : (A.C i).QueryBound tC)
    (Pt : IVK × (I × Fin (bound + 1)) → OComp lam (X × Pf)) (hPt : ∀ key, (Pt key).QueryBound tP) :
    Pr (wrongExp (A.coinsFirst bound) i Pt) (fun _ => {o | o.1 = true ∧ o.2 ∉ R.L (some i)})
      ≤ δ + ε tC tP :=
  false_instance_of_extraction (he.coinsFirst bound h)
    ((hasIndexBindingWith_coinsFirst_iff bound E ε).2 hb) i
    (queryBound_C_coinsFirst A bound i tC hC) Pt hPt

/-- Completeness, index binding and index privacy together: the same extractor, the same simulator,
the same three bounds. -/
theorem IsZKCPArgWith.coinsFirst {E : Extractor lam I X W IVK Pf} {S : Simulator lam PP IVK X Pf}
    {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (bound : ℕ) (h : ∀ i, (A.C i).CoinsSuffice (bound + 1))
    (ha : IsZKCPArgWith R A E S α ε ζ) : IsZKCPArgWith R (A.coinsFirst bound) E S α ε ζ :=
  ⟨ha.completeness.coinsFirst bound h,
    (hasIndexBindingWith_coinsFirst_iff bound E ε).2 ha.indexBinding,
    ha.indexPrivacy.coinsFirst bound h⟩

/-- For a finite type of indices the three properties carry over at the bound `coinBound A.C`. -/
theorem IsZKCPArgWith.coinsFirst_of_finite [Finite I] {E : Extractor lam I X W IVK Pf}
    {S : Simulator lam PP IVK X Pf} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}
    (ha : IsZKCPArgWith R A E S α ε ζ) :
    IsZKCPArgWith R (A.coinsFirst (coinBound A.C)) E S α ε ζ :=
  ha.coinsFirst (coinBound A.C) (coinsSuffice_coinBound A.C)

end ZKCP
