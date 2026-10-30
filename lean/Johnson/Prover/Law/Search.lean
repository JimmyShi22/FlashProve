-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Search.lean: THE SEARCH FOR A NONCE UNDER LAZILY SAMPLED ORACLES, WITH WHAT
FOLLOWS IT: if the queries of the tries are new in the table and differ from each other, the
probability of an event of what follows is at most the mean, over "sample until the test is passed"
(Prob.retry, Prob/Retry.lean), of a bound that may hang on the last answer; where the search runs
out the bound is 1.

Why an inequality. What follows the search is the rest of the prover's chain, of which a bound is
known, not a law.

Main names. PrFrom_le_one, set_fb_other, PrFrom_ask a probability is at most 1; a query that is new
  in the table is
    answered by a fresh uniform draw, which the table then holds.
  search_le   THE STATEMENT.

An earlier lemma: askW_then (Compile/Batch/LoopLazy.lean), over the first form's oracles, an
equation of laws for a search that hands on its last answer whatever it is. The walk is askW_then's.

Limits. One search. Nothing on what the mean is: Johnson/Prover/Law/Round.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Defs
import Johnson.Prover.Law.Keeps
import Compile.Batch.LoopLazy
import Prob.Retry

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Batch.LoopLazy (obind_assoc)
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem PrFrom_le_one {S : OSpec} {α : Type} (T : Table S) (c : OComp S α) (E : Set α) :
    PrFrom T c E ≤ 1 := by
  rw [PrFrom_eq_lazy]
  exact pr_le_one _ _

/-- a table with one more entry in the column fb t, at another query of that column -/
theorem set_fb_other (T : Table (typedOracleFamily lam K L)) (t : Tag) {q q' : FbIn lam L t} (h : q' ≠ q)
    (r : FsAns lam K) : T.set (OracleName.fb t) q r (OracleName.fb t) q' = T (OracleName.fb t) q' :=
  Law.set_other (S := typedOracleFamily lam K L) (o := OracleName.fb t) (o' := OracleName.fb t) T r
    fun e => h (eq_of_heq (Sigma.mk.inj_iff.1 e).2)

/-- A query that is new in the table is answered by a fresh uniform draw. -/
theorem PrFrom_ask {γ : Type} (t : Tag) (x : FbIn lam L t) (k : FsAns lam K → TypedOracleComputation lam K L γ)
    (T : Table (typedOracleFamily lam K L)) (hnew : T (OracleName.fb t) x = none) (E : Set γ) :
    PrFrom T ((askTypedOracle (L := L) (K := K) (OracleName.fb t) x).bind k) E =
      expect (unif (FsAns lam K)) fun ans => PrFrom (T.set (OracleName.fb t) x ans) (k ans) E := by
  have h : (askTypedOracle (L := L) (K := K) (OracleName.fb t) x).runLazy T =
      (unif (FsAns lam K)).bind fun ans => PMF.pure (ans, T.set (OracleName.fb t) x ans) := by
    show OComp.runLazy (OComp.query (S := typedOracleFamily lam K L) (OracleName.fb t) x OComp.pure) T = _
    simp only [OComp.runLazy]
    rw [hnew]
    rfl
  rw [PrFrom_bind, h]
  exact (expect_bind _ _ _).trans (expect_congr _ fun ans => expect_pure _ _)

section
variable {C P γ : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C) (t : Tag)
  (qf : P → FbIn lam L t) (α : P) (k : Option (P × FsAns lam K) → TypedOracleComputation lam K L γ) (E : Set γ)
  (φ : FsAns lam K → ℝ≥0∞)

/-- **The search, with what follows it.** The tries are the numbers j, .., j + n. hk: from every
table that agrees with T, in the column fb t, off the tries' queries, what follows a passed try has
the event with probability at most φ of the answer. -/
theorem search_le : ∀ (n j : ℕ) (T : Table (typedOracleFamily lam K L)),
    (∀ m, j ≤ m → m ≤ j + n → T (OracleName.fb t) (qf (gr.put m α)) = none) →
    (∀ m m', j ≤ m → m ≤ j + n → j ≤ m' → m' ≤ j + n →
      qf (gr.put m α) = qf (gr.put m' α) → m = m') →
    (∀ m ans T', gr.ok (chal ans.1) = true →
      (∀ q, (∀ m', q ≠ qf (gr.put m' α)) → T' (OracleName.fb t) q = T (OracleName.fb t) q) →
      PrFrom T' (k (some (gr.put m α, ans))) E ≤ φ ans) →
    PrFrom T ((searchO gr chal (fun β => askTypedOracle (L := L) (K := K) (OracleName.fb t) (qf β)) α (n + 1) j).bind
        k) E ≤
      expect (retry (fun a : FsAns lam K => gr.ok (chal a.1)) n) fun a =>
        if gr.ok (chal a.1) then φ a else 1
  | 0, j, T, hnew, _, hk => by
    rw [searchO, obind_assoc]
    refine (PrFrom_ask t _ _ T (hnew j le_rfl (Nat.le_add_right _ _)) E).trans_le ?_
    refine expect_mono _ fun ans => ?_
    by_cases ho : gr.ok (chal ans.1) = true
    · rw [if_pos ho, if_pos ho]
      refine hk j ans _ ho fun q hq => ?_
      exact set_fb_other T t (hq j) ans
    · rw [if_neg ho, if_neg ho]
      exact PrFrom_le_one _ _ _
  | n + 1, j, T, hnew, hinj, hk => by
    rw [searchO, obind_assoc, retry, expect_bind]
    refine (PrFrom_ask t _ _ T (hnew j le_rfl (Nat.le_add_right _ _)) E).trans_le ?_
    refine expect_mono _ fun ans => ?_
    by_cases ho : gr.ok (chal ans.1) = true
    · rw [if_pos ho, if_pos ho, expect_pure, if_pos ho]
      refine hk j ans _ ho fun q hq => ?_
      exact set_fb_other T t (hq j) ans
    · rw [if_neg ho, if_neg ho]
      refine search_le n (j + 1) (T.set (OracleName.fb t) (qf (gr.put j α)) ans) (fun m h1 h2 => ?_)
        (fun m m' a b c d => hinj m m' (by omega) (by omega) (by omega) (by omega))
        fun m ans' T' ho' hT' => ?_
      · have hne : qf (gr.put m α) ≠ qf (gr.put j α) := fun e => by
          have := hinj m j (by omega) (by omega) le_rfl (by omega) e
          omega
        rw [set_fb_other T t hne ans]
        exact hnew m (by omega) (by omega)
      · refine hk m ans' T' ho' fun q hq => ?_
        rw [hT' q hq]
        exact set_fb_other T t (hq j) ans

end

end OnBytes.Prover
