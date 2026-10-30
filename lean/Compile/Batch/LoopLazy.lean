-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/LoopLazy.lean: the search over nonces (`Ref.askW`, Compile/Batch/CompleteRefDefs.lean)
under lazily sampled oracles. It proves `Spec.askW_law` (Compile/Batch/SpecLoop.lean).

  `set_other`        a table with one more entry, at another query to the same oracle
  `askW_law`         if the queries of the attempts are new and differ from each other, the final
                     answer has the distribution `Prob.retry`, exactly
  `askW_then`        the same with what follows: if the distribution of h of what follows the final
                     answer, from any table that differs from T only at the attempts' queries
                     (`LeftBy`), depends on the answer only (F), then h of the whole has the
                     distribution (retry ..).bind F

Notation: `Prob.retry ok n` (Prob/Retry.lean): sample until the test is passed, at most n + 1 times;
the last sample is output in any case.
-/
import Compile.Batch.SpecLoop

noncomputable section

namespace Compile.Batch.LoopLazy
open Iop Rom Prob

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem set_other (T : Table (spec lam K L)) (t : Tag) {q q' : FbIn lam L t}
    (h : q' ≠ q) (r : (spec lam K L).Rng (OracleName.fb t)) :
    T.set (OracleName.fb t) q r (OracleName.fb t) q' = T (OracleName.fb t) q' := by
  rw [Table.set, Function.update_self,
    @Function.update_of_ne _ _ ((spec lam K L).decDom (OracleName.fb t)) _ _ h]

section Loop
variable {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (q : ℕ → FbIn lam L t)

/-- T' is T except at queries among q j, .., q (j + n) to the Fiat-Shamir oracle of t -/
def LeftBy (T : Table (spec lam K L)) (j n : ℕ) (T' : Table (spec lam K L)) : Prop :=
  ∀ (o : OracleName) (x : (spec lam K L).Dom o), T' o x ≠ T o x →
    ∃ m, j ≤ m ∧ m ≤ j + n ∧ (⟨o, x⟩ : Σ o : OracleName, (spec lam K L).Dom o) = ⟨OracleName.fb t, q m⟩

theorem obind_assoc {S : OSpec} {α β γ : Type} (c : OComp S α)
    (f : α → OComp S β) (k : β → OComp S γ) :
    (c.bind f).bind k = c.bind fun a => (f a).bind k := by
  induction c with
  | pure a => rfl
  | query o q k' ih => simp only [OComp.bind, ih]
  | sample n k' ih => simp only [OComp.bind, ih]

theorem obind_pure {S : OSpec} {α : Type} (c : OComp S α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [OComp.bind, ih]
  | sample n k ih => simp only [OComp.bind, ih]

theorem run_ask_new {γ : Type} (x : FbIn lam L t) (k : (Fin K → Dig lam) × Dig lam → TypedOracleComputation lam K L γ)
    (T : Table (spec lam K L)) (hnew : T (OracleName.fb t) x = none) :
    ((askTypedOracle (L := L) (K := K) (OracleName.fb t) x).bind k).runLazy T =
      (unif ((Fin K → Dig lam) × Dig lam)).bind fun ans =>
        (k ans).runLazy (T.set (OracleName.fb t) x ans) := by
  show (OComp.runLazy (OComp.query (S := spec lam K L) (OracleName.fb t) x k) T) = _
  simp only [OComp.runLazy]
  rw [hnew]
  rfl

theorem leftBy_set (T : Table (spec lam K L)) (j n : ℕ) (ans : (spec lam K L).Rng (OracleName.fb t)) :
    LeftBy t q T j n (T.set (OracleName.fb t) (q j) ans) := by
  intro o x hx
  refine ⟨j, le_rfl, Nat.le_add_right _ _, ?_⟩
  by_contra hne
  apply hx
  by_cases ho : o = OracleName.fb t
  · subst ho
    exact set_other T t (fun e => hne (by rw [e])) ans
  · exact congrFun (Function.update_of_ne ho _ _) x

theorem LeftBy.step {T T1 T' : Table (spec lam K L)} {j n : ℕ}
    (h1 : LeftBy t q T j 0 T1) (h2 : LeftBy t q T1 (j + 1) n T') : LeftBy t q T j (n + 1) T' := by
  intro o x hx
  by_cases e : T' o x = T1 o x
  · obtain ⟨m, a, b, c⟩ := h1 o x (by rw [← e]; exact hx)
    exact ⟨m, a, by omega, c⟩
  · obtain ⟨m, a, b, c⟩ := h2 o x e
    exact ⟨m, by omega, by omega, c⟩

/-- The search, with what follows it. -/
theorem askW_then {γ τ : Type} (k : (Fin K → Dig lam) × Dig lam → TypedOracleComputation lam K L γ)
    (h : γ × Table (spec lam K L) → τ) (F : (Fin K → Dig lam) × Dig lam → PMF τ) :
    ∀ (n j : ℕ) (T : Table (spec lam K L)), (∀ m, j ≤ m → m ≤ j + n → T (OracleName.fb t) (q m) = none) →
      (∀ m m', j ≤ m → m ≤ j + n → j ≤ m' → m' ≤ j + n → q m = q m' → m = m') →
      (∀ ans T', LeftBy t q T j n T' → ((k ans).runLazy T').map h = F ans) →
      (((Ref.askW g chal t q n j).bind k).runLazy T).map h =
        (retry (fun x : (Fin K → Dig lam) × Dig lam => g.ok (chal x.1)) n).bind F
  | 0, j, T, hnew, _, hk => by
      rw [Ref.askW]
      refine (congrArg (PMF.map h)
        (run_ask_new t (q j) k T (hnew j le_rfl (Nat.le_add_right _ _)))).trans ?_
      rw [PMF.map_bind]
      exact congrArg _ (funext fun ans => hk ans _ (leftBy_set t q T j 0 ans))
  | n + 1, j, T, hnew, hinj, hk => by
      rw [Ref.askW, obind_assoc, run_ask_new t (q j) _ T (hnew j le_rfl (Nat.le_add_right _ _)),
        PMF.map_bind, retry, PMF.bind_bind]
      refine congrArg _ (funext fun ans => ?_)
      by_cases ho : g.ok (chal ans.1) = true
      · rw [if_pos ho, if_pos ho, PMF.pure_bind]
        exact hk ans _ (leftBy_set t q T j (n + 1) ans)
      · rw [if_neg ho, if_neg ho]
        refine askW_then k h F n (j + 1) (T.set (OracleName.fb t) (q j) ans) (fun m h1 h2 => ?_)
          (fun m m' a b c d => hinj m m' (by omega) (by omega) (by omega) (by omega))
          fun ans' T' hT' => ?_
        · have hne : q m ≠ q j := fun e => by
            have := hinj m j (by omega) (by omega) le_rfl (by omega) e
            omega
          rw [set_other T t hne ans]
          exact hnew m (by omega) (by omega)
        · exact hk ans' T' (LeftBy.step t q (leftBy_set t q T j 0 ans) hT')

end Loop

end Compile.Batch.LoopLazy

namespace Compile.Batch
open Iop Rom Prob LoopLazy

theorem askW_law : Spec.askW_law := by
  intro I X lam K L C P g chal t q n j T hnew hinj
  have h := askW_then g chal t q (OComp.pure (S := spec lam K L))
    (fun x : ((Fin K → Dig lam) × Dig lam) × Table (spec lam K L) => x.1)
    PMF.pure n j T hnew hinj (fun ans T' _ => PMF.pure_map _ _)
  rw [obind_pure, PMF.bind_pure] at h
  exact h

end Compile.Batch
