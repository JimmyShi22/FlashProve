-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CompleteAdaptive.lean: general lemmas on runs with lazily sampled oracles, on counts of
queries and on probabilities, and a sanity lemma on completeness against an adaptive environment
(`HasAdaptiveCompleteness`, Compile/SpecAdaptive.lean) (words of this library: lean/GLOSSARY.md). No
program of a scheme occurs in this file.

 Part 1  oracle algorithms in general: lazy runs of erased token programs
         (`runLazy_erase_bind_pure`, `erase_prefix`); how many queries to some oracles a lazy run
         adds to the table (`QB`, `TLe`, `runLazy_TLe`); the same count for token programs (`SQB`;
         `Step`, Rom/Defer.lean).
 Part 2  one round, in plain types (`avg_step`); a lazy run at a query that is not in the table
         (`pr_runLazy_query_none`); `card_dig`, `prRho_nil_of_mem`.
 Part 3  an event about what comes first (`pr_bind_le_pr`); the bits of a number determine it
         (`bits_injective`).
 Part 4  a last step that only computes (`runLazy_bind_pure`); a hash term (`hsh`).
 Part 5  one lazy answer adds at most one entry (`TLe_lazyAnswer`); two facts on expectations.
 Part 6  two sequences that agree on the support of the first part (`bind_congr_support`).
 Part 7  `completeness_of_adaptive`: the property implies completeness in the sense of
         `ZKCP.Gen.HasCompletenessError`, for batches of at most one pair, with the error at no
         queries and one session.

Notation: `TLe P T sz`, a proposition: the table T holds at most sz queries to oracles with the
property P; `T : Table S` (Rom/OSpec.lean): a partial table: what lazy sampling has fixed so far.
-/
import Compile.SpecAdaptive
import Compile.GluePrivacy
import Compile.EraseKit
import Compile.CompleteStrict

set_option autoImplicit false

noncomputable section

namespace Compile.CompleteAdaptive

open Iop Rom Prob Compile.Adaptive
open Compile.Glue (runLazy_pure runLazy_query)
open scoped ENNReal

/-! ## Part 1. Oracle algorithms in general -/

section Generic

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- A last step that only computes. -/
theorem runLazy_erase_bind_pure (c : Step S sp α) (h : α → β) (vs : List Bits) (T : Table S) :
    (erase (c.bind fun a => Step.pure (h a)) vs).runLazy T
      = ((erase c vs).runLazy T).map fun o => ((h o.1.1, o.1.2), o.2) := by
  rw [erase_bind, OComp.runLazy_bind]
  rfl

/-- The list of token values only grows. -/
theorem erase_prefix (c : Step S sp α) :
    ∀ (vs : List Bits) (T : Table S), ∀ out ∈ ((erase c vs).runLazy T).support, vs <+: out.1.2 := by
  induction c with
  | pure a =>
    intro vs T out ho
    simp only [erase, OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact List.prefix_rfl
  | sample n k ih =>
    intro vs T out ho
    simp only [erase, OComp.runLazy, PMF.mem_support_bind_iff] at ho
    obtain ⟨r, -, ho⟩ := ho
    exact ih r vs T out ho
  | plain o q k ih =>
    intro vs T out ho
    simp only [erase, runLazy_query, PMF.mem_support_bind_iff] at ho
    obtain ⟨a, -, ho⟩ := ho
    exact ih a.1 vs a.2 out ho
  | fresh ℓ k ih =>
    intro vs T out ho
    simp only [erase, OComp.runLazy, PMF.mem_support_bind_iff] at ho
    obtain ⟨r, -, ho⟩ := ho
    exact (List.prefix_append vs _).trans (ih _ _ T out ho)
  | marked o t us pt inj k ih =>
    intro vs T out ho
    simp only [erase, runLazy_query, PMF.mem_support_bind_iff] at ho
    obtain ⟨a, -, ho⟩ := ho
    exact (List.prefix_append vs _).trans (ih _ _ _ a.2 out ho)
  | reveal ts k ih =>
    intro vs T out ho
    simp only [erase] at ho
    exact ih _ vs T out ho

/-- "QB P c m": on every path, the algorithm c makes at most m queries to oracles with the property
P. -/
def QB (P : S.ι → Prop) : OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .query o _ k, m => (¬ P o ∧ ∀ r, QB P (k r) m) ∨ ∃ m', m = m' + 1 ∧ ∀ r, QB P (k r) m'
  | .sample _ k, m => ∀ r, QB P (k r) m

variable {P : S.ι → Prop}

theorem QB.mono {c : OComp S α} : ∀ {m m' : ℕ}, m ≤ m' → QB P c m → QB P c m' := by
  induction c with
  | pure a => intro m m' _ _; trivial
  | query o q k ih =>
    intro m m' hle h
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun r => ih r hle (h r)⟩
    · obtain ⟨m1, rfl⟩ : ∃ m1, m' = m1 + 1 := ⟨m' - 1, by omega⟩
      exact Or.inr ⟨m1, rfl, fun r => ih r (by omega) (h r)⟩
  | sample n k ih => intro m m' hle h r; exact ih r hle (h r)

theorem QB.bind {c : OComp S α} {g : α → OComp S β} {m' : ℕ} (hg : ∀ a, QB P (g a) m') :
    ∀ {m : ℕ}, QB P c m → QB P (c.bind g) (m + m') := by
  induction c with
  | pure a => intro m _; exact (hg a).mono (Nat.le_add_left _ _)
  | query o q k ih =>
    intro m h
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun r => ih r (h r)⟩
    · exact Or.inr ⟨m0 + m', by omega, fun r => ih r (h r)⟩
  | sample n k ih => intro m h r; exact ih r (h r)

/-- "TLe P T sz": the table T holds at most sz queries to oracles with the property P. -/
def TLe (P : S.ι → Prop) (T : Table S) (sz : ℕ) : Prop :=
  ∃ D : Finset (Σ o, S.Dom o),
    (∀ o q, P o → T o q ≠ none → (⟨o, q⟩ : Σ o, S.Dom o) ∈ D) ∧ D.card ≤ sz

theorem TLe.mono {T : Table S} {sz sz' : ℕ} (h : TLe P T sz) (hle : sz ≤ sz') : TLe P T sz' := by
  obtain ⟨D, hD, hc⟩ := h
  exact ⟨D, hD, hc.trans hle⟩

theorem TLe.empty : TLe P (Table.empty S) 0 := ⟨∅, fun _ _ _ h => absurd rfl h, by simp⟩

theorem set_of_ne (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) (o' : S.ι) (q' : S.Dom o')
    (h : (⟨o', q'⟩ : Σ o, S.Dom o) ≠ ⟨o, q⟩) : T.set o q r o' q' = T o' q' := by
  by_cases ho : o' = o
  · subst ho
    have hq : q' ≠ q := fun e => h (by rw [e])
    simp [Table.set, Function.update_of_ne hq]
  · simp [Table.set, Function.update_of_ne ho]

open Classical in
theorem mem_insert_of_set {T : Table S} {D : Finset (Σ o, S.Dom o)}
    (hD : ∀ o q, P o → T o q ≠ none → (⟨o, q⟩ : Σ o, S.Dom o) ∈ D) (o : S.ι)
    (q : S.Dom o) (r : S.Rng o) :
    ∀ o' q', P o' → T.set o q r o' q' ≠ none →
      (⟨o', q'⟩ : Σ o, S.Dom o) ∈ insert (⟨o, q⟩ : Σ o, S.Dom o) D := by
  intro o' q' hP h
  by_cases e : (⟨o', q'⟩ : Σ o, S.Dom o) = ⟨o, q⟩
  · rw [e]; exact Finset.mem_insert_self _ _
  · rw [set_of_ne T o q r o' q' e] at h
    exact Finset.mem_insert_of_mem (hD o' q' hP h)

theorem TLe.set {T : Table S} {sz : ℕ} (h : TLe P T sz) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    TLe P (T.set o q r) (sz + 1) := by
  classical
  obtain ⟨D, hD, hc⟩ := h
  exact ⟨insert ⟨o, q⟩ D,
    mem_insert_of_set hD o q r,
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hc)⟩

theorem set_apply_of_ne_oracle
    (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) {o' : S.ι} (h : o' ≠ o) :
    T.set o q r o' = T o' := by
  simp [Table.set, Function.update_of_ne h]

/-- An algorithm that queries no oracle with the property P leaves their part of the table as it
is. -/
theorem runLazy_eq_of_QB_zero (c : OComp S α) :
    ∀ T : Table S, QB P c 0 → ∀ out ∈ (c.runLazy T).support, ∀ o, P o → out.2 o = T o := by
  induction c with
  | pure a =>
    intro T _ out ho o _
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at ho
    rw [ho]
  | query o q k ih =>
    intro T h out ho o' hP
    rcases h with ⟨hn, h⟩ | ⟨m0, h0, -⟩
    · simp only [OComp.runLazy] at ho
      cases hT : T o q with
      | some r =>
        simp only [hT] at ho
        exact ih r T (h r) out ho o' hP
      | none =>
        simp only [hT, PMF.mem_support_bind_iff] at ho
        obtain ⟨r, -, ho⟩ := ho
        rw [ih r _ (h r) out ho o' hP]
        exact set_apply_of_ne_oracle T o q r fun e => hn (e ▸ hP)
    · omega
  | sample n k ih =>
    intro T h out ho o hP
    simp only [OComp.runLazy, PMF.mem_support_bind_iff] at ho
    obtain ⟨r, -, ho⟩ := ho
    exact ih r T (h r) out ho o hP

/-- A lazy run adds at most as many entries as it makes queries. -/
theorem runLazy_TLe (c : OComp S α) : ∀ (m : ℕ) (T : Table S) (sz : ℕ), QB P c m → TLe P T sz →
    ∀ out ∈ (c.runLazy T).support, TLe P out.2 (sz + m) := by
  induction c with
  | pure a =>
    intro m T sz _ hT out ho
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at ho
    rw [ho]
    exact hT.mono (Nat.le_add_right _ _)
  | query o q k ih =>
    intro m T sz h hT out ho
    simp only [OComp.runLazy] at ho
    cases hq : T o q with
    | some r =>
      simp only [hq] at ho
      rcases h with ⟨-, h⟩ | ⟨m0, rfl, h⟩
      · exact ih r m T sz (h r) hT out ho
      · exact (ih r m0 T sz (h r) hT out ho).mono (by omega)
    | none =>
      simp only [hq, PMF.mem_support_bind_iff] at ho
      obtain ⟨r, -, ho⟩ := ho
      rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
      · refine ih r m _ sz (h r) ?_ out ho
        obtain ⟨D, hD, hc⟩ := hT
        refine ⟨D, fun o' q' hP hne => hD o' q' hP ?_, hc⟩
        rwa [set_apply_of_ne_oracle T o q r fun e => hn (e ▸ hP)] at hne
      · exact (ih r m0 _ (sz + 1) (h r) (hT.set o q r) out ho).mono (by omega)
  | sample n k ih =>
    intro m T sz h hT out ho
    simp only [OComp.runLazy, PMF.mem_support_bind_iff] at ho
    obtain ⟨r, -, ho⟩ := ho
    exact ih r m T sz (h r) hT out ho

/-- If no point is related to two values c, then at most card D values are related to a point of
D. -/
theorem cnt_rel_le {C Pt : Type} [Fintype C] (D : Finset Pt) (rel : C → Pt → Prop)
    (hinj : ∀ c c' x, rel c x → rel c' x → c = c') : cnt (fun c => ∃ x ∈ D, rel c x) ≤ D.card := by
  classical
  refine cnt_le_of_forall_finset fun Y hY => ?_
  rcases Y.eq_empty_or_nonempty with rfl | ⟨y0, hy0⟩
  · simp
  obtain ⟨x0, -, -⟩ := hY y0 hy0
  haveI : Nonempty Pt := ⟨x0⟩
  choose! g hg using hY
  exact Finset.card_le_card_of_injOn g (fun y hy => (hg y hy).1)
    fun y hy y' hy' e => hinj y y' (g y) (hg y hy).2 (e ▸ (hg y' hy').2)

end Generic

/-! ### The same count for token programs -/

section StepCount

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- "SQB P c m": on every path, the program c makes at most m queries, plain or marked, to oracles
with the property P. -/
def SQB (P : S.ι → Prop) : Step S sp α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ k, m => ∀ r, SQB P (k r) m
  | .plain o _ k, m => (¬ P o ∧ ∀ r, SQB P (k r) m) ∨ ∃ m', m = m' + 1 ∧ ∀ r, SQB P (k r) m'
  | .fresh _ k, m => ∀ t, SQB P (k t) m
  | .marked o _ _ _ _ k, m => (¬ P o ∧ ∀ v t, SQB P (k v t) m) ∨ ∃ m', m = m' + 1 ∧ ∀ v t, SQB P (k v t) m'
  | .reveal _ k, m => ∀ vs, SQB P (k vs) m

variable {P : S.ι → Prop}

theorem SQB.erase {c : Step S sp α} : ∀ {m : ℕ}, SQB P c m → ∀ vs, QB P (erase c vs) m := by
  induction c with
  | pure a => intro m _ vs; trivial
  | sample n k ih => intro m h vs r; exact ih r (h r) vs
  | plain o q k ih =>
    intro m h vs
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun r => ih r (h r) vs⟩
    · exact Or.inr ⟨m0, rfl, fun r => ih r (h r) vs⟩
  | fresh ℓ k ih => intro m h vs r; exact ih _ (h _) _
  | marked o t us pt inj k ih =>
    intro m h vs
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun r => ih _ _ (h _ _) _⟩
    · exact Or.inr ⟨m0, rfl, fun r => ih _ _ (h _ _) _⟩
  | reveal ts k ih => intro m h vs; exact ih _ (h _) vs

theorem SQB.mono {c : Step S sp α} : ∀ {m m' : ℕ}, m ≤ m' → SQB P c m → SQB P c m' := by
  induction c with
  | pure a => intro m m' _ _; trivial
  | sample n k ih => intro m m' hle h r; exact ih r hle (h r)
  | plain o q k ih =>
    intro m m' hle h
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun r => ih r hle (h r)⟩
    · obtain ⟨m1, rfl⟩ : ∃ m1, m' = m1 + 1 := ⟨m' - 1, by omega⟩
      exact Or.inr ⟨m1, rfl, fun r => ih r (by omega) (h r)⟩
  | fresh ℓ k ih => intro m m' hle h t; exact ih t hle (h t)
  | marked o t us pt inj k ih =>
    intro m m' hle h
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun v t' => ih v t' hle (h v t')⟩
    · obtain ⟨m1, rfl⟩ : ∃ m1, m' = m1 + 1 := ⟨m' - 1, by omega⟩
      exact Or.inr ⟨m1, rfl, fun v t' => ih v t' (by omega) (h v t')⟩
  | reveal ts k ih => intro m m' hle h vs; exact ih vs hle (h vs)

theorem SQB.bind {c : Step S sp α} {g : α → Step S sp β} {m' : ℕ} (hg : ∀ a, SQB P (g a) m') :
    ∀ {m : ℕ}, SQB P c m → SQB P (c.bind g) (m + m') := by
  induction c with
  | pure a => intro m _; exact (hg a).mono (Nat.le_add_left _ _)
  | sample n k ih => intro m h r; exact ih r (h r)
  | plain o q k ih =>
    intro m h
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun r => ih r (h r)⟩
    · exact Or.inr ⟨m0 + m', by omega, fun r => ih r (h r)⟩
  | fresh ℓ k ih => intro m h t; exact ih t (h t)
  | marked o t us pt inj k ih =>
    intro m h
    rcases h with ⟨hn, h⟩ | ⟨m0, rfl, h⟩
    · exact Or.inl ⟨hn, fun v t' => ih v t' (h v t')⟩
    · exact Or.inr ⟨m0 + m', by omega, fun v t' => ih v t' (h v t')⟩
  | reveal ts k ih => intro m h vs; exact ih vs (h vs)

/-- two programs without such queries, one after the other -/
theorem SQB.bind0 {c : Step S sp α} {g : α → Step S sp β}
    (hc : SQB P c 0) (hg : ∀ a, SQB P (g a) 0) : SQB P (c.bind g) 0 :=
  SQB.bind hg hc

end StepCount

/-! ## Part 2. One round, in plain types, and small facts -/

section Chain

theorem pr_runLazy_query_none {S : OSpec} {α : Type} {o : S.ι} {q : S.Dom o}
    {k : S.Rng o → OComp S α} {T : Table S} (h : T o q = none) (E : Set (α × Table S)) :
    pr ((OComp.query o q k).runLazy T) E =
      expect (unif (S.Rng o)) fun r => pr ((k r).runLazy (T.set o q r)) E := by
  simp only [OComp.runLazy, h, pr_bind]

/-- One round, in plain types (hypotheses below). The answer is a uniform pair (a, b). Its first
part gives the verifier message chal a, which is uniform.
Unless b is bad, what follows has the right law up to e. Then the average of F is at most Pr[b bad]
+ Pr[E] + e. -/
theorem avg_step {A B C R : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C]
    [Nonempty C] [Fintype R] [Nonempty R] (chal : A → C) (hch : (unif A).map chal = unif C)
    (E : Set (C × R)) (Bad : Set B) (e : ℝ≥0∞) (F : A × B → ℝ≥0∞)
    (hF : ∀ r, r.2 ∉ Bad → F r ≤ pr (unif R) {ρ | (chal r.1, ρ) ∈ E} + e) (hF1 : ∀ r, F r ≤ 1) :
    expect (unif (A × B)) F ≤ pr (unif B) Bad + (pr (unif (C × R)) E + e) := by
  classical
  have h1 : ∀ r : A × B,
      F r ≤ (if r.2 ∈ Bad then 1 else 0) + (pr (unif R) {ρ | (chal r.1, ρ) ∈ E} + e) := by
    intro r
    by_cases hr : r.2 ∈ Bad
    · rw [if_pos hr]; exact (hF1 r).trans le_self_add
    · rw [if_neg hr, zero_add]; exact hF r hr
  refine (expect_mono _ h1).trans (le_of_eq ?_)
  rw [expect_add, expect_add, expect_const]
  congr 1
  · rw [← map_snd_unif (C := A) (D := B), pr_eq_expect, expect_map]
  · congr 1
    rw [unif_prod (C := C) (D := R), pr_prod, ← hch, expect_map,
      ← map_fst_unif (C := A) (D := B), expect_map]

variable {I X : Type} {lam K : ℕ}

theorem card_dig : (Fintype.card (Dig lam) : ℝ≥0∞) = 2 ^ lam := by
  simp [Dig]

theorem prRho_nil_of_mem {E : Set (Rho [])} (h : () ∈ E) : prRho E = 1 :=
  pr_eq_one_of_support_subset _ fun u _ => by cases u; exact h

end Chain

/-! ## Part 3. What comes first; the bits of a number -/

section Prove

/-- An event about what comes first. -/
theorem pr_bind_le_pr {α β : Type} (p : PMF α) (g : α → PMF β) (E : Set β) (E' : Set α)
    (h : ∀ a ∈ p.support, ∀ b ∈ (g a).support, b ∈ E → a ∈ E') : pr (p.bind g) E ≤ pr p E' := by
  classical
  rw [pr_bind, pr_eq_expect p E']
  refine expect_mono_support _ fun a ha => ?_
  by_cases hE : a ∈ E'
  · rw [if_pos hE]; exact pr_le_one _ _
  · rw [if_neg hE]
    exact le_of_eq (pr_eq_zero_of_forall_not_mem _ fun b hb hbE => hE (h a ha b hb hbE))

/-- The ℓ bits of a number below 2^ℓ determine it. -/
theorem bits_injective (ℓ : ℕ) :
    Function.Injective fun r : Fin (2 ^ ℓ - 1 + 1) =>
      List.ofFn fun i : Fin ℓ => r.val.testBit i := by
  intro r r' h
  have h1 := List.ofFn_injective h
  have hlt : ∀ x : Fin (2 ^ ℓ - 1 + 1), x.val < 2 ^ ℓ := fun x => by
    have := x.2
    have h2 : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
    omega
  refine Fin.ext (Nat.eq_of_testBit_eq fun i => ?_)
  by_cases hi : i < ℓ
  · exact congrFun h1 ⟨i, hi⟩
  · have hle : 2 ^ ℓ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)
    rw [Nat.testBit_lt_two_pow ((hlt r).trans_le hle),
      Nat.testBit_lt_two_pow ((hlt r').trans_le hle)]

end Prove

/-! ## Part 4. A last step that only computes; a hash term -/

section Star

theorem runLazy_bind_pure {S : OSpec} {α β : Type} (c : OComp S α) (h : α → β) (T : Table S) :
    (c.bind fun a => pure (h a)).runLazy T = (c.runLazy T).map fun o => (h o.1, o.2) := by
  rw [OComp.runLazy_bind]
  rfl

variable {I X : Type} {lam : ℕ} (p : Params)

/-- the hash term of l queries, each among at most S queries in the table -/
def hsh (lam : ℕ) (p : Params) (l S : ℕ) : ℝ≥0∞ := ((l * S : ℕ) : ℝ≥0∞) / 2 ^ (min p.sFS lam)

theorem hsh_mono (l : ℕ) {a S : ℕ} (h : a ≤ S) :
    ((l * a : ℕ) : ℝ≥0∞) / 2 ^ (min p.sFS lam) ≤ hsh lam p l S :=
  ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.mul_le_mul_left l h)) _

end Star

/-! ## Part 5. One lazy answer; expectations -/

section Notice

theorem TLe_lazyAnswer {S : OSpec} {P : S.ι → Prop} {T : Table S} {sz : ℕ} (hT : TLe P T sz)
    (o : S.ι) (q : S.Dom o) :
    ∀ a ∈ (lazyAnswer T o q).support, TLe P a.2 (sz + 1) := by
  intro a ha
  unfold lazyAnswer at ha
  split at ha
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at ha
    rw [ha]
    exact hT.mono (Nat.le_succ _)
  · rw [PMF.mem_support_map_iff] at ha
    obtain ⟨r, -, rfl⟩ := ha
    exact hT.set o q r

theorem expect_le_pr_add_expect {α : Type} (p : PMF α) (F G : α → ℝ≥0∞) (B : Set α)
    (h1 : ∀ a ∈ p.support, a ∈ B → F a ≤ 1 + G a) (h : ∀ a ∈ p.support, a ∉ B → F a ≤ G a) :
    expect p F ≤ pr p B + expect p G := by
  classical
  rw [pr_eq_expect, ← expect_add]
  refine expect_mono_support _ fun a ha => ?_
  by_cases hB : a ∈ B
  · rw [if_pos hB]; exact h1 a ha hB
  · rw [if_neg hB, zero_add]; exact h a ha hB

theorem expect_pr_comm {α β : Type} (p : PMF α) (q : PMF β) (R : α → β → Prop) :
    expect p (fun a => pr q {b | R a b}) = expect q fun b => pr p {a | R a b} := by
  simp only [pr_eq_expect]
  exact expect_comm p q _

end Notice

end Compile.CompleteAdaptive

/-! ## Part 6. Sequences that agree on the support -/

namespace Compile.CompleteAdaptive

open Iop Rom Prob Compile.Adaptive
open Compile.Glue (runLazy_pure runLazy_query)
open scoped ENNReal

section GlueA

theorem bind_congr_support {α β : Type} (p : PMF α)
    {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g :=
  ext_of_expect fun F => by
    rw [expect_bind, expect_bind]
    exact expect_congr_support p fun a ha => by rw [h a ha]

end GlueA

end Compile.CompleteAdaptive

/-! ## Part 7. The property implies completeness -/

namespace Compile

open Iop Rom Prob
open scoped ENNReal

namespace Adaptive

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

/-- Sanity. The property implies completeness in the sense of `ZKCP.Gen.HasCompletenessError`, for
batches of at most one pair, with the error at no queries and one session. -/
theorem completeness_of_adaptive (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf)
    (R : ZKCP.Gen.RelPair I X Wn PP) (α : ℕ → ℕ → ℝ≥0∞) (h : HasAdaptiveCompleteness A R α) :
    ZKCP.Gen.HasCompletenessError R A 1 (α 0 1) := by
  intro i b hb
  rcases b with _ | ⟨⟨x, w⟩, _ | ⟨y, b'⟩⟩
  · have e : ZKCP.Gen.completenessExp A i [] =
        (A.C i).bind fun key => (A.P key.2 []).bind fun _ => pure true := rfl
    refine le_trans (le_of_eq ?_) (zero_le _)
    rw [e]
    unfold Rom.Pr Rom.PrCoins
    refine (MeasureTheory.lintegral_congr fun f => ?_).trans MeasureTheory.lintegral_zero
    refine pr_eq_zero_of_forall_not_mem _ fun out ho => ?_
    simp only [OComp.runEager_bind, PMF.mem_support_bind_iff] at ho
    obtain ⟨_, -, _, -, ho⟩ := ho
    have ho' : out ∈ (PMF.pure true : PMF Bool).support := ho
    simp only [PMF.support_pure, Set.mem_singleton_iff] at ho'
    simp [ho']
  · have key : ∀ (ivk : IVK) (πs : ZKCP.Gen.Slots Pf [(x, w)]),
        ZKCP.Gen.verifyAll A ivk (([(x, w)].map Prod.fst).zip πs.val) =
            (A.V ivk x (one πs)).bind fun c =>
              (pure true : OComp S Bool).bind fun rest => pure (c && rest) := by
      rintro ivk ⟨l, hl⟩
      rcases l with _ | ⟨π, _ | ⟨π', l'⟩⟩
      · simp at hl
      · rfl
      · simp at hl
    have e : ZKCP.Gen.completenessExp A i [(x, w)] =
        exp A (fun _ => .session x w fun _ _ => .halt) i 1 := by
      have e1 : ZKCP.Gen.completenessExp A i [(x, w)] = (A.C i).bind fun k => (A.P k.2 [(x, w)]).bind fun πs =>
          ZKCP.Gen.verifyAll A k.1 (([(x, w)].map Prod.fst).zip πs.val) := rfl
      rw [e1]
      simp only [key]
      rfl
    rw [e]
    exact h i 0 1 _ (fun _ _ _ => trivial) fun _ => ⟨hb.2 (x, w) (by simp), fun _ _ => trivial⟩
  · have := hb.1
    simp at this

end Adaptive

end Compile
