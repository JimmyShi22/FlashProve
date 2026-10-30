-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Derive.lean: lemmas for deriving the committer's coins from one seed through an auxiliary random
oracle (Rom/SpecDerive.lean). The theorem is in Rom/DeriveWith.lean (`deriveWith`).

The lemmas are for one seed, counters as labels, and all coins of the committer. All experiments are
run with lazily sampled oracles (`Pr_eq_law`, Rom/EagerLazy.lean).

  1  Tables. With derived coins the table of lazy sampling is `glue s T R`: a table T, overlaid at
     the queries of the seed s by a record R : ℕ → Option (answer).
  2  `runRec`: an algorithm run on (T, R), its j-th sample read from the record, or sampled and
     recorded. For an algorithm that avoids the auxiliary oracle: the derived algorithm on
     `glue s T R` is `runRec` (`runLazy_derive`), and the algorithm itself does not see the overlay
     (`runLazy_glue`).
  3  `runRec_again` ((Use): so called in the head of Rom/SpecDerive.lean): a second run.
  4  `runB`: the run with ψ-biased coins; `map_runRec`, `tv_runB_le`.
  5  Completeness.
  6  Privacy: identical until the adversary makes a query of the seed; a trace of t queries meets at
     most t seeds.
-/
import Rom.SpecDerive
import Rom.EagerLazy
import Rom.Bridge
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob

namespace Rom
namespace Derive

variable {S : OSpec} {α β : Type} (σ : SeedOracle S)

/-! ## 1. Tables -/

/-- the record of the derived answers: at the counter j the answer of the auxiliary oracle at the
query (s, j), once it is fixed -/
abbrev Rec (σ : SeedOracle S) : Type := ℕ → Option (S.Rng σ.o)

/-- q is a query of the seed s -/
def IsPt (s : Fin (σ.sd + 1)) (q : S.Dom σ.o) : Prop := ∃ j, q = σ.pt s j

open Classical in
/-- The table of lazy sampling with derived coins: T, overlaid at the queries of the seed s by the
record R. -/
def glue (s : Fin (σ.sd + 1)) (T : Table S) (R : Rec σ) : Table S :=
  Function.update T σ.o fun q => if h : IsPt σ s q then R h.choose else T σ.o q

variable {σ} {s : Fin (σ.sd + 1)} {T : Table S} {R : Rec σ}

theorem glue_of_ne {o : S.ι} (h : o ≠ σ.o) : glue σ s T R o = T o := Function.update_of_ne h _ _

theorem glue_pt (j : ℕ) : glue σ s T R σ.o (σ.pt s j) = R j := by
  have h : IsPt σ s (σ.pt s j) := ⟨j, rfl⟩
  unfold glue
  rw [Function.update_self, dif_pos h]
  exact congrArg R (σ.inj _ _ _ _ h.choose_spec).2.symm

theorem glue_not_pt {q : S.Dom σ.o} (h : ¬ IsPt σ s q) : glue σ s T R σ.o q = T σ.o q := by
  unfold glue
  rw [Function.update_self, dif_neg h]

theorem set_of_ne_oracle (T : Table S) {o o' : S.ι} (h : o' ≠ o) (q : S.Dom o) (r : S.Rng o) :
    T.set o q r o' = T o' :=
  Function.update_of_ne h _ _

theorem set_same (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    T.set o q r o q = some r := by
  simp [Table.set]

theorem set_of_ne_point (T : Table S) (o : S.ι) {q q' : S.Dom o} (h : q' ≠ q) (r : S.Rng o) :
    T.set o q r o q' = T o q' := by
  simp [Table.set, Function.update_of_ne h]

theorem glue_set_of_ne {o : S.ι} (h : o ≠ σ.o) (q : S.Dom o) (r : S.Rng o) :
    (glue σ s T R).set o q r = glue σ s (T.set o q r) R := by
  funext o'
  by_cases ho : o' = σ.o
  · subst ho
    rw [set_of_ne_oracle _ (Ne.symm h)]
    funext q'
    by_cases hq : IsPt σ s q'
    · obtain ⟨j, rfl⟩ := hq
      rw [glue_pt, glue_pt]
    · rw [glue_not_pt hq, glue_not_pt hq, set_of_ne_oracle _ (Ne.symm h)]
  · rw [glue_of_ne ho]
    by_cases ho' : o' = o
    · subst ho'
      funext q'
      by_cases hq : q' = q
      · subst hq; rw [set_same, set_same]
      · rw [set_of_ne_point _ _ hq, set_of_ne_point _ _ hq, glue_of_ne ho]
    · rw [set_of_ne_oracle _ ho', set_of_ne_oracle _ ho', glue_of_ne ho]

theorem glue_set_not_pt {q : S.Dom σ.o} (h : ¬ IsPt σ s q) (r : S.Rng σ.o) :
    (glue σ s T R).set σ.o q r = glue σ s (T.set σ.o q r) R := by
  funext o'
  by_cases ho : o' = σ.o
  · subst ho
    funext q'
    by_cases hq' : q' = q
    · subst hq'; rw [set_same, glue_not_pt h, set_same]
    · rw [set_of_ne_point _ _ hq']
      by_cases hp : IsPt σ s q'
      · obtain ⟨j, rfl⟩ := hp
        rw [glue_pt, glue_pt]
      · rw [glue_not_pt hp, glue_not_pt hp, set_of_ne_point _ _ hq']
  · rw [set_of_ne_oracle _ ho, glue_of_ne ho, glue_of_ne ho, set_of_ne_oracle _ ho]

theorem glue_set_pt (j : ℕ) (d : S.Rng σ.o) :
    (glue σ s T R).set σ.o (σ.pt s j) d = glue σ s T (Function.update R j (some d)) := by
  funext o'
  by_cases ho : o' = σ.o
  · subst ho
    funext q'
    by_cases hp : IsPt σ s q'
    · obtain ⟨j', rfl⟩ := hp
      rw [glue_pt]
      by_cases hj : j' = j
      · subst hj; rw [set_same, Function.update_self]
      · rw [set_of_ne_point _ _ (fun e => hj (σ.inj _ _ _ _ e).2),
          glue_pt, Function.update_of_ne hj]
    · rw [glue_not_pt hp, set_of_ne_point _ _ (fun e => hp ⟨j, e⟩), glue_not_pt hp]
  · rw [set_of_ne_oracle _ ho, glue_of_ne ho, glue_of_ne ho]

theorem glue_empty (s : Fin (σ.sd + 1)) :
    glue σ s (Table.empty S) (fun _ => none) = Table.empty S := by
  funext o'
  by_cases ho : o' = σ.o
  · subst ho
    funext q'
    by_cases hp : IsPt σ s q'
    · obtain ⟨j, rfl⟩ := hp
      rw [glue_pt]; rfl
    · rw [glue_not_pt hp]
  · rw [glue_of_ne ho]

/-- every entry of T is an entry of T' -/
def Sub (T T' : Table S) : Prop := ∀ o q r, T o q = some r → T' o q = some r

theorem Sub.refl (T : Table S) : Sub T T := fun _ _ _ h => h
theorem Sub.trans {T T' T'' : Table S} (h : Sub T T') (h' : Sub T' T'') : Sub T T'' :=
  fun o q r hr => h' o q r (h o q r hr)

theorem sub_set {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none) (r : S.Rng o) :
    Sub T (T.set o q r) := by
  intro o' q' r' h'
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq; rw [h] at h'; cases h'
    · rw [set_of_ne_point _ _ hq]; exact h'
  · rw [set_of_ne_oracle _ ho]; exact h'

/-- every entry of R is an entry of R' -/
def SubR (R R' : Rec σ) : Prop := ∀ j d, R j = some d → R' j = some d

theorem SubR.refl (R : Rec σ) : SubR R R := fun _ _ h => h
theorem SubR.trans {R R' R'' : Rec σ} (h : SubR R R') (h' : SubR R' R'') : SubR R R'' :=
  fun j d hd => h' j d (h j d hd)

theorem subR_update {R : Rec σ} {j : ℕ} (h : R j = none) (d : S.Rng σ.o) :
    SubR R (Function.update R j (some d)) := by
  intro j' d' h'
  by_cases hj : j' = j
  · subst hj; rw [h] at h'; cases h'
  · rw [Function.update_of_ne hj]; exact h'

/-! ## 2. Runs on a table and a record -/

variable (σ)

/-- The run on (T, R): oracle queries from T, lazily; in place of the j-th uniform sample it takes ψ
of the record at j, which is sampled and recorded if it is not there. -/
def runRec : OComp S α → ℕ → Table S → Rec σ → PMF (α × Table S × Rec σ)
  | .pure a, _, T, R => PMF.pure (a, T, R)
  | .query o q k, j, T, R =>
      match T o q with
      | some r => runRec (k r) j T R
      | none => (PMF.uniformOfFintype (S.Rng o)).bind fun r => runRec (k r) j (T.set o q r) R
  | .sample n k, j, T, R =>
      match R j with
      | some d => runRec (k (σ.ψ n d)) (j + 1) T R
      | none =>
        (PMF.uniformOfFintype (S.Rng σ.o)).bind fun d =>
          runRec (k (σ.ψ n d)) (j + 1) T (Function.update R j (some d))

/-- For an algorithm that avoids the auxiliary oracle: the derived algorithm on `glue s T R` is the
run on (T, R). -/
theorem runLazy_derive (s : Fin (σ.sd + 1)) (c : OComp S α) :
    c.Avoids σ.o →
    ∀ (j : ℕ) (T : Table S) (R : Rec σ), (c.derive σ s j).runLazy (glue σ s T R) =
      (runRec σ c j T R).map fun x => (x.1, glue σ s x.2.1 x.2.2) := by
  induction c with
  | pure a =>
    intro _ j T R
    simp only [OComp.derive, OComp.runLazy, runRec, PMF.pure_map]
  | query o q k ih =>
    intro hc j T R
    have hg : glue σ s T R o q = T o q := congrFun (glue_of_ne hc.1) q
    cases hT : T o q with
    | some r =>
      simp only [OComp.derive, OComp.runLazy, runRec, hg, hT]
      exact ih r (hc.2 r) j T R
    | none =>
      simp only [OComp.derive, OComp.runLazy, runRec, hg, hT, PMF.map_bind]
      refine congrArg _ (funext fun r => ?_)
      rw [glue_set_of_ne hc.1]
      exact ih r (hc.2 r) j _ R
  | sample n k ih =>
    intro hc j T R
    have hg : glue σ s T R σ.o (σ.pt s j) = R j := glue_pt j
    cases hR : R j with
    | some d =>
      simp only [OComp.derive, OComp.runLazy, runRec, hg, hR]
      exact ih _ (hc _) (j + 1) T R
    | none =>
      simp only [OComp.derive, OComp.runLazy, runRec, hg, hR, PMF.map_bind]
      refine congrArg _ (funext fun d => ?_)
      rw [glue_set_pt]
      exact ih _ (hc _) (j + 1) T _

/-- An algorithm that avoids the auxiliary oracle does not see the overlay. -/
theorem runLazy_glue (s : Fin (σ.sd + 1)) (c : OComp S α) :
    c.Avoids σ.o →
    ∀ (T : Table S) (R : Rec σ),
      c.runLazy (glue σ s T R) = (c.runLazy T).map fun x => (x.1, glue σ s x.2 R) := by
  induction c with
  | pure a =>
    intro _ T R
    simp only [OComp.runLazy, PMF.pure_map]
  | query o q k ih =>
    intro hc T R
    have hg : glue σ s T R o q = T o q := congrFun (glue_of_ne hc.1) q
    cases hT : T o q with
    | some r =>
      simp only [OComp.runLazy, hg, hT]
      exact ih r (hc.2 r) T R
    | none =>
      simp only [OComp.runLazy, hg, hT, PMF.map_bind]
      refine congrArg _ (funext fun r => ?_)
      rw [glue_set_of_ne hc.1]
      exact ih r (hc.2 r) _ R
  | sample n k ih =>
    intro hc T R
    simp only [OComp.runLazy, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r (hc r) T R)

/-- a lazy run only adds entries -/
theorem runLazy_sub (c : OComp S α) : ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support, Sub T x.2 := by
  induction c with
  | pure a =>
    intro T x hx
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact Sub.refl T
  | query o q k ih =>
    intro T x hx
    cases hT : T o q with
    | some r =>
      simp only [OComp.runLazy, hT] at hx
      exact ih r T x hx
    | none =>
      simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact (sub_set hT r).trans (ih r _ x hx)
  | sample n k ih =>
    intro T x hx
    simp only [OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    exact ih r T x hx

theorem runLazy_avoids (o₀ : S.ι) (c : OComp S α) :
    c.Avoids o₀ → ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support, x.2 o₀ = T o₀ := by
  induction c with
  | pure a =>
    intro _ T x hx
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | query o q k ih =>
    intro hc T x hx
    cases hT : T o q with
    | some r =>
      simp only [OComp.runLazy, hT] at hx
      exact ih r (hc.2 r) T x hx
    | none =>
      simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      rw [ih r (hc.2 r) _ x hx, set_of_ne_oracle _ (Ne.symm hc.1)]
  | sample n k ih =>
    intro hc T x hx
    simp only [OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    exact ih r (hc r) T x hx

/-! ## 3. A second run -/

/-- a run on (T, R) only adds entries -/
theorem runRec_sub (c : OComp S α) :
    ∀ (j : ℕ) (T : Table S) (R : Rec σ),
      ∀ x ∈ (runRec σ c j T R).support, Sub T x.2.1 ∧ SubR R x.2.2 := by
  induction c with
  | pure a =>
    intro j T R x hx
    simp only [runRec, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; exact ⟨Sub.refl T, SubR.refl R⟩
  | query o q k ih =>
    intro j T R x hx
    cases hT : T o q with
    | some r =>
      simp only [runRec, hT] at hx
      exact ih r j T R x hx
    | none =>
      simp only [runRec, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact ⟨(sub_set hT r).trans (ih r j _ R x hx).1, (ih r j _ R x hx).2⟩
  | sample n k ih =>
    intro j T R x hx
    cases hR : R j with
    | some d =>
      simp only [runRec, hR] at hx
      exact ih _ (j + 1) T R x hx
    | none =>
      simp only [runRec, hR, PMF.mem_support_bind_iff] at hx
      obtain ⟨d, -, hx⟩ := hx
      exact ⟨(ih _ (j + 1) T _ x hx).1, (subR_update hR d).trans (ih _ (j + 1) T _ x hx).2⟩

theorem runRec_avoids (o₀ : S.ι) (c : OComp S α) :
    c.Avoids o₀ →
    ∀ (j : ℕ) (T : Table S) (R : Rec σ), ∀ x ∈ (runRec σ c j T R).support, x.2.1 o₀ = T o₀ := by
  induction c with
  | pure a =>
    intro _ j T R x hx
    simp only [runRec, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | query o q k ih =>
    intro hc j T R x hx
    cases hT : T o q with
    | some r =>
      simp only [runRec, hT] at hx
      exact ih r (hc.2 r) j T R x hx
    | none =>
      simp only [runRec, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      rw [ih r (hc.2 r) j _ R x hx, set_of_ne_oracle _ (Ne.symm hc.1)]
  | sample n k ih =>
    intro hc j T R x hx
    cases hR : R j with
    | some d =>
      simp only [runRec, hR] at hx
      exact ih _ (hc _) (j + 1) T R x hx
    | none =>
      simp only [runRec, hR, PMF.mem_support_bind_iff] at hx
      obtain ⟨d, -, hx⟩ := hx
      exact ih _ (hc _) (j + 1) T _ x hx

/-- (Use): a second run, on any table and record that contain those which the first run returns,
returns the same result and changes nothing. -/
theorem runRec_again (c : OComp S α) :
    ∀ (j : ℕ) (T : Table S) (R : Rec σ), ∀ x ∈ (runRec σ c j T R).support,
      ∀ (T₃ : Table S) (R₃ : Rec σ),
        Sub x.2.1 T₃ → SubR x.2.2 R₃ → runRec σ c j T₃ R₃ = PMF.pure (x.1, T₃, R₃) := by
  induction c with
  | pure a =>
    intro j T R x hx T₃ R₃ _ _
    simp only [runRec, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]; rfl
  | query o q k ih =>
    intro j T R x hx T₃ R₃ hT₃ hR₃
    cases hT : T o q with
    | some r =>
      simp only [runRec, hT] at hx
      have h3 : T₃ o q = some r := hT₃ o q r ((runRec_sub σ (k r) j T R x hx).1 o q r hT)
      simp only [runRec, h3]
      exact ih r j T R x hx T₃ R₃ hT₃ hR₃
    | none =>
      simp only [runRec, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      have h3 : T₃ o q = some r :=
        hT₃ o q r ((runRec_sub σ (k r) j _ R x hx).1 o q r (set_same T o q r))
      simp only [runRec, h3]
      exact ih r j _ R x hx T₃ R₃ hT₃ hR₃
  | sample n k ih =>
    intro j T R x hx T₃ R₃ hT₃ hR₃
    cases hR : R j with
    | some d =>
      simp only [runRec, hR] at hx
      have h3 : R₃ j = some d := hR₃ j d ((runRec_sub σ _ (j + 1) T R x hx).2 j d hR)
      simp only [runRec, h3]
      exact ih _ (j + 1) T R x hx T₃ R₃ hT₃ hR₃
    | none =>
      simp only [runRec, hR, PMF.mem_support_bind_iff] at hx
      obtain ⟨d, -, hx⟩ := hx
      have h3 : R₃ j = some d :=
        hR₃ j d ((runRec_sub σ _ (j + 1) T _ x hx).2 j d (Function.update_self j _ R))
      simp only [runRec, h3]
      exact ih _ (j + 1) T _ x hx T₃ R₃ hT₃ hR₃

/-! ## 4. Biased coins -/

/-- The run with ψ-biased coins: each sample is ψ of a fresh uniform answer. -/
def runB : OComp S α → Table S → PMF (α × Table S)
  | .pure a, T => PMF.pure (a, T)
  | .query o q k, T =>
      match T o q with
      | some r => runB (k r) T
      | none => (PMF.uniformOfFintype (S.Rng o)).bind fun r => runB (k r) (T.set o q r)
  | .sample n k, T => (PMF.uniformOfFintype (S.Rng σ.o)).bind fun d => runB (k (σ.ψ n d)) T

/-- Without its record, a run on (T, R) whose record is empty from the counter j on is the run with
biased coins. -/
theorem map_runRec (c : OComp S α) :
    ∀ (j : ℕ) (T : Table S) (R : Rec σ), (∀ j', j ≤ j' → R j' = none) →
      (runRec σ c j T R).map (fun x => (x.1, x.2.1)) = runB σ c T := by
  induction c with
  | pure a =>
    intro j T R _
    simp only [runRec, runB, PMF.pure_map]
  | query o q k ih =>
    intro j T R hR
    cases hT : T o q with
    | some r =>
      simp only [runRec, runB, hT]
      exact ih r j T R hR
    | none =>
      simp only [runRec, runB, hT, PMF.map_bind]
      exact congrArg _ (funext fun r => ih r j _ R hR)
  | sample n k ih =>
    intro j T R hR
    simp only [runRec, runB, hR j (le_refl j), PMF.map_bind]
    refine congrArg _ (funext fun d => ih _ (j + 1) T _ fun j' hj' => ?_)
    rw [Function.update_of_ne (by omega)]
    exact hR j' (by omega)

/-- The run with biased coins is within the path bias of the run with uniform coins (`runLazy`). -/
theorem tv_runB_le (c : OComp S α) :
    ∀ T : Table S, tv (runB σ c T) (c.runLazy T) ≤ c.pathBias σ := by
  induction c with
  | pure a =>
    intro T
    simp only [runB, OComp.runLazy, tv_self]
    exact zero_le _
  | query o q k ih =>
    intro T
    cases hT : T o q with
    | some r =>
      simp only [runB, OComp.runLazy, hT, OComp.pathBias]
      exact (ih r T).trans (le_iSup (fun r => (k r).pathBias σ) r)
    | none =>
      simp only [runB, OComp.runLazy, hT, OComp.pathBias]
      exact tv_bind_right_le_of_forall _ _ _ fun r _ =>
        (ih r _).trans (le_iSup (fun r => (k r).pathBias σ) r)
  | sample n k ih =>
    intro T
    simp only [runB, OComp.runLazy, OComp.pathBias]
    have h1 : ((PMF.uniformOfFintype (S.Rng σ.o)).bind fun d => runB σ (k (σ.ψ n d)) T)
        = ((PMF.uniformOfFintype (S.Rng σ.o)).map (σ.ψ n)).bind fun r => runB σ (k r) T := by
      rw [PMF.bind_map]; rfl
    rw [h1]
    exact tv_bind_le_of_forall _ _ _ _ fun r =>
      (ih r T).trans (le_iSup (fun r => (k r).pathBias σ) r)

theorem bind_congr_support {γ δ : Type} {p : PMF γ}
    {g g' : γ → PMF δ} (h : ∀ a ∈ p.support, g a = g' a) : p.bind g = p.bind g' := by
  refine PMF.ext fun b => ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ((p.mem_support_iff a).2 ha)]

/-! ## 5. Completeness -/

open ZKCP

variable {σ}
variable {I X W PP IVK ISK Pf : Type}

theorem Avoids.bind {o₀ : S.ι} {c : OComp S α} {g : α → OComp S β}
    (hc : c.Avoids o₀) (hg : ∀ a, (g a).Avoids o₀) : (c.bind g).Avoids o₀ := by
  induction c with
  | pure a => exact hg a
  | query o q k ih => exact ⟨hc.1, fun r => ih r (hc.2 r)⟩
  | sample n k ih => exact fun r => ih r (hc r)

theorem map_fst_runLazy_bind (c : OComp S α) (g : α → OComp S β) (T : Table S) :
    ((c.bind g).runLazy T).map Prod.fst =
      (c.runLazy T).bind fun x => ((g x.1).runLazy x.2).map Prod.fst := by
  rw [OComp.runLazy_bind, PMF.map_bind]

variable (A : Gen.Arg S I X W IVK ISK Pf)

theorem verifyAll_derived (σ : SeedOracle S) (ivk : IVK) :
    ∀ l : List (X × Pf), Gen.verifyAll (derived A σ) ivk l = Gen.verifyAll A ivk l
  | [] => rfl
  | (x, π) :: rest => by
      simp only [Gen.verifyAll, verifyAll_derived σ ivk rest]
      rfl

theorem avoids_verifyAll {o₀ : S.ι} (hA : ArgAvoids A o₀) (ivk : IVK) :
    ∀ l : List (X × Pf), (Gen.verifyAll A ivk l).Avoids o₀
  | [] => trivial
  | (x, π) :: rest =>
    Avoids.bind (g := fun c => (Gen.verifyAll A ivk rest).bind fun cs => OComp.pure (c && cs))
      (hA.V ivk x π) fun _ => Avoids.bind (avoids_verifyAll hA ivk rest) fun _ => trivial

theorem avoids_sessionExp {o₀ : S.ι} (hA : ArgAvoids A o₀) (ivk : IVK)
    (isk : ISK) (b : List (X × W)) :
    (Gen.sessionExp A ivk isk b).Avoids o₀ :=
  Avoids.bind (g := fun πs : Gen.Slots Pf b => Gen.verifyAll A ivk ((b.map Prod.fst).zip πs.val))
    (hA.P isk b) fun _ => avoids_verifyAll A hA ivk _

/-- Under hc, hg: two derived runs of c under one seed from the empty table, then g, have the law of
one run of c with biased coins, then g at its result, taken twice. -/
theorem law_two_runs {γ δ : Type} (c : OComp S γ) (hc : c.Avoids σ.o) (s : Fin (σ.sd + 1))
    (g : γ → γ → OComp S δ) (hg : ∀ a a', (g a a').Avoids σ.o) :
    (((c.derive σ s 0).bind fun a => (c.derive σ s 0).bind fun a' => g a a').runLazy
        (Table.empty S)).map Prod.fst =
      (runB σ c (Table.empty S)).bind fun y => ((g y.1 y.1).runLazy y.2).map Prod.fst := by
  have e : (c.derive σ s 0).runLazy (Table.empty S) =
      (runRec σ c 0 (Table.empty S) (fun _ => none)).map fun x => (x.1, glue σ s x.2.1 x.2.2) := by
    have h := runLazy_derive σ s c hc 0 (Table.empty S) (fun _ => none)
    rwa [glue_empty] at h
  rw [map_fst_runLazy_bind, e, PMF.bind_map,
    ← map_runRec σ c 0 (Table.empty S) (fun _ => none) (fun _ _ => rfl), PMF.bind_map]
  refine bind_congr_support fun x hx => ?_
  show (((c.derive σ s 0).bind fun a' => g x.1 a').runLazy (glue σ s x.2.1 x.2.2)).map Prod.fst = _
  rw [map_fst_runLazy_bind, runLazy_derive σ s c hc,
    runRec_again σ c 0 _ _ x hx x.2.1 x.2.2 (Sub.refl _) (SubR.refl _), PMF.pure_map, PMF.pure_bind]
  show ((g x.1 x.1).runLazy (glue σ s x.2.1 x.2.2)).map Prod.fst = _
  rw [runLazy_glue σ s _ (hg _ _), PMF.map_comp]
  rfl

theorem sessionExp_derived (σ : SeedOracle S) (ivk : IVK) (i : I)
    (s : Fin (σ.sd + 1)) (bt : List (X × W)) :
    Gen.sessionExp (derived A σ) ivk (i, s) bt =
      ((A.C i).derive σ s 0).bind fun a' => Gen.sessionExp A ivk a'.2 bt := by
  show ((((A.C i).derive σ s 0).bind fun out => A.P out.2 bt).bind fun πs : Gen.Slots Pf bt =>
    Gen.verifyAll (derived A σ) ivk ((bt.map Prod.fst).zip πs.val)) = _
  rw [OComp.bind_assoc]
  simp only [verifyAll_derived]
  rfl

theorem completenessExp_derived (σ : SeedOracle S) (i : I) (bt : List (X × W)) :
    Gen.completenessExp (derived A σ) i bt = OComp.sample σ.sd fun s =>
      ((A.C i).derive σ s 0).bind fun a =>
          ((A.C i).derive σ s 0).bind fun a' => Gen.sessionExp A a.1 a'.2 bt := by
  show OComp.sample σ.sd (fun s =>
      (((A.C i).derive σ s 0).bind fun out => OComp.pure (out.1, (i, s))).bind fun x =>
        Gen.sessionExp (derived A σ) x.1 x.2 bt) = _
  refine congrArg _ (funext fun s => ?_)
  rw [OComp.bind_assoc]
  refine congrArg _ (funext fun a => ?_)
  exact sessionExp_derived A σ a.1 i s bt

/-- Completeness, under hA: the derived experiment is within the bias of the committer's coins of
the experiment of A. -/
theorem tv_completeness (hA : ArgAvoids A σ.o) (i : I) (bt : List (X × W)) :
    tv (Gen.completenessExp (derived A σ) i bt).law (Gen.completenessExp A i bt).law ≤
      (A.C i).pathBias σ := by
  have h1 : (Gen.completenessExp (derived A σ) i bt).law =
      (runB σ (A.C i) (Table.empty S)).bind fun y =>
        ((Gen.sessionExp A y.1.1 y.1.2 bt).runLazy y.2).map Prod.fst := by
    rw [completenessExp_derived, OComp.law]
    simp only [OComp.runLazy, PMF.map_bind]
    refine (congrArg _
      (funext fun s =>
        law_two_runs (A.C i) (hA.C i) s (fun a a' => Gen.sessionExp A a.1 a'.2 bt)
          fun a a' => avoids_sessionExp A hA a.1 a'.2 bt)).trans ?_
    exact PMF.bind_const _ _
  have h2 : (Gen.completenessExp A i bt).law =
      ((A.C i).runLazy (Table.empty S)).bind fun y =>
        ((Gen.sessionExp A y.1.1 y.1.2 bt).runLazy y.2).map Prod.fst :=
    map_fst_runLazy_bind (A.C i) (fun x => Gen.sessionExp A x.1 x.2 bt) _
  rw [h1, h2]
  exact (tv_bind_left_le _ _ _).trans (tv_runB_le σ (A.C i) _)

/-! ## 6. Privacy -/

/-- two laws give the same probability to every outcome outside B -/
def EqOff {γ : Type} (B : Set γ) (p q : PMF γ) : Prop := ∀ u, u ∉ B → p u = q u

theorem EqOff.refl {γ : Type} (B : Set γ) (p : PMF γ) : EqOff B p p := fun _ _ => rfl

theorem EqOff.bind {γ δ : Type} {B : Set γ} (r : PMF δ) {f g : δ → PMF γ}
    (h : ∀ c ∈ r.support, EqOff B (f c) (g c)) :
    EqOff B (r.bind f) (r.bind g) := by
  intro u hu
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun c => ?_
  by_cases hc : r c = 0
  · rw [hc, zero_mul, zero_mul]
  · rw [h c ((r.mem_support_iff c).2 hc) u hu]

theorem EqOff.of_support {γ : Type} {B : Set γ} {p q : PMF γ}
    (hp : ∀ u ∈ p.support, u ∈ B) (hq : ∀ u ∈ q.support, u ∈ B) :
    EqOff B p q := by
  intro u hu
  rw [(p.apply_eq_zero_iff u).2 fun h => hu (hp u h),
    (q.apply_eq_zero_iff u).2 fun h => hu (hq u h)]

variable (σ) in
/-- the entry of a trace is a query of the seed s -/
def Hit (s : Fin (σ.sd + 1)) (e : QA S) : Prop := ∃ j r, e = ⟨σ.o, σ.pt s j, r⟩

variable (σ) in
/-- The bad event: the adversary has made a query of the seed s to the auxiliary oracle. -/
def Bad (s : Fin (σ.sd + 1)) : Set (Gen.View S IVK X Pf) := {u | ∃ e ∈ u.trace, Hit σ s e}

section Loop
variable {ISK' : Type} (A' : Gen.Arg S I X W IVK ISK' Pf)
  (Z : Gen.ViewEnv S IVK X W Pf) (isk : ISK')

/-- the trace of the view only grows -/
theorem realLoop_trace (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (T : Table S),
      ∀ x ∈ ((Gen.realLoop A' Z isk V n v).runLazy T).support, v.trace <+: x.1.trace := by
  induction V with
  | halt =>
    intro n v T x hx
    simp only [Gen.realLoop] at hx
    have hx' : x ∈ (PMF.pure (v, T)).support := hx
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
    rw [hx']
  | query o q k ih =>
    intro n v T x hx
    simp only [Gen.realLoop] at hx
    cases hT : T o q with
    | some r =>
      simp only [OComp.runLazy, hT] at hx
      exact (List.prefix_append _ _).trans (ih r n _ T x hx)
    | none =>
      simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact (List.prefix_append _ _).trans (ih r n _ _ x hx)
  | sample m k ih =>
    intro n v T x hx
    simp only [Gen.realLoop, OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    have h := ih r n _ T x hx
    exact h
  | request k ih =>
    intro n v T x hx
    cases n with
    | zero =>
      have hx' : x ∈ (PMF.pure (v, T)).support := hx
      rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
      rw [hx']
    | succ n =>
      simp only [Gen.realLoop] at hx
      cases hZ : Z v with
      | none =>
        rw [hZ] at hx
        have hx' : x ∈ (PMF.pure (v, T)).support := hx
        rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
        rw [hx']
      | some b =>
        rw [hZ] at hx
        simp only [OComp.runLazy_bind, PMF.mem_support_bind_iff] at hx
        obtain ⟨y, -, hx⟩ := hx
        have h := ih _ n _ _ x hx
        exact h

/-- an adversary with at most t queries adds at most t entries to the trace -/
theorem realLoop_length (V : Gen.AdvVerifier S X Pf) :
    ∀ (t n : ℕ) (v : Gen.View S IVK X Pf) (T : Table S), V.QueryBound t →
      ∀ x ∈ ((Gen.realLoop A' Z isk V n v).runLazy T).support,
        x.1.trace.length ≤ v.trace.length + t := by
  induction V with
  | halt =>
    intro t n v T _ x hx
    have hx' : x ∈ (PMF.pure (v, T)).support := hx
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
    rw [hx']; exact Nat.le_add_right _ _
  | query o q k ih =>
    intro t n v T hV x hx
    cases t with
    | zero => exact hV.elim
    | succ t =>
      simp only [Gen.realLoop] at hx
      have hstep : ∀ (r : S.Rng o) (T' : Table S), x ∈
            ((Gen.realLoop A' Z isk (k r) n { v with trace := v.trace ++ [⟨o, q, r⟩] }).runLazy
              T').support →
          x.1.trace.length ≤ v.trace.length + (t + 1) := by
        intro r T' h
        have h1 := ih r t n _ T' (hV r) x h
        simp only [List.length_append, List.length_singleton] at h1
        omega
      cases hT : T o q with
      | some r =>
        simp only [OComp.runLazy, hT] at hx
        exact hstep r T hx
      | none =>
        simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
        obtain ⟨r, -, hx⟩ := hx
        exact hstep r _ hx
  | sample m k ih =>
    intro t n v T hV x hx
    simp only [Gen.realLoop, OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    have h := ih r t n _ T (hV r) x hx
    exact h
  | request k ih =>
    intro t n v T hV x hx
    cases n with
    | zero =>
      have hx' : x ∈ (PMF.pure (v, T)).support := hx
      rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
      rw [hx']; exact Nat.le_add_right _ _
    | succ n =>
      simp only [Gen.realLoop] at hx
      cases hZ : Z v with
      | none =>
        rw [hZ] at hx
        have hx' : x ∈ (PMF.pure (v, T)).support := hx
        rw [PMF.support_pure, Set.mem_singleton_iff] at hx'
        rw [hx']; exact Nat.le_add_right _ _
      | some b =>
        rw [hZ] at hx
        simp only [OComp.runLazy_bind, PMF.mem_support_bind_iff] at hx
        obtain ⟨y, -, hx⟩ := hx
        have h := ih _ t n _ _ (hV _) x hx
        exact h

/-- after a query of the seed, every view is bad -/
theorem bad_of_query {s : Fin (σ.sd + 1)} {q : S.Dom σ.o} (hq : IsPt σ s q)
    (k : S.Rng σ.o → Gen.AdvVerifier S X Pf) (n : ℕ) (v : Gen.View S IVK X Pf) (T : Table S) :
    ∀ u ∈ (((Gen.realLoop A' Z isk (.query σ.o q k) n v).runLazy T).map Prod.fst).support,
      u ∈ Bad σ s := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hu
  obtain ⟨j, rfl⟩ := hq
  simp only [Gen.realLoop] at hx
  have hstep : ∀ (r : S.Rng σ.o) (T' : Table S), x ∈ ((Gen.realLoop A' Z isk (k r) n
      { v with trace := v.trace ++ [⟨σ.o, σ.pt s j, r⟩] }).runLazy T').support → x.1 ∈ Bad σ s := by
    intro r T' h
    exact ⟨⟨σ.o, σ.pt s j, r⟩,
      (realLoop_trace A' Z isk (k r) n _ T' x h).subset (by simp), j, r, rfl⟩
  cases hT : T σ.o (σ.pt s j) with
  | some r =>
    simp only [OComp.runLazy, hT] at hx
    exact hstep r T hx
  | none =>
    simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    exact hstep r _ hx

end Loop

/-- Identical until bad, under hA. Fix the seed s, the key, and a table T₀ and a record R on which
(and on every larger table) a run of the committer returns the key and changes nothing. Then, for
every table T that contains T₀, the derived loop on glue s T R and the loop of A on T give the same
probability to every view without a query of s. -/
theorem loop_eqOff (hA : ArgAvoids A σ.o) (Z : Gen.ViewEnv S IVK X W Pf) (i : I)
    (s : Fin (σ.sd + 1)) (key : IVK × ISK) (T₀ : Table S) (R : Rec σ)
    (hdet : ∀ T₃, Sub T₀ T₃ → runRec σ (A.C i) 0 T₃ R = PMF.pure (key, T₃, R))
    (V : Gen.AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : Gen.View S IVK X Pf) (T : Table S), Sub T₀ T →
      EqOff (Bad σ s)
        (((Gen.realLoop (derived A σ) Z (i, s) V n v).runLazy (glue σ s T R)).map Prod.fst)
        (((Gen.realLoop A Z key.2 V n v).runLazy T).map Prod.fst) := by
  induction V with
  | halt =>
    intro n v T _
    simp only [Gen.realLoop]
    show EqOff _ ((PMF.pure (v, glue σ s T R)).map Prod.fst) ((PMF.pure (v, T)).map Prod.fst)
    rw [PMF.pure_map, PMF.pure_map]
    exact EqOff.refl _ _
  | query o q k ih =>
    intro n v T hT
    have hgood : glue σ s T R o q = T o q →
        (∀ r, (glue σ s T R).set o q r = glue σ s (T.set o q r) R) →
        EqOff (Bad σ s)
          (((Gen.realLoop (derived A σ) Z (i, s) (.query o q k) n v).runLazy
            (glue σ s T R)).map Prod.fst)
          (((Gen.realLoop A Z key.2 (.query o q k) n v).runLazy T).map Prod.fst) := by
      intro hg hset
      cases hq : T o q with
      | some r =>
        simp only [Gen.realLoop, OComp.runLazy, hg, hq]
        exact ih r n _ T hT
      | none =>
        simp only [Gen.realLoop, OComp.runLazy, hg, hq, PMF.map_bind]
        refine EqOff.bind _ fun r _ => ?_
        rw [hset r]
        exact ih r n _ _ (hT.trans (sub_set hq r))
    by_cases ho : o = σ.o
    · subst ho
      by_cases hp : IsPt σ s q
      · exact EqOff.of_support (bad_of_query _ Z _ hp k n v _) (bad_of_query _ Z _ hp k n v _)
      · exact hgood (glue_not_pt hp) fun r => glue_set_not_pt hp r
    · exact hgood (congrFun (glue_of_ne ho) q) fun r => glue_set_of_ne ho q r
  | sample m k ih =>
    intro n v T hT
    simp only [Gen.realLoop, OComp.runLazy, PMF.map_bind]
    exact EqOff.bind _ fun r _ => ih r n _ T hT
  | request k ih =>
    intro n v T hT
    cases n with
    | zero =>
      show EqOff _ ((PMF.pure (v, glue σ s T R)).map Prod.fst) ((PMF.pure (v, T)).map Prod.fst)
      rw [PMF.pure_map, PMF.pure_map]
      exact EqOff.refl _ _
    | succ n =>
      simp only [Gen.realLoop]
      cases hZ : Z v with
      | none =>
        show EqOff _ ((PMF.pure (v, glue σ s T R)).map Prod.fst) ((PMF.pure (v, T)).map Prod.fst)
        rw [PMF.pure_map, PMF.pure_map]
        exact EqOff.refl _ _
      | some b =>
        show EqOff _
          ((((((A.C i).derive σ s 0).bind fun out => A.P out.2 b.pairs).bind fun πs =>
              Gen.realLoop (derived A σ) Z (i, s) (k (b.released πs.val)) n
                { v with sessions := v.sessions ++ [b.released πs.val] }).runLazy
            (glue σ s T R)).map Prod.fst)
          ((((A.P key.2 b.pairs).bind fun πs =>
              Gen.realLoop A Z key.2 (k (b.released πs.val)) n
                { v with sessions := v.sessions ++ [b.released πs.val] }).runLazy T).map Prod.fst)
        rw [OComp.bind_assoc, map_fst_runLazy_bind, runLazy_derive σ s _ (hA.C i), hdet T hT,
          PMF.pure_map, PMF.pure_bind, map_fst_runLazy_bind, map_fst_runLazy_bind,
          runLazy_glue σ s _ (hA.P _ _), PMF.bind_map]
        exact EqOff.bind _ fun y hy => ih _ n _ _ (hT.trans (runLazy_sub _ T y hy))

open Classical in
/-- a trace meets at most as many seeds as it has entries -/
theorem card_seeds_le (σ : SeedOracle S) :
    ∀ l : List (QA S),
      (Finset.univ.filter fun s : Fin (σ.sd + 1) => ∃ e ∈ l, Hit σ s e).card ≤ l.length
  | [] => by simp
  | e :: l => by
      have h1 : (Finset.univ.filter fun s : Fin (σ.sd + 1) => ∃ e' ∈ e :: l, Hit σ s e') ⊆
          (Finset.univ.filter fun s : Fin (σ.sd + 1) => Hit σ s e) ∪
            (Finset.univ.filter fun s : Fin (σ.sd + 1) => ∃ e' ∈ l, Hit σ s e') := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          List.mem_cons, Finset.mem_union] at hs ⊢
        obtain ⟨e', he' | he', hh⟩ := hs
        · exact Or.inl (he' ▸ hh)
        · exact Or.inr ⟨e', he', hh⟩
      have h2 : (Finset.univ.filter fun s : Fin (σ.sd + 1) => Hit σ s e).card ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        obtain ⟨j, r, rfl⟩ := ha
        obtain ⟨j', r', h⟩ := hb
        have h3 : (σ.pt a j, r) = (σ.pt b j', r') := eq_of_heq (Sigma.mk.inj h).2
        exact (σ.inj _ _ _ _ (Prod.mk.inj h3).1).1
      calc _ ≤ _ := Finset.card_le_card h1
        _ ≤ _ := Finset.card_union_le _ _
        _ ≤ 1 + l.length := Nat.add_le_add h2 (card_seeds_le σ l)
        _ = (e :: l).length := by simp [Nat.add_comm]

theorem realExp_derived (σ : SeedOracle S) (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X W Pf) (i : I) (N : ℕ) :
    Gen.realExp (derived A σ) Vt Z i N = OComp.sample σ.sd fun s => ((A.C i).derive σ s 0).bind fun a =>
      Gen.realLoop (derived A σ) Z (i, s) (Vt a.1) N ⟨a.1, [], [], []⟩ := by
  show OComp.sample σ.sd (fun s =>
      (((A.C i).derive σ s 0).bind fun out => OComp.pure (out.1, (i, s))).bind fun x =>
        Gen.realLoop (derived A σ) Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) = _
  refine congrArg _ (funext fun s => ?_)
  rw [OComp.bind_assoc]
  rfl

/-- The real experiment of index privacy, under hA, hV: the derived prover changes the law of the
adversary's view by at most t / (number of seeds), plus the path bias of C i. (The number of seeds:
`σ.sd + 1`; the path bias: `OComp.pathBias`, Rom/SpecDerive.lean.) -/
theorem tv_real_le (hA : ArgAvoids A σ.o) (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X W Pf) (i : I) (N t : ℕ) (hV : ∀ ivk, (Vt ivk).QueryBound t) :
    tv (Gen.realExp (derived A σ) Vt Z i N).law (Gen.realExp A Vt Z i N).law ≤
      (t : ℝ≥0∞) / (σ.sd + 1 : ℕ) + (A.C i).pathBias σ := by
  classical
  -- the experiment with biased coins of the committer
  obtain ⟨K, hK⟩ : ∃ K : (IVK × ISK) × Table S → PMF (Gen.View S IVK X Pf), K = fun y =>
    ((Gen.realLoop A Z y.1.2 (Vt y.1.1) N ⟨y.1.1, [], [], []⟩).runLazy y.2).map Prod.fst := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (runB σ (A.C i) (Table.empty S)).bind K := ⟨_, rfl⟩
  have hreal : (Gen.realExp A Vt Z i N).law = ((A.C i).runLazy (Table.empty S)).bind K := by
    rw [hK]
    exact map_fst_runLazy_bind
      (A.C i) (fun x => Gen.realLoop A Z x.2 (Vt x.1) N ⟨x.1, [], [], []⟩) _
  have hQreal : tv Q (Gen.realExp A Vt Z i N).law ≤ (A.C i).pathBias σ := by
    rw [hQ, hreal]
    exact (tv_bind_left_le _ _ _).trans (tv_runB_le σ (A.C i) _)
  have hQ' : Q =
      (runRec σ (A.C i) 0 (Table.empty S) (fun _ => none)).bind fun x => K (x.1, x.2.1) := by
    rw [hQ, ← map_runRec σ (A.C i) 0 (Table.empty S) (fun _ => none) (fun _ _ => rfl), PMF.bind_map]
    rfl
  -- the derived experiment under a fixed seed
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Fin (σ.sd + 1) → PMF (Gen.View S IVK X Pf), Ps = fun s =>
    ((((A.C i).derive σ s 0).bind fun a =>
            Gen.realLoop (derived A σ) Z (i, s) (Vt a.1) N ⟨a.1, [], [], []⟩).runLazy
          (Table.empty S)).map Prod.fst := ⟨_, rfl⟩
  have hlaw : (Gen.realExp (derived A σ) Vt Z i N).law = (unif (Fin (σ.sd + 1))).bind Ps := by
    rw [realExp_derived, OComp.law, hPs]
    simp only [OComp.runLazy, PMF.map_bind]
  have hoff : ∀ s, EqOff (Bad σ s) (Ps s) Q := by
    intro s
    have e : ((A.C i).derive σ s 0).runLazy (Table.empty S) =
        (runRec σ (A.C i) 0 (Table.empty S) (fun _ => none)).map fun x =>
          (x.1, glue σ s x.2.1 x.2.2) := by
      have h := runLazy_derive σ s (A.C i) (hA.C i) 0 (Table.empty S) (fun _ => none)
      rwa [glue_empty] at h
    rw [hPs, hQ', hK]
    show EqOff _ ((OComp.runLazy (OComp.bind _ _) _).map Prod.fst) _
    rw [map_fst_runLazy_bind, e, PMF.bind_map]
    refine EqOff.bind _ fun x hx => ?_
    exact loop_eqOff A hA Z i s x.1 x.2.1 x.2.2
      (fun T₃ hT₃ => runRec_again σ (A.C i) 0 _ _ x hx T₃ x.2.2 hT₃ (SubR.refl _))
      (Vt x.1.1) N _ x.2.1 (Sub.refl _)
  have htv : ∀ s, tv (Ps s) Q ≤ pr Q (Bad σ s) := fun s => by
    rw [tv_comm]
    exact tv_le_pr_of_eq_off Q (Ps s) (Bad σ s) fun u hu => (hoff s u hu).symm
  -- a view meets at most t seeds
  have hlen : ∀ u ∈ Q.support, u.trace.length ≤ t := by
    intro u hu
    rw [hQ, hK] at hu
    obtain ⟨y, -, hu⟩ := (PMF.mem_support_bind_iff _ _ _).1 hu
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hu
    have h := realLoop_length A Z y.1.2 (Vt y.1.1) t N _ y.2 (hV _) x hx
    simpa using h
  have hsum : ∑ s, pr Q (Bad σ s) ≤ (t : ℝ≥0∞) := by
    simp only [pr_eq_expect]
    rw [← expect_finset_sum]
    refine expect_le_of_forall_le Q fun u hu => ?_
    rw [Finset.sum_boole]
    refine Nat.cast_le.2 (le_trans ?_ (hlen u hu))
    convert card_seeds_le σ u.trace
  have h1 : tv (Gen.realExp (derived A σ) Vt Z i N).law Q ≤ (t : ℝ≥0∞) / (σ.sd + 1 : ℕ) := by
    have hc : Q = (unif (Fin (σ.sd + 1))).bind fun _ => Q := (PMF.bind_const _ _).symm
    rw [hlaw]
    conv_lhs => rw [hc]
    refine (tv_unif_bind_le Ps fun _ => Q).trans ?_
    rw [Fintype.card_fin]
    exact ENNReal.div_le_div_right ((Finset.sum_le_sum fun s _ => htv s).trans hsum) _
  exact (tv_triangle _ Q _).trans (add_le_add h1 hQreal)

end Derive

end Rom
