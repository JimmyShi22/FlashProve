-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Prefix.lean: a whole family of independent oracles from one hash function f.

This is the easy direction of the step to one hash function (`OComp.overOne`, Rom/Family.lean): an
algorithm over the family becomes one over f. The other direction, from an adversary over f to one
over the family, is in Rom/ExitDown.lean.

Oracle o at the query q is read as the tuple ( f(code o q 0), ..., f(code o q (blocks o - 1)) ),
taken through the bijection rng o.
Because the query encoding (`OracleCoding.code`) (o, q, j) ↦ code o q j is injective, for f uniform the
family so obtained is distributed as U S: all its members are uniformly random functions,
independent of each other (`U_map_readBlocks`).
Then an algorithm over S and the same over f (`OComp.overOne`) have the same probabilities
(`Pr_overOne`).

Shared with VCV-io: lean/CREDITS.md, section 4.
-/
import Rom.Family
import Rom.Bridge
import Rom.EagerLazy

open MeasureTheory
open scoped ENNReal

namespace Rom

variable {S : OSpec} {lam : ℕ} {α β : Type}

/-- The family that is read out of the hash function g through the query encoding m. -/
def readBlocks (m : OracleCoding S lam) (g : Fam (rom lam)) : Fam S :=
  fun o q => (m.rng o).symm fun j => rngOf () (g () (m.code o q j))

/-- The encoding as one function on the triples ((o, q), j). -/
def OracleCoding.flat (m : OracleCoding S lam) (k : Σ p : (Σ o, S.Dom o), Fin (m.blocks p.1)) : ZKCP.Str :=
  m.code k.1.1 k.1.2 k.2

lemma OracleCoding.flat_injective (m : OracleCoding S lam) : Function.Injective m.flat := by
  rintro ⟨⟨o, q⟩, j⟩ ⟨⟨o', q'⟩, j'⟩ h
  have h' := m.inj (a₁ := ⟨o, (q, j)⟩) (a₂ := ⟨o', (q', j')⟩) h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq h2)
  rfl

lemma measurable_rng_symm (m : OracleCoding S lam) (o : S.ι) :
    Measurable fun r : Fin (m.blocks o) → ZKCP.Digest lam => (m.rng o).symm r :=
  measurable_of_finite _

/-- A finite product of uniform distributions is the uniform distribution on the tuples. -/
lemma infinitePi_uniform_fin (n : ℕ) :
    Measure.infinitePi (fun _ : Fin n => (PMF.uniformOfFintype (ZKCP.Digest lam)).toMeasure)
      = (PMF.uniformOfFintype (Fin n → ZKCP.Digest lam)).toMeasure := by
  rw [Measure.infinitePi_eq_pi]
  refine Measure.ext_of_singleton fun g => ?_
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton g)]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_pi,
    Nat.cast_pow, ENNReal.inv_pow]

/-- A uniform tuple of hash blocks, mapped by the bijection, is a uniform element of the range. -/
lemma map_rng_symm (m : OracleCoding S lam) (o : S.ι) :
    ((PMF.uniformOfFintype (Fin (m.blocks o) → ZKCP.Digest lam)).toMeasure).map
        (fun r => (m.rng o).symm r) = unifM S o := by
  refine Measure.ext_of_singleton fun r => ?_
  have hpre : (fun x : Fin (m.blocks o) → ZKCP.Digest lam => (m.rng o).symm x) ⁻¹' {r} =
      {m.rng o r} := by
    ext x; simp [Equiv.symm_apply_eq]
  rw [Measure.map_apply (measurable_rng_symm m o) (measurableSet_singleton r), hpre,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_congr (m.rng o)]

lemma measurable_readBlocks (m : OracleCoding S lam) : Measurable (readBlocks m) := by
  refine measurable_pi_iff.2 fun o => measurable_pi_iff.2 fun q => ?_
  have h : Measurable fun g : Fam (rom lam) =>
      fun j : Fin (m.blocks o) => rngOf () (g () (m.code o q j)) := by
    refine measurable_pi_iff.2 fun j => ?_
    have h1 : Measurable fun g : Fam (rom lam) => g () := measurable_pi_apply (() : (rom lam).ι)
    have h2 : Measurable fun g : (rom lam).Dom () → (rom lam).Rng () => g (m.code o q j) :=
      measurable_pi_apply (m.code o q j : (rom lam).Dom ())
    exact (measurable_rngOf ()).comp (h2.comp h1)
  exact (measurable_rng_symm m o).comp h

/-- Independent oracles out of one. Reading a uniform oracle through an injective query encoding
gives the uniform distribution on the whole family: every member is a uniformly random function, and
all members are independent. -/
theorem U_map_readBlocks (m : OracleCoding S lam) : (U (rom lam)).map (readBlocks m) = U S := by
  set μD : Measure (ZKCP.Digest lam) := (PMF.uniformOfFintype (ZKCP.Digest lam)).toMeasure with hμD
  -- the four steps
  let r1 : ZKCP.Oracle lam → ((k : Σ p : (Σ o, S.Dom o), Fin (m.blocks p.1)) → ZKCP.Digest lam) :=
    fun f k => f (m.flat k)
  let r2 :=
    MeasurableEquiv.piCurry fun (p : Σ o, S.Dom o) (_ : Fin (m.blocks p.1)) => ZKCP.Digest lam
  let r3 : ((p : Σ o, S.Dom o) → Fin (m.blocks p.1) → ZKCP.Digest lam) → Flat S :=
    fun x p => (m.rng p.1).symm (x p)
  let r4 := MeasurableEquiv.piCurry fun (o : S.ι) (_ : S.Dom o) => S.Rng o
  have hr1 : Measurable r1 := measurable_pi_iff.2 fun k => measurable_pi_apply (m.flat k)
  have hr3 : Measurable r3 :=
    measurable_pi_iff.2 fun p => (measurable_rng_symm m p.1).comp (measurable_pi_apply p)
  -- 1. read f at the strings code o q j: independent uniform hash blocks
  have h1 : (ZKCP.U lam).map r1 =
      Measure.infinitePi fun _ : (Σ p : (Σ o, S.Dom o), Fin (m.blocks p.1)) => μD :=
    infinitePi_map_reindex m.flat m.flat_injective fun _ : ZKCP.Str => μD
  -- 2. group the hash blocks of one query
  have h2 : (Measure.infinitePi fun _ : (Σ p : (Σ o, S.Dom o), Fin (m.blocks p.1)) => μD).map r2 =
      Measure.infinitePi fun p : (Σ o, S.Dom o) =>
        Measure.infinitePi fun _ : Fin (m.blocks p.1) => μD :=
    Measure.infinitePi_map_piCurry
      (X := fun (p : Σ o, S.Dom o) (_ : Fin (m.blocks p.1)) => ZKCP.Digest lam) (fun _ _ => μD)
  -- 3. a tuple of uniform hash blocks is a uniform element of the range
  have h3 : (Measure.infinitePi fun p : (Σ o, S.Dom o) =>
        Measure.infinitePi fun _ : Fin (m.blocks p.1) => μD).map r3 =
      Measure.infinitePi fun p : (Σ o, S.Dom o) => unifM S p.1 := by
    have h := Measure.infinitePi_map_pi
      (μ := fun p : (Σ o, S.Dom o) => Measure.infinitePi fun _ : Fin (m.blocks p.1) => μD)
      (f := fun p (r : Fin (m.blocks p.1) → ZKCP.Digest lam) => (m.rng p.1).symm r)
      (fun p => measurable_rng_symm m p.1)
    simp only [hμD, infinitePi_uniform_fin, map_rng_symm] at h
    simpa only [hμD, infinitePi_uniform_fin] using h
  -- 4. curry (o, q)
  calc (U (rom lam)).map (readBlocks m)
      = (ZKCP.U lam).map (fun f => readBlocks m (famOf f)) := by
        rw [← U_map_famOf, Measure.map_map (measurable_readBlocks m) measurable_famOf]; rfl
    _ = ((((ZKCP.U lam).map r1).map r2).map r3).map r4 := by
        rw [Measure.map_map r2.measurable hr1, Measure.map_map hr3 (r2.measurable.comp hr1),
          Measure.map_map r4.measurable (hr3.comp (r2.measurable.comp hr1))]
        rfl
    _ = U S := by rw [h1, h2, h3, ← U_eq_map_curry]

/-! ### Algorithms -/

lemma runEager_askAll (g : Fam (rom lam)) : ∀ (n : ℕ) (pts : Fin n → List Bool),
    (askAll lam n pts).runEager g = PMF.pure fun j => g () (pts j)
  | 0, _ => by
    simp only [askAll, OComp.runEager]
    congr 1; funext j; exact j.elim0
  | n + 1, pts => by
    simp only [askAll, OComp.runEager, OComp.runEager_bind, runEager_askAll g n]
    refine (PMF.pure_bind _ _).trans ?_
    congr 1; funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- The same algorithm over the hash function behaves, for every fixed function, as the algorithm
over the family that is read out of it. -/
theorem runEager_overOne (m : OracleCoding S lam) (g : Fam (rom lam)) (c : OComp S α) :
    (c.overOne m).runEager g = c.runEager (readBlocks m g) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.overOne, OComp.runEager, ih]
  | query o q k ih =>
    simp only [OComp.overOne, OComp.runEager, OComp.runEager_bind, runEager_askAll, ih]
    exact PMF.pure_bind _ _

/-- The probabilities agree, also for an event that depends on the family (measurably). -/
theorem Pr_overOne_dep (m : OracleCoding S lam) (c : OComp S α) (E : Fam S → Set α)
    (hE : ∀ a, MeasurableSet {f | a ∈ E f}) :
    Pr (c.overOne m) (fun g => E (readBlocks m g)) = Pr c E := by
  unfold Pr
  rw [← U_map_readBlocks m, lintegral_map (measurable_PrCoins_dep c E hE) (measurable_readBlocks m)]
  refine lintegral_congr fun g => ?_
  unfold PrCoins
  rw [runEager_overOne]

theorem Pr_overOne (m : OracleCoding S lam) (c : OComp S α) (E : Set α) :
    Pr (c.overOne m) (fun _ => E) = Pr c (fun _ => E) :=
  Pr_overOne_dep m c (fun _ => E) fun a => by by_cases h : a ∈ E <;> simp [h]

/-! ### Query counts -/

lemma OComp.QueryBound.mono {c : OComp S α} {s t : ℕ} (h : c.QueryBound s) (hst : s ≤ t) :
    c.QueryBound t := by
  induction c generalizing s t with
  | pure a => trivial
  | query o q k ih =>
    cases s with
    | zero => exact h.elim
    | succ s =>
      cases t with
      | zero => omega
      | succ t => exact fun r => ih r (h r) (by omega)
  | sample n k ih => exact fun r => ih r (h r) hst

lemma OComp.QueryBound.bind {c : OComp S α} {g : α → OComp S β} {s t : ℕ} (h : c.QueryBound s)
    (hg : ∀ a, (g a).QueryBound t) : (c.bind g).QueryBound (s + t) := by
  induction c generalizing s with
  | pure a => exact (hg a).mono (by omega)
  | query o q k ih =>
    cases s with
    | zero => exact h.elim
    | succ s =>
      have : s + 1 + t = (s + t) + 1 := by omega
      rw [this]
      exact fun r => ih r (h r)
  | sample n k ih => exact fun r => ih r (h r)

lemma queryBound_askAll : ∀ (n : ℕ) (pts : Fin n → List Bool), (askAll lam n pts).QueryBound n
  | 0, _ => trivial
  | n + 1, pts => fun r => by
    have := (queryBound_askAll n fun i => pts i.succ).bind (t := 0)
      (g := fun rest => (OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest) :
        OComp (rom lam) (Fin (n + 1) → Fin lam → Bool))) fun _ => trivial
    simpa using this

/-- t queries to the family are at most t * B queries to the hash function, if no answer has more
than B hash blocks. -/
theorem queryBound_overOne (m : OracleCoding S lam) {B : ℕ} (hB : ∀ o, m.blocks o ≤ B) (c : OComp S α) :
    ∀ t, c.QueryBound t → (c.overOne m).QueryBound (t * B) := by
  induction c with
  | pure a => intro t _; trivial
  | sample n k ih => intro t h r; exact ih r t (h r)
  | query o q k ih =>
    intro t h
    cases t with
    | zero => exact h.elim
    | succ t =>
      have h1 := ((queryBound_askAll (lam := lam) (m.blocks o) (m.code o q)).mono (hB o)).bind
        (g := fun bs => (k ((m.rng o).symm bs)).overOne m) fun bs => ih _ t (h _)
      have : (t + 1) * B = B + t * B := by ring
      rw [this]
      exact h1

end Rom
