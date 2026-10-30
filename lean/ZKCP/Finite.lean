-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Finite.lean: how a probability under U(λ), a measure on functions with an infinite domain,
reduces to counting.

Seen through any finite set S of query strings, U(λ) (ZKCP/Defs.lean: the uniform distribution on
functions {0,1}* → {0,1}^λ) is the uniform distribution on the finitely many tables S → {0,1}^λ
(`U_map_restrict`). Every oracle algorithm queries inside some finite S
(`OComp.exists_queriesIn`), and then its probability `Pr`, for an event that does not mention f, is
the plain average, over all tables on S, of its probability with the table fixed (`Pr_eq_average`;
for an event that reads f on S only: `Pr_eq_average_dep`). This is how a proof by counting over a
finite table of hash values connects to the definitions of ZKCP/Defs.lean.

Notation: ZKCP: see `IsZKCPArg`, ZKCP/Defs.lean.
-/
import ZKCP.Defs

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {α : Type}

/-- The restriction of f ← U(λ) to a finite set S of strings is uniform on the tables S →
{0,1}^λ. -/
theorem U_map_restrict (S : Finset Str) :
    (U lam).map S.restrict = (PMF.uniformOfFintype (S → Digest lam)).toMeasure := by
  rw [U, Measure.infinitePi_map_restrict]
  refine Measure.ext_of_singleton fun g => ?_
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton g)]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ, Fintype.card_pi,
    Nat.cast_pow, ENNReal.inv_pow]

/-- The average over f ← U(λ) of a quantity that depends on f only through its values on the finite
set S is the plain average over all tables g : S → {0,1}^λ. -/
theorem lintegral_U_restrict (S : Finset Str) (F : (S → Digest lam) → ℝ≥0∞) :
    ∫⁻ f, F (S.restrict f) ∂(U lam)
      = ∑ g : S → Digest lam, (Fintype.card (S → Digest lam) : ℝ≥0∞)⁻¹ * F g := by
  rw [← lintegral_map (f := F) (measurable_of_finite _) (Finset.measurable_restrict S),
    U_map_restrict, lintegral_fintype]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton g), PMF.uniformOfFintype_apply,
    mul_comm]

/-- The number of tables on S is (2^λ)^|S|. -/
lemma card_tables (S : Finset Str) : Fintype.card (S → Digest lam) = (2 ^ lam) ^ S.card := by
  simp

/-- A table on S, read as a whole oracle: outside S the answer is 0^λ. (Which value is taken outside
S does not matter for an algorithm that queries inside S: OComp.run_congr.) -/
def extend (S : Finset Str) (g : S → Digest lam) : Oracle lam :=
  fun q => if h : q ∈ S then g ⟨q, h⟩ else fun _ => false

lemma extend_restrict (S : Finset Str) (f : Oracle lam) {q : Str} (hq : q ∈ S) :
    extend S (S.restrict f) q = f q := by
  simp [extend, hq]

/-- All queries that the algorithm can ever make, on any path, lie in S. -/
def OComp.QueriesIn (S : Finset Str) : OComp lam α → Prop
  | .pure _ => True
  | .query q k => q ∈ S ∧ ∀ r, (k r).QueriesIn S
  | .sample _ k => ∀ r, (k r).QueriesIn S

/-- An algorithm with `QueriesIn S` sees the oracle only through its values on S. -/
theorem OComp.run_congr {S : Finset Str} {f g : Oracle lam} (h : ∀ q ∈ S, f q = g q)
    (c : OComp lam α) (hc : c.QueriesIn S) : c.run f = c.run g := by
  induction c with
  | pure a => rfl
  | query q k ih =>
    simp only [OComp.run, h q hc.1]
    exact ih (g q) (hc.2 _)
  | sample n k ih =>
    simp only [OComp.run]
    congr 1; funext r; exact ih r (hc r)

lemma OComp.QueriesIn.mono {S S' : Finset Str} (hS : S ⊆ S') (c : OComp lam α)
    (h : c.QueriesIn S) : c.QueriesIn S' := by
  induction c with
  | pure a => trivial
  | query q k ih => exact ⟨hS h.1, fun r => ih r (h.2 r)⟩
  | sample n k ih => exact fun r => ih r (h r)

/-- Every oracle algorithm has a finite set S with `QueriesIn S`: its tree is finite. -/
theorem OComp.exists_queriesIn (c : OComp lam α) : ∃ S : Finset Str, c.QueriesIn S := by
  classical
  induction c with
  | pure a => exact ⟨∅, trivial⟩
  | query q k ih =>
    choose S hS using ih
    refine ⟨insert q (Finset.univ.biUnion S), Finset.mem_insert_self _ _, fun r => ?_⟩
    exact (hS r).mono (fun x hx => Finset.mem_insert_of_mem
      (Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, hx⟩)) _
  | sample n k ih =>
    choose S hS using ih
    exact ⟨Finset.univ.biUnion S, fun r => (hS r).mono (fun x hx =>
      Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, hx⟩) _⟩

/-- For an algorithm with `QueriesIn S` and f fixed, the probability over the coins depends on f
only through its values on S. -/
theorem PrCoins_congr {S : Finset Str} {f g : Oracle lam} (h : ∀ q ∈ S, f q = g q)
    (c : OComp lam α) (hc : c.QueriesIn S) (E : Set α) : PrCoins f c E = PrCoins g c E := by
  unfold PrCoins; rw [OComp.run_congr h c hc]

/-- Counting.  For an algorithm that queries inside the finite set S, and an event that does not
mention f,  Pr[ a ∈ E | f ← U(λ); a ← c^f ]  is the average, over all tables g on S, of
Pr[ a ∈ E | a ← c^g ]. -/
theorem Pr_eq_average (c : OComp lam α) {S : Finset Str} (hc : c.QueriesIn S) (E : Set α) :
    Pr c (fun _ => E) = ∑ g : S → Digest lam,
      (Fintype.card (S → Digest lam) : ℝ≥0∞)⁻¹ * PrCoins (extend S g) c E := by
  rw [← lintegral_U_restrict S fun g => PrCoins (extend S g) c E]
  unfold Pr
  exact lintegral_congr fun f => PrCoins_congr (fun q hq => (extend_restrict S f hq).symm) c hc E

/-- `Pr_eq_average` for an event that mentions f, but only through its values on S. -/
theorem Pr_eq_average_dep (c : OComp lam α) {S : Finset Str} (hc : c.QueriesIn S)
    (E : Oracle lam → Set α) (hE : ∀ f g : Oracle lam, (∀ q ∈ S, f q = g q) → E f = E g) :
    Pr c E = ∑ g : S → Digest lam,
      (Fintype.card (S → Digest lam) : ℝ≥0∞)⁻¹ * PrCoins (extend S g) c (E (extend S g)) := by
  rw [← lintegral_U_restrict S fun g => PrCoins (extend S g) c (E (extend S g))]
  unfold Pr
  refine lintegral_congr fun f => ?_
  have h : ∀ q ∈ S, f q = extend S (S.restrict f) q := fun q hq => (extend_restrict S f hq).symm
  rw [hE f _ h, PrCoins_congr h c hc]

end ZKCP
