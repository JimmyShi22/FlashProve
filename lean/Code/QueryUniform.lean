-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/QueryUniform.lean: when do a few positions of a randomised linear encoding reveal nothing?

K is a finite field (any field where nothing is counted or sampled) and φ any linear map; all is
stated on Mathlib's types only.

An encoding is a fixed word (the contribution of the message) plus φ μ, where φ is linear and μ is
uniform. All that matters is whether φ, restricted to a set S of positions, is onto K^S
(`OntoUpTo`). The file shows:

 * Part 1: a map with fibres of equal size maps the uniform distribution to the uniform one.
 * Part 2: what `OntoUpTo φ b` gives for one encoding, as a count and as a distribution; two
   characterisations (`queryUniform_iff_ontoUpTo`, `ontoUpTo_iff_linearIndependent`).
 * Part 3: the same for a table of R encodings with independent randomness.
 * Part 4: no encoder with r uniform coordinates hides more than r positions (`OntoUpTo.le_card`).
 * Part 5: if φ is onto on every set of at most b positions, so is the same matrix over an extension
   field E (`OntoUpTo.of_algebraMap`).

The label (P3) is that of the field `hides` of `Enc.Props` (Code/Iface.lean).
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Algebra.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false

namespace Code

open Function

/-! ## Part 1. Fibres of equal size, and the uniform distribution -/

/-- All fibres of a surjective additive map between finite groups have the same size:
(size of a fibre) · |W| = |V|. -/
theorem card_fiber_mul {V W : Type*} [AddGroup V] [AddGroup W] [Finite V] [Finite W] (φ : V →+ W)
    (hφ : Surjective φ) (w : W) : Nat.card {x : V // φ x = w} * Nat.card W = Nat.card V := by
  have hsame : ∀ w', Nat.card {x : V // φ x = w'} = Nat.card {x : V // φ x = w} := by
    intro w'
    obtain ⟨x0, hx0⟩ := hφ (-w + w')
    refine (Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight x0) fun a => ?_)).symm
    rw [Equiv.coe_addRight, map_add, hx0]
    constructor
    · intro h
      rw [h, add_neg_cancel_left]
    · intro h
      have h2 : φ a + (-w + w') = w + (-w + w') := by rw [h, add_neg_cancel_left]
      exact add_right_cancel h2
  haveI := Fintype.ofFinite W
  have hW : Nat.card W = Fintype.card W := Nat.card_eq_fintype_card
  calc Nat.card {x : V // φ x = w} * Nat.card W
      = ∑ _w' : W, Nat.card {x : V // φ x = w} := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hW, mul_comm]
    _ = ∑ w' : W, Nat.card {x : V // φ x = w'} := Finset.sum_congr rfl fun w' _ => (hsame w').symm
    _ = Nat.card (Σ w' : W, {x : V // φ x = w'}) := Nat.card_sigma.symm
    _ = Nat.card V := Nat.card_congr (Equiv.sigmaFiberEquiv φ)

/-- `card_fiber_mul` for a surjective additive map followed by a translation. -/
theorem card_affine_fiber_mul {V W : Type*} [AddGroup V] [AddGroup W] [Finite V] [Finite W]
    (φ : V →+ W) (hφ : Surjective φ) (c w : W) :
    Nat.card {x : V // c + φ x = w} * Nat.card W = Nat.card V := by
  rw [Nat.card_congr
      (Equiv.subtypeEquivRight fun x => (eq_neg_add_iff_add_eq (a := φ x) (b := c) (c := w)).symm)]
  exact card_fiber_mul φ hφ (-c + w)

/-- For non-empty α and β, a map all of whose fibres have the size |α| / |β| maps the uniform
distribution on α to the uniform distribution on β. -/
theorem map_uniform_of_card_fiber {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α → β) (h : ∀ b, Nat.card {a : α // f a = b} * Nat.card β = Nat.card α) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  classical
  ext b
  have hb := h b
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype] at hb
  have hc0 : (Finset.univ.filter fun a => f a = b).card ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hb
    exact Fintype.card_ne_zero hb.symm
  have hsum : (∑ a, if b = f a then ((Fintype.card α : ENNReal))⁻¹ else 0) =
      ((Finset.univ.filter fun a => f a = b).card : ENNReal) * ((Fintype.card α : ENNReal))⁻¹ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 3
    ext a
    simp [eq_comm]
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [hsum, ← hb]
  push_cast
  rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hc0)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hc0) (ENNReal.natCast_ne_top _), one_mul]

/-- A surjective additive map, followed by a translation, maps uniform to uniform. -/
theorem map_uniform_of_surjective {V W : Type*} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
    (φ : V →+ W) (hφ : Surjective φ) (c : W) :
    (PMF.uniformOfFintype V).map (fun x => c + φ x) = PMF.uniformOfFintype W :=
  map_uniform_of_card_fiber _ fun w => card_affine_fiber_mul φ hφ c w

/-! ## Part 2. One encoding -/

section One

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*}

/-- The word φ μ, read at the positions of S only. -/
def restr (φ : V →ₗ[K] (ι → K)) (S : Finset ι) : V →ₗ[K] (S → K) :=
  (LinearMap.funLeft K K (Subtype.val : S → ι)).comp φ

@[simp] theorem restr_apply (φ : V →ₗ[K] (ι → K)) (S : Finset ι) (μ : V) (j : S) :
    restr φ S μ j = φ μ j := rfl

/-- What is used of the code. φ maps the randomness of an encoding to its
contribution to the codeword. On every set of at most b positions the words φ μ take all patterns of
symbols. -/
def OntoUpTo (φ : V →ₗ[K] (ι → K)) (b : ℕ) : Prop :=
  ∀ S : Finset ι, S.card ≤ b → Surjective (restr φ S)

theorem OntoUpTo.mono {φ : V →ₗ[K] (ι → K)} {b b' : ℕ} (h : OntoUpTo φ b) (hb : b' ≤ b) :
    OntoUpTo φ b' :=
  fun S hS => h S (hS.trans hb)

/-- On the empty set of positions there is nothing to show. -/
theorem ontoUpTo_zero (φ : V →ₗ[K] (ι → K)) : OntoUpTo φ 0 := by
  intro S hS w
  refine ⟨0, funext fun j => ?_⟩
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨j, j.2⟩
  omega

/-- `OntoUpTo` carries over from φ to a map φ' that arises from φ by a surjection g of the domains
and by multiplying every position j by a scalar c j that is not 0. -/
theorem OntoUpTo.of_scaled {V' : Type*} [AddCommGroup V'] [Module K V'] {φ : V →ₗ[K] (ι → K)}
    {b : ℕ} (h : OntoUpTo φ b) (φ' : V' →ₗ[K] (ι → K)) (g : V' → V) (hg : Surjective g) (c : ι → K)
    (hc : ∀ j, c j ≠ 0) (h' : ∀ μ j, φ' μ j = c j * φ (g μ) j) : OntoUpTo φ' b := by
  intro S hS w
  obtain ⟨μ, hμ⟩ := h S hS fun j => w j / c j
  obtain ⟨μ', rfl⟩ := hg μ
  refine ⟨μ', funext fun j => ?_⟩
  have h1 : φ (g μ') j = w j / c j := congrFun hμ j
  rw [restr_apply, h', h1, mul_comm, div_mul_cancel₀ _ (hc j)]

/-- `OntoUpTo` carries over from φ to a map φ' with a larger domain that extends φ. -/
theorem OntoUpTo.of_emb {V' : Type*} [AddCommGroup V'] [Module K V'] {φ : V →ₗ[K] (ι → K)} {b : ℕ}
    (h : OntoUpTo φ b) (φ' : V' →ₗ[K] (ι → K)) (emb : V → V') (h' : ∀ μ j, φ' (emb μ) j = φ μ j) :
    OntoUpTo φ' b := by
  intro S hS w
  obtain ⟨μ, hμ⟩ := h S hS w
  refine ⟨emb μ, funext fun j => ?_⟩
  rw [restr_apply, h']
  exact congrFun hμ j

/-- One encoding, as a count, under `h`. Let d be the contribution of the message, S a
set of at most b positions and v any pattern on S. Of all values μ of the randomness, exactly one in
|K|^|S| gives the encoding d + φ μ the pattern v on S.
The count does not depend on the message. -/
theorem OntoUpTo.card_fiber [Finite K] [Finite V] {φ : V →ₗ[K] (ι → K)} {b : ℕ} (h : OntoUpTo φ b)
    {S : Finset ι} (hS : S.card ≤ b) (d : ι → K) (v : S → K) :
    Nat.card {μ : V // (fun j : S => d j + φ μ j) = v} * Nat.card K ^ S.card = Nat.card V := by
  have h1 := card_affine_fiber_mul (restr φ S).toAddMonoidHom (h S hS) (fun j : S => d j) v
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at h1
  exact h1

variable [DecidableEq ι]

/-- One encoding, as a distribution, under `h`. The symbols of d + φ μ at a set of at
most b positions are uniform and independent for uniform μ, whatever d is. -/
theorem OntoUpTo.map_uniform [Fintype K] [Fintype V] {φ : V →ₗ[K] (ι → K)} {b : ℕ}
    (h : OntoUpTo φ b) {S : Finset ι} (hS : S.card ≤ b) (d : ι → K) :
    (PMF.uniformOfFintype V).map (fun μ => fun j : S => d j + φ μ j) =
      PMF.uniformOfFintype (S → K) :=
  map_uniform_of_surjective (restr φ S).toAddMonoidHom (h S hS) (fun j : S => d j)

/-- If the symbols of d + φ μ on S are uniform, for one d, then φ is onto on S. -/
theorem surjective_restr_of_map_uniform [Fintype K] [Fintype V] {φ : V →ₗ[K] (ι → K)}
    {S : Finset ι} (d : ι → K)
    (h : (PMF.uniformOfFintype V).map (fun μ => fun j : S => d j + φ μ j) =
      PMF.uniformOfFintype (S → K)) : Surjective (restr φ S) := by
  intro w
  have hmem : (fun j : S => d j + w j) ∈
      ((PMF.uniformOfFintype V).map fun μ => fun j : S => d j + φ μ j).support := by
    rw [h]
    exact PMF.mem_support_uniformOfFintype _
  obtain ⟨μ, -, hμ⟩ := (PMF.mem_support_map_iff _ _ _).1 hmem
  refine ⟨μ, funext fun j => ?_⟩
  exact add_left_cancel (congrFun hμ j)

/-- A b-query uniform encoder (P3): for every message and every set S of at most b positions, the
symbols of the encoding on S are uniform in K^S when the randomness is uniform. -/
def QueryUniform [Fintype K] [Fintype V] {M : Type*} (enc : M → V → ι → K) (b : ℕ) : Prop :=
  ∀ S : Finset ι, S.card ≤ b → ∀ m : M,
    (PMF.uniformOfFintype V).map (fun μ => fun j : S => enc m μ j) = PMF.uniformOfFintype (S → K)

/-- First characterisation. For a non-empty set of messages, an encoder m, μ ↦ ψ m + φ μ with φ
linear is b-query uniform if and only if φ is onto on every set of at most b positions. -/
theorem queryUniform_iff_ontoUpTo [Fintype K] [Fintype V] {M : Type*} [Nonempty M] (ψ : M → ι → K)
    (φ : V →ₗ[K] (ι → K)) (b : ℕ) : QueryUniform (fun m μ j => ψ m j + φ μ j) b ↔ OntoUpTo φ b :=
  ⟨fun h S hS => surjective_restr_of_map_uniform (ψ (Classical.arbitrary M)) (h S hS _),
    fun h _ hS m => h.map_uniform hS (ψ m)⟩

omit [DecidableEq ι] in
/-- Second characterisation. φ is onto on every set of at most b positions if and only if any at
most b rows of its matrix are linearly independent. Row j is the linear form μ ↦ φ μ j. -/
theorem ontoUpTo_iff_linearIndependent (φ : V →ₗ[K] (ι → K)) (b : ℕ) :
    OntoUpTo φ b ↔ ∀ S : Finset ι, S.card ≤ b →
      LinearIndependent K fun j : S => ((LinearMap.proj (j : ι)).comp φ : V →ₗ[K] K) := by
  classical
  refine forall_congr' fun S => imp_congr_right fun _ => ?_
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hs g hg j0
    obtain ⟨μ, hμ⟩ := hs (Pi.single j0 1)
    have h1 := LinearMap.congr_fun hg μ
    rw [LinearMap.sum_apply] at h1
    have h2 : ∀ j : S, (g j • ((LinearMap.proj (j : ι)).comp φ : V →ₗ[K] K)) μ =
        g j * (Pi.single j0 1 : S → K) j := by
      intro j
      rw [← hμ]
      rfl
    simpa [h2, Pi.single_apply] using h1
  · intro hg
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro ψ hψ
    have h0 : ∀ j : S, ψ (Pi.single j 1) = 0 := by
      refine hg (fun j => ψ (Pi.single j 1)) (LinearMap.ext fun μ => ?_)
      have h1 : ψ (restr φ S μ) = 0 := LinearMap.congr_fun hψ μ
      rw [LinearMap.sum_apply, LinearMap.zero_apply, ← h1,
        ← Finset.univ_sum_single (restr φ S μ), map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h3 : (Pi.single j (restr φ S μ j) : S → K) =
          restr φ S μ j • (Pi.single j 1 : S → K) := by
        ext j'
        simp [Pi.single_apply]
      rw [h3, map_smul, smul_eq_mul, mul_comm]
      rfl
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    simpa using h0 j

end One

/-! ## Part 3. A table of encodings with independent randomness -/

section Table

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι R : Type*}

/-- The table whose row a is φ (μ a), read at the positions of S: a position holds a column, one
symbol for each row. -/
def restrTable (φ : V →ₗ[K] (ι → K)) (R : Type*) (S : Finset ι) : (R → V) →+ (S → R → K) where
  toFun μ := fun j a => φ (μ a) j
  map_zero' := by
    funext j a
    simp
  map_add' μ μ' := by
    funext j a
    simp

theorem OntoUpTo.surjective_restrTable
    {φ : V →ₗ[K] (ι → K)} {b : ℕ} (h : OntoUpTo φ b) {S : Finset ι} (hS : S.card ≤ b) :
    Surjective (restrTable φ R S) := by
  intro w
  choose μ hμ using fun a : R => h S hS fun j => w j a
  exact ⟨μ, funext fun j => funext fun a => congrFun (hμ a) j⟩

/-- A table, as a count, under `h`. Let d a be the contribution of the message of row a,
S a set of at most b positions and v any pattern of columns on S. Of all families μ of randomness,
one vector for each row, exactly one in |K|^(|R| |S|) gives the table the pattern v on S. The
count does not depend on the messages. -/
theorem OntoUpTo.card_fiber_table [Finite K] [Finite V] [Finite R] {φ : V →ₗ[K] (ι → K)} {b : ℕ}
    (h : OntoUpTo φ b) {S : Finset ι} (hS : S.card ≤ b) (d : R → ι → K) (v : S → R → K) :
    Nat.card {μ : R → V // (fun (j : S) (a : R) => d a j + φ (μ a) j) = v} *
        (Nat.card K ^ Nat.card R) ^ S.card =
      Nat.card V ^ Nat.card R := by
  have h1 := card_affine_fiber_mul
    (restrTable φ R S) (h.surjective_restrTable hS) (fun (j : S) (a : R) => d a j) v
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fun,
    Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at h1
  exact h1

/-- A table, as a distribution, under `h`. The encodings of R messages with independent
uniform randomness: the columns at a set of at most b positions are uniform and independent,
whatever the messages. -/
theorem OntoUpTo.map_uniform_table [Fintype K] [Fintype V] [Fintype R] [DecidableEq R]
    [DecidableEq ι] {φ : V →ₗ[K] (ι → K)} {b : ℕ} (h : OntoUpTo φ b) {S : Finset ι}
    (hS : S.card ≤ b) (d : R → ι → K) :
    (PMF.uniformOfFintype (R → V)).map (fun μ => fun (j : S) (a : R) => d a j + φ (μ a) j) =
      PMF.uniformOfFintype (S → R → K) :=
  map_uniform_of_surjective (restrTable φ R S)
    (h.surjective_restrTable hS) (fun (j : S) (a : R) => d a j)

end Table

/-! ## Part 4. No more positions than uniform coordinates -/

/-- An encoder with r uniform coordinates hides at most r positions (if the code has that many
positions at all). -/
theorem OntoUpTo.le_card {K : Type*} [Field K] [Finite K] {ι ρ : Type*} [Fintype ι] [Fintype ρ]
    {φ : (ρ → K) →ₗ[K] (ι → K)} {b : ℕ} (h : OntoUpTo φ b) (hb : b ≤ Fintype.card ι) :
    b ≤ Fintype.card ρ := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := b)
    (by rw [Finset.card_univ]; exact hb)
  have h1 := Nat.card_le_card_of_surjective _ (h S hS.le)
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe, hS,
    Nat.card_eq_fintype_card (α := ρ)] at h1
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).1 h1

/-! ## Part 5. The same matrix over an extension field -/

section BaseChange

variable {F : Type*} [Field F] (E : Type*) [Field E] [Algebra F E] {ι : Type*}

/-- Let φ be linear over F and φE linear over E, and let φE extend φ: there is a map
`emb` of the domains with φE (emb μ) = φ μ, read in E. If φ is onto on every set of at most b
positions, so is φE. -/
theorem OntoUpTo.of_algebraMap {V VE : Type*} [AddCommGroup V] [Module F V] [AddCommGroup VE]
    [Module E VE] {φ : V →ₗ[F] (ι → F)} {b : ℕ} (h : OntoUpTo φ b) (φE : VE →ₗ[E] (ι → E))
    (emb : V → VE) (hemb : ∀ μ j, φE (emb μ) j = algebraMap F E (φ μ j)) : OntoUpTo φE b := by
  classical
  intro S hS w
  choose μ hμ using fun j0 : S => h S hS (Pi.single j0 1)
  refine ⟨∑ j0, w j0 • emb (μ j0), funext fun j => ?_⟩
  have h1 : ∀ j0 : S, φ (μ j0) j = (Pi.single j0 1 : S → F) j := fun j0 => congrFun (hμ j0) j
  rw [restr_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, hemb, smul_eq_mul, h1]
  simp [Pi.single_apply]

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]


/-- A linear map on tuples is given by its matrix. -/
theorem apply_eq_sum_single (φ : (ρ → F) →ₗ[F] (ι → F)) (μ : ρ → F) (j : ι) :
    φ μ j = ∑ i, φ (Pi.single i 1) j * μ i := by
  have h : φ μ = ∑ i, μ i • φ (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single μ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    congr 1
    ext i'
    simp [Pi.single_apply]
  rw [h, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm]


end BaseChange

end Code
