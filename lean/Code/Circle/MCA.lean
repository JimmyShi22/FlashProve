-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Circle/MCA.lean: mutual correlated agreement of circle codes up to half the distance.

The statements hold for every field L in which 2 ≠ 0 (in `mca_range_gen` L and the set of points are
finite) and for all points z_I of the circle that satisfy `CirclePoints` (Code/Circle/Basis.lean:
they are distinct, and none is the point (-1, 0)).

 * `range_gen_le`: the circle code of any dimension k is in the generalised Reed–Solomon code of
   the polynomials of degree at most 2⌊k/2⌋ at the points θ_I = y / (1 + x) of L (`theta`,
   Code/Circle/Basis.lean) with the column multipliers η_I (`eta`, Code/Circle/GRS.lean).
 * `range_gen_odd`: for odd k = 2N + 1 the two codes are equal.
 * `mca_range_gen`: if 2e < n - 2⌊k/2⌋, at most n values of the line's parameter are bad (`MCA`,
   Code/Agree.lean), for any number of interleaved rows. For odd k (`range_gen_odd`) this is
   `mca_monomialImage_rsCode` (Code/Half.lean); for even k the code is a subcode of the code of
   dimension k + 1. (The proof takes the subcode step, `range_gen_le`, for every k.)

Notation:
  `gen z k` (Code/Circle/GRS.lean): a linear map: the generator of the circle code of dimension k at
    the points z: the coefficients a go to the values of ∑_(i < k) a_i bas_i at the points; the
    circle code is its range (`LinearMap.range (gen z k)`);
  n: a natural number, the number of points (`Fintype.card P`);
  e: a natural number, the radius (`MCA`, Code/Agree.lean);
  bad (`MCA`, Code/Agree.lean): for interleaved words f₀ and f₁, said of a value θ of the line's
    parameter that admits a set S of all but at most e positions on which every row of f₀ + θ f₁
    agrees with a word of the code, while not all rows of f₀ and of f₁ do.
-/
import Code.Half
import Code.Circle.GRS

set_option autoImplicit false

namespace Code.Circle

open Polynomial Function

variable {L P : Type} [Field L]

/-- The points θ_I as an embedding. -/
def thetaEmb (h2 : (2 : L) ≠ 0) {z : P → Circ L} (hz : CirclePoints z) : P ↪ L :=
  ⟨fun I => theta (z I), hz.theta_injective h2⟩

/-- The generalised Reed–Solomon code: the words (η_I p(θ_I))_I for the polynomials p of degree at
most 2N. -/
abbrev grs (h2 : (2 : L) ≠ 0) {z : P → Circ L} (hz : CirclePoints z) (N : ℕ) :
    Submodule L (P → L) :=
  monomialImage (Equiv.refl P) (eta N z) (eta_ne_zero h2 hz N) (rsCode (thetaEmb h2 hz) (2 * N))

/-- For 2 ≠ 0 and points that satisfy `CirclePoints`: the circle code of dimension k is in the
generalised Reed–Solomon code with N = ⌊k/2⌋. -/
theorem range_gen_le (h2 : (2 : L) ≠ 0) {z : P → Circ L} (hz : CirclePoints z) (k : ℕ) :
    LinearMap.range (gen z k) ≤ grs h2 hz (k / 2) := by
  rintro _ ⟨a, rfl⟩
  have hB : k ≤ 2 ^ (k + 1) :=
    (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
  refine ⟨fun I => (wordPoly k k a).eval (theta (z I)),
    ⟨wordPoly k k a, wordPoly_natDegree_le_two_mul k k hB a, fun _ => rfl⟩,
    ?_⟩
  funext I
  exact (gen_eq_eval h2 hz hB a I).symm

/-- Under the conditions of `range_gen_le` the circle code of odd dimension 2N + 1 is the
generalised Reed–Solomon code of the polynomials of degree at most 2N at the points θ_I, with the
column multipliers η_I. -/
theorem range_gen_odd (h2 : (2 : L) ≠ 0) {z : P → Circ L} (hz : CirclePoints z) (N : ℕ) :
    LinearMap.range (gen z (2 * N + 1)) = grs h2 hz N := by
  apply le_antisymm
  · have h := range_gen_le h2 hz (2 * N + 1)
    have h3 : (2 * N + 1) / 2 = N := by omega
    rwa [h3] at h
  · rintro _ ⟨w, ⟨p, hp, hw⟩, rfl⟩
    refine ⟨(toRS h2 N).symm fun i => p.coeff i, funext fun I => ?_⟩
    have hdeg : p.degree < ((2 * N + 1 : ℕ) : WithBot ℕ) :=
      lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (by omega : p.natDegree < 2 * N + 1))
    rw [gen_eq_scaled_rs h2 hz, LinearEquiv.apply_symm_apply, RS.gen_coeff hdeg]
    show _ = eta N z I * w I
    rw [hw I]
    rfl

variable [Fintype P] [Finite L]

/-- Under the conditions of `range_gen_le`, for a finite field and finitely many points: if 2e < n -
2⌊k/2⌋, which is the minimum distance or a lower bound for it, then the circle code of dimension k
has mutual correlated agreement on lines at the radius e with at most n bad values, for any number
of interleaved rows. -/
theorem mca_range_gen (h2 : (2 : L) ≠ 0) {z : P → Circ L} (hz : CirclePoints z) {k e : ℕ}
    (he : 2 * e < Fintype.card P - 2 * (k / 2)) :
    MCA (LinearMap.range (gen z k)) e (Fintype.card P) := by
  have h := mca_monomialImage_rsCode (thetaEmb h2 hz) (e := e) (K := 2 * (k / 2)) (by omega)
    (Equiv.refl P) (eta (k / 2) z) (eta_ne_zero h2 hz (k / 2))
  have hd : MinDist (grs h2 hz (k / 2)) (Fintype.card P - 2 * (k / 2)) :=
    (minDist_monomial _ _ _ _ _).2 (minDist_rsCode (thetaEmb h2 hz) (2 * (k / 2)))
  exact fun R _ => MCAOn.subcode hd he (range_gen_le h2 hz k) (by omega) (by omega) (h R)

end Code.Circle
