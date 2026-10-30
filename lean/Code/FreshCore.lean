--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/FreshCore.lean: one row of random entries under a code with a random tail: the joint
distribution of three things that are made of it: the symbols at some positions, one out-of-domain
answer, and some of the entries themselves. A statement of linear algebra over a finite field; no
protocol occurs in it.

The row has a random tail t, one entry p that is the pad of the answer, and entries k i, for i in a
finite set J. All its other entries are fixed. Then, with fixed coefficients,
  the symbol at a position j of a set S is
      c0 j + (the tail's share at j + p bp j + the sum of k i bk i j),
  the answer is
      a0 + (beta p + the sum of ak i k i).
If the tail's shares take all patterns on S, and beta is not 0, the map from (t, p, k) to (the
symbols on S, the answer, c + k) is affine and ONTO. It is one to one only where S has as many
positions as the tail has entries. An affine map that is onto has fibres of one size, so it carries
the uniform distribution to the uniform distribution.

  freshHom, freshHom_onto   the linear part, and that it is onto
  fresh_core      **the statement**: whatever is made of (symbols on S, answer, c + k), over uniform
                  (t, p, k), has the distribution of the same made of a uniform triple

How it is meant to be read. With c := 0: the entries k are uniform and independent of the symbols on
S and of the answer. With J a single entry and c the value that a scalar lays under that entry: the
symbols, the answer and the scalar are jointly uniform. For several entries the third component is
c + k, entry by entry: scalars that are c' + M k for a matrix M are not of that form, and for them
the statement serves at c := 0 alone. The order in which the proof solves: k from the third
component, then p from the answer (beta is not 0), then t from the symbols.

What is assumed. The tail's shares take all patterns on S: Surjective (Code.restr phi S); for a set
of at most b positions that is Code.OntoUpTo phi b (Code/QueryUniform.lean), which ontoUpTo_gen
(Code/RS.lean) shows of a tail of b entries at distinct points. S counts DISTINCT positions, over
all lists at which the row is read. beta is not 0.
What is not claimed. That any code, row, answer or scalar of a protocol has this form. That an
honest prover samples t, p and k uniformly. How many positions of a row a run reads. Nothing on what
else hangs on these values. No property of a protocol is claimed.

-/
import Code.QueryUniform
import Prob.LawKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Code

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι J : Type} [Fintype J]

/-- The linear part of the map from (tail, pad, entries) to (symbols on S, answer, entries). -/
def freshHom (φ : V →ₗ[K] (ι → K)) (S : Finset ι) (bp : S → K) (bk : J → S → K) (ak : J → K)
    (β : K) : V × K × (J → K) →+ (S → K) × K × (J → K) :=
  AddMonoidHom.mk'
    (fun x => (fun j => φ x.1 j.1 + x.2.1 * bp j + ∑ i, x.2.2 i * bk i j,
      β * x.2.1 + ∑ i, ak i * x.2.2 i, x.2.2))
    (by
      intro a b
      refine Prod.ext ?_ (Prod.ext ?_ rfl)
      · funext j
        show φ (a.1 + b.1) j.1 + (a.2.1 + b.2.1) * bp j + ∑ i, (a.2.2 i + b.2.2 i) * bk i j =
          (φ a.1 j.1 + a.2.1 * bp j + ∑ i, a.2.2 i * bk i j) +
            (φ b.1 j.1 + b.2.1 * bp j + ∑ i, b.2.2 i * bk i j)
        simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      · show β * (a.2.1 + b.2.1) + ∑ i, ak i * (a.2.2 i + b.2.2 i) =
          (β * a.2.1 + ∑ i, ak i * a.2.2 i) + (β * b.2.1 + ∑ i, ak i * b.2.2 i)
        simp only [mul_add, Finset.sum_add_distrib]
        ring)

/-- It is onto, if the tail's shares take all patterns on S and beta is not 0. -/
theorem freshHom_onto (φ : V →ₗ[K] (ι → K)) (S : Finset ι)
    (hS : Function.Surjective (restr φ S)) (bp : S → K) (bk : J → S → K) (ak : J → K) (β : K)
    (hβ : β ≠ 0) : Function.Surjective (freshHom φ S bp bk ak β) := by
  rintro ⟨s, y, k⟩
  obtain ⟨t, ht⟩ := hS fun j => s j - (y - ∑ i, ak i * k i) / β * bp j - ∑ i, k i * bk i j
  refine ⟨(t, (y - ∑ i, ak i * k i) / β, k), ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext j
    have e : φ t j.1 = s j - (y - ∑ i, ak i * k i) / β * bp j - ∑ i, k i * bk i j := congrFun ht j
    show φ t j.1 + (y - ∑ i, ak i * k i) / β * bp j + ∑ i, k i * bk i j = s j
    rw [e]
    ring
  · have h : β * ((y - ∑ i, ak i * k i) / β) = y - ∑ i, ak i * k i := by
      rw [mul_comm, div_mul_cancel₀ _ hβ]
    show β * ((y - ∑ i, ak i * k i) / β) + ∑ i, ak i * k i = y
    rw [h]
    ring

/-- **Over uniform (tail, pad, entries), whatever is made of (the symbols on S, the answer, c + the
entries) has the distribution of the same made of a uniform triple.** -/
theorem fresh_core [Fintype K] [Fintype V] [DecidableEq ι] [DecidableEq J] {γ : Type}
    (φ : V →ₗ[K] (ι → K)) (S : Finset ι) (hS : Function.Surjective (restr φ S))
    (bp c0 : S → K) (bk : J → S → K) (ak c : J → K) (a0 β : K) (hβ : β ≠ 0)
    (f : (S → K) × K × (J → K) → γ) :
    (Prob.unif (V × K × (J → K))).map (fun x => f
        (fun j => c0 j + (φ x.1 j.1 + x.2.1 * bp j + ∑ i, x.2.2 i * bk i j),
          a0 + (β * x.2.1 + ∑ i, ak i * x.2.2 i), fun i => c i + x.2.2 i)) =
      (Prob.unif ((S → K) × K × (J → K))).map f := by
  have h := map_uniform_of_surjective (freshHom φ S bp bk ak β)
    (freshHom_onto φ S hS bp bk ak β hβ) (c0, a0, c)
  have e : (Prob.unif (V × K × (J → K))).map (fun x => f
        (fun j => c0 j + (φ x.1 j.1 + x.2.1 * bp j + ∑ i, x.2.2 i * bk i j),
          a0 + (β * x.2.1 + ∑ i, ak i * x.2.2 i), fun i => c i + x.2.2 i)) =
      ((Prob.unif (V × K × (J → K))).map
        (fun x => (c0, a0, c) + freshHom φ S bp bk ak β x)).map f := by
    rw [PMF.map_comp]
    rfl
  rw [e, h]

end Code

#print axioms Code.freshHom_onto
#print axioms Code.fresh_core
