-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfKeys.lean: algebra of multilinear extensions for the lookups on the index.
Key maps that are affine in the columns of the matrix of the index meet the law "a key map is
linear" of the preamble of weights-formedness, whatever the matrix is, with number of variables,
constant, row factor and point as `P.LinKeys` fixes them.

Definitions, statements (in `Cb.Spec`) and proofs. No protocol.

Why: Cb/Ld/LdWf.lean asks (`Laws.keyLin`): the multilinear extension of the keys of a forest at a
point is a public constant plus a tensor form in "the matrix of the index" `P.mat U`.
Cb/Obj/LdObjectWf.lean asks (`Tie`): `P.mat U` is the index matrix in the layout of the encoded
index. Can both hold?
`Tie` says what `P.mat` is. The law holds for every `P.mat` if the keys are what this library takes
them to be (Cb/Gen/WfKeys.lean: `Keys.key`): key number b = u · 2^k + c of forest f is
        o f u  +  ∑_r co f u r · (P.mat U) (r, column c):
an affine function of one column, with public offsets o and coefficients co, u < 2^(rv f) a row of
keys, c < 2^k a column.

Main names:
  `P.LinKeys rv o co`: five families of equations between values that say so: the number of
    variables is rv f + k; the keys; the public constant is the extension of the offsets at the row
    part of the point (its first rv f coordinates); the row factor is the extension of the
    coefficients there; the point of the column factor is the column part.
  `Spec.ldWfK_ext`: the mathematics: the extension of keys that are affine in one column is the
    extension of the offsets plus a tensor form.
  `Spec.ldWfK_keyLin`: `P.LinKeys rv o co` gives the clause `keyLin` of `P.Laws`. Nothing is asked
    of `P.mat`: so it holds beside `Tie`, in every layout.

Notation: a column c < 2^k is the corner `Alg.bits k c` (top bit first), as `Blocks.ext` lists
points. The mathematics is that of Blocks/RngPlan.lean (`Plan.ext_key`), with rows named by any
finite type and the column sum written as `Alg.mle`.

Limits: this file does not say that the lookups describe the index set (`Laws.describes`). That is a
condition on the model. This file says nothing on the cost of evaluating constant and row factor.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWf

set_option autoImplicit false

namespace Cb
open Finset Blocks

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : Hiop.ConfigurationWithOutOfDomainSample} (P : LdWfP E C)

/-- The key maps are affine in the columns of the matrix of the index. -/
structure LinKeys (rv : ℕ → ℕ) (o : ℕ → ℕ → E) (co : ℕ → ℕ → P.Rw → E) : Prop where
  v   : ∀ f, f ≤ P.n → P.v f = rv f + P.k
  key : ∀ f, f ≤ P.n →
    ∀ U b, b < 2 ^ (rv f + P.k) →
      P.key f U b =
        o f (b / 2 ^ P.k) + ∑ r, co f (b / 2 ^ P.k) r * P.mat U (r, Alg.bits P.k (b % 2 ^ P.k))
  off : ∀ f, f ≤ P.n → ∀ z, P.off f z = ext (rv f) (o f) z
  gOf : ∀ f, f ≤ P.n → ∀ z r, P.gOf f z r = ext (rv f) (fun u => co f u r) z
  cOf : ∀ f, f ≤ P.n → ∀ z i, P.cOf f z i = z (rv f + (i : ℕ))

end LdWfP

namespace Spec

/-- The extension of keys that are affine in one column is the extension of the offsets plus a
tensor form. -/
def ldWfK_ext : Prop :=
  ∀ (E Rw : Type) [Field E] [Fintype Rw] (R k : ℕ) (o : ℕ → E) (co : ℕ → Rw → E)
    (M : Rw × (Fin k → Bool) → E) (z : ℕ → E),
    ext (R + k) (fun b => o (b / 2 ^ k) + ∑ r, co (b / 2 ^ k) r * M (r, Alg.bits k (b % 2 ^ k))) z =
      ext R o z +
        Alg.mle (fun c => ∑ r, ext R (fun u => co u r) z * M (r, c))
          (fun i : Fin k => z (R + (i : ℕ)))

/-- Under `P.LinKeys rv o co`, the clause `keyLin` of `P.Laws` holds, whatever the matrix is. -/
def ldWfK_keyLin : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (C : Hiop.ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (rv : ℕ → ℕ)
      (o : ℕ → ℕ → E) (co : ℕ → ℕ → P.Rw → E),
    P.LinKeys rv o co →
    ∀ f, f ≤ P.n →
      ∀ U z, ext (P.v f) (P.key f U) z =
        P.off f z + Alg.mle (fun c => ∑ r, P.gOf f z r * P.mat U (r, c)) (P.cOf f z)

/-- Under `P.LinKeys rv o co`, such keys read the index through its matrix alone: two messages with
the same matrix have the same keys. (So, beside `Tie`, no key reads a place off the layout of the
matrix.) -/
def ldWfK_reads : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (C : Hiop.ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (rv : ℕ → ℕ)
      (o : ℕ → ℕ → E) (co : ℕ → ℕ → P.Rw → E),
    P.LinKeys rv o co →
    ∀ U U', P.mat U = P.mat U' → ∀ f, f ≤ P.n → ∀ b, b < 2 ^ P.v f → P.key f U b = P.key f U' b

end Spec

theorem ldWfK_ext : Spec.ldWfK_ext := by
  intro E Rw _ _ R k o co M z
  have hpos : 0 < 2 ^ k := by positivity
  have hone : ∑ c ∈ range (2 ^ k), eqN k R z c = 1 := by
    simp only [eqN_eq]
    exact Alg.sum_eqN _
  have hm : Alg.mle (fun c => ∑ r, ext R (fun u => co u r) z * M (r, c))
        (fun i : Fin k => z (R + (i : ℕ))) =
      ∑ c ∈ range (2 ^ k), eqN k R z c * ∑ r, ext R (fun u => co u r) z * M (r, Alg.bits k c) := by
    rw [← Alg.sum_num (fun c => eqN k R z c * ∑ r, ext R (fun u => co u r) z * M (r, Alg.bits k c))]
    unfold Alg.mle
    refine sum_congr rfl fun b _ => ?_
    rw [eqN_eq, Alg.eqN_num, Alg.bits_num]
  have hterm : ∀ i, ∀ c ∈ range (2 ^ k), eqN (R + k) 0 z (i * 2 ^ k + c) *
        (o ((i * 2 ^ k + c) / 2 ^ k) +
          ∑ r, co ((i * 2 ^ k + c) / 2 ^ k) r * M (r, Alg.bits k ((i * 2 ^ k + c) % 2 ^ k))) =
      eqN R 0 z i * o i * eqN k R z c +
        eqN k R z c * ∑ r, (eqN R 0 z i * co i r) * M (r, Alg.bits k c) := by
    intro i c hc
    have hc' := mem_range.mp hc
    have h1 : (i * 2 ^ k + c) / 2 ^ k = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hc', Nat.zero_add]
    have h2 : (i * 2 ^ k + c) % 2 ^ k = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc']
    have h3 := eqN_append' R k 0 z i hc'
    rw [Nat.zero_add] at h3
    rw [h1, h2, h3, mul_add, mul_sum, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun r _ => by ring
  have hL : ext (R + k)
        (fun b => o (b / 2 ^ k) + ∑ r, co (b / 2 ^ k) r * M (r, Alg.bits k (b % 2 ^ k))) z =
      ∑ i ∈ range (2 ^ R), ∑ c ∈ range (2 ^ k), (eqN R 0 z i * o i * eqN k R z c +
        eqN k R z c * ∑ r, (eqN R 0 z i * co i r) * M (r, Alg.bits k c)) := by
    unfold Blocks.ext
    rw [pow_add, Alg.sum_range_mul_add]
    exact sum_congr rfl fun i _ => sum_congr rfl (hterm i)
  rw [hL, hm]
  simp only [sum_add_distrib]
  congr 1
  · unfold Blocks.ext
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_sum, hone, mul_one]
  · rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    unfold Blocks.ext
    rw [sum_mul]

theorem ldWfK_keyLin : Spec.ldWfK_keyLin := by
  intro E _ _ C P rv o co h f hf U z
  have e1 : ext (P.v f) (P.key f U) z =
      ext (rv f + P.k)
        (fun b =>
          o f (b / 2 ^ P.k) + ∑ r, co f (b / 2 ^ P.k) r * P.mat U (r, Alg.bits P.k (b % 2 ^ P.k)))
        z := by
    rw [h.v f hf]
    exact ext_congr (fun b hb => h.key f hf U b hb) z
  have e2 : P.cOf f z = fun i : Fin P.k => z (rv f + (i : ℕ)) := funext (h.cOf f hf z)
  have e3 : (fun c => ∑ r, P.gOf f z r * P.mat U (r, c)) =
      fun c => ∑ r, ext (rv f) (fun u => co f u r) z * P.mat U (r, c) :=
    funext fun c => sum_congr rfl fun r _ => by rw [h.gOf f hf z r]
  rw [e1, e2, e3, h.off f hf z]
  exact ldWfK_ext E P.Rw (rv f) P.k (o f) (co f) (P.mat U) z

theorem ldWfK_reads : Spec.ldWfK_reads := by
  intro E _ _ C P rv o co h U U' hU f hf b hb
  rw [h.v f hf] at hb
  rw [h.key f hf U b hb, h.key f hf U' b hb, hU]

end Cb
