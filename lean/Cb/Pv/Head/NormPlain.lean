-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/NormPlain.lean: the claim from which the chain of Cb/Pv/Head/Norm.lean starts is the
library's clause on the 17 identities of the head's final norm.

Norm.lean states the identities on two letters: the stream's limbs at an index that joins feature
and position, over all 2^lPd padded features, and the digits of a row. Here the letters are filled
from the library's cells of the head (Inst/Model/Head/Trace.lean: Cells, bl, Dv): a limb is the
cell's value below the model's width and 0 from there on. At the reference sizes (1,024 positions,
width 5,120, padded to 8,192) the chain's first claim is then that the library's 17 identities
(Inst/Model/Head/TraceN.lean: idn) are 0 at every position, at the cells t m. The identities of the
plain head (Cm/Head.lean: idn, the clause idns of its relation RF) have the same text.

Main definitions: limbOf, digOf.
Main theorems: wsum_pad, wsum_congr, limbOf_at, normIdn_plain, norm_start_iff, idn_cast,
norm_start_cast.

What is not claimed. t, the reading of the committed entries as cells over the challenge field, is a
letter. That these cells are casts of small integers, which the library's relation asks beside the
identities, is the matter of the smallness test. Nothing is said about hiding.


-/
import Cb.Pv.Head.Norm
import Inst.Model.Head.NoWrapProgramN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Finset Inst.Model

/-- Features at which all limbs are 0 add nothing to a sum of limb products. -/
theorem wsum_pad {K : Type} [CommRing K] {d D : ℕ} (h : d ≤ D) (b : ℕ → ℕ → K)
    (hb : ∀ l j, d ≤ j → b l j = 0) (s : ℕ) : Ledger.Wsum D b s = Ledger.Wsum d b s := by
  unfold Ledger.Wsum
  refine (sum_subset (range_subset_range.2 h) fun j _ hj => ?_).symm
  have hj' : d ≤ j := Nat.le_of_not_lt fun hlt => hj (mem_range.2 hlt)
  have h0 : ∀ l, b l j = 0 := fun l => hb l j hj'
  simp [h0]

/-- A sum of limb products reads the limbs below the width alone. -/
theorem wsum_congr {K : Type} [CommRing K] {d : ℕ} {b b' : ℕ → ℕ → K}
    (h : ∀ l j, j < d → b l j = b' l j) (s : ℕ) : Ledger.Wsum d b s = Ledger.Wsum d b' s := by
  unfold Ledger.Wsum
  refine sum_congr rfl fun j hj => ?_
  have h0 : ∀ l, b l j = b' l j := fun l => h l j (mem_range.1 hj)
  simp only [h0]

section
variable {E : Type} [Field E] {J : Type} (t : (J → E) → Head.Cells E)

/-- The stream's limbs at the index 2^lt j + a: the cell's value for a feature j below the width d,
and 0 from there on. -/
def limbOf (lt d : ℕ) : (J → E) → ℕ → ℕ → E := fun m l c =>
  if c / 2 ^ lt < d then Head.bl (t m) l (c / 2 ^ lt) (c % 2 ^ lt) else 0

/-- The digits of a row. -/
def digOf : (J → E) → ℕ → ℕ → E := fun m n a => Head.Dv (t m) n a

theorem limbOf_at (lt d : ℕ) (m : J → E) (l j : ℕ) {a : ℕ} (ha : a < 2 ^ lt) :
    limbOf t lt d m l (2 ^ lt * j + a) = if j < d then Head.bl (t m) l j a else 0 := by
  have h1 : (2 ^ lt * j + a) / 2 ^ lt = j := by
    rw [Nat.mul_add_div (Nat.two_pow_pos lt), Nat.div_eq_of_lt ha, Nat.add_zero]
  have h2 : (2 ^ lt * j + a) % 2 ^ lt = a := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ha]
  unfold limbOf
  rw [h1, h2]

/-- At the reference sizes an identity of Norm.lean is the library's identity of the plain head. -/
theorem normIdn_plain (np : NormPar) (m : J → E) (k : ℕ) {a : ℕ} (ha : a < 2 ^ 10) :
    normIdn np (limbOf t 10 Head.nD) (digOf t) ⟨10, 13⟩ m k a = Head.N.idn np (t m) a k := by
  have e : Ledger.Wsum (2 ^ 13) (fun l j => limbOf t 10 Head.nD m l (2 ^ 10 * j + a)) =
      Ledger.Wsum Head.nD fun l j => Head.bl (t m) l j a := by
    funext s
    rw [wsum_pad (d := Head.nD) (by norm_num [Head.nD]) _ (fun l j hj => by
      rw [limbOf_at t 10 Head.nD m l j ha, if_neg (Nat.not_lt.2 hj)])]
    exact wsum_congr (fun l j hj => by rw [limbOf_at t 10 Head.nD m l j ha, if_pos hj]) s
  show Ledger.idn np (Ledger.Wsum (2 ^ 13) fun l j => limbOf t 10 Head.nD m l (2 ^ 10 * j + a))
    (fun n => Head.Dv (t m) n a) k = _
  rw [e]
  rfl

/-- The chain's first claim, at the reference sizes, is the clause on the identities. -/
theorem norm_start_iff (np : NormPar) (m : J → E) :
    (∀ k < 17, ∀ X < 2 ^ 10, normIdn np (limbOf t 10 Head.nD) (digOf t) ⟨10, 13⟩ m k X = 0) ↔
      ∀ i < Head.nT, ∀ k < 17, Head.N.idn np (t m) i k = 0 := by
  have hT : Head.nT = 2 ^ 10 := by norm_num [Head.nT]
  constructor
  · intro h i hi k hk
    have hi' : i < 2 ^ 10 := hT ▸ hi
    rw [← normIdn_plain t np m k hi']
    exact h k hk i hi'
  · intro h k hk X hX
    rw [normIdn_plain t np m k hX]
    exact h X (hT ▸ hX) k hk

/-- If the cells over the challenge field are the images of cells over a ring F under a one-to-one
ring homomorphism, the identities are 0 over the field exactly if they are 0 over F. -/
theorem idn_cast {F : Type} [CommRing F] (f : F →+* E) (hf : Function.Injective f) (np : NormPar)
    (t0 : Head.Cells F) (i k : ℕ) :
    Head.N.idn np (t0.map f) i k = 0 ↔ Head.N.idn np t0 i k = 0 := by
  rw [← Head.N.map_idn' f np t0 i k]
  exact map_eq_zero_iff f hf

/-- The chain's first claim, at the reference sizes, where the cells over the challenge field are
the
images of cells t0 over a ring F: the 17 identities are 0 over F at every position. -/
theorem norm_start_cast {F : Type} [CommRing F] (f : F →+* E) (hf : Function.Injective f)
    (np : NormPar) (m : J → E) (t0 : Head.Cells F) (ht : t m = t0.map f) :
    (∀ k < 17, ∀ X < 2 ^ 10, normIdn np (limbOf t 10 Head.nD) (digOf t) ⟨10, 13⟩ m k X = 0) ↔
      ∀ i < Head.nT, ∀ k < 17, Head.N.idn np t0 i k = 0 := by
  refine (norm_start_iff t np m).trans ?_
  rw [ht]
  exact ⟨fun h i hi k hk => (idn_cast f hf np t0 i k).1 (h i hi k hk),
    fun h i hi k hk => (idn_cast f hf np t0 i k).2 (h i hi k hk)⟩

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.norm_start_iff
#print axioms Cb.Pv.Head.idn_cast
#print axioms Cb.Pv.Head.norm_start_cast
