-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/SquaresSum.lean: what the layer of the sum of squares sums to.

The layer of Cb/Pv/Head/Squares.lean sums, over features and positions, the square of the limbs'
batch under the powers of an element g. This file shows that this sum is 2^-lPd times the batch,
under the same powers, of the nine sums of limb products W_s, extended over the positions at the
norm's point. It rests on the library's identity for the W_s (sum_pow_Wsum,
Inst/Model/Common/LedgerSound.lean) and on the evaluation of an extension in two steps
(Alg.mleN_append).

Main definitions: sqTrue.
Main theorems: ext_mleN, eqN_half, sq_sum, sq_end_value, sq_batch.

What is not claimed. Nothing on a protocol. 2 must not be 0 in the field.


-/
import Cb.Pv.Head.Squares
import Inst.Model.Common.LedgerSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Finset Inst.Model

section
variable {E : Type} [Field E]

/-- The two ways to write the extension of a vector that is indexed by numbers agree. -/
theorem ext_mleN (g : ℕ) (v : ℕ → E) (z : Fin g → E) :
    Blocks.ext g v (Blocks.nat z) = Alg.mleN v z := by
  unfold Blocks.ext Alg.mleN
  exact sum_congr rfl fun X _ => by rw [Blocks.eqN_nat]

/-- At a point all of whose coordinates are h, with 1 - h = h, every index has the weight h^n. -/
theorem eqN_half (n c : ℕ) (h : E) (hh : 1 - h = h) :
    Alg.eqN (fun _ : Fin n => h) c = h ^ n := by
  unfold Alg.eqN Alg.eqk
  simp [hh]

theorem one_sub_half (h2 : (2 : E) ≠ 0) : 1 - (2 : E)⁻¹ = (2 : E)⁻¹ := by
  have h := mul_inv_cancel₀ h2
  linear_combination (-1 : E) * h

variable {J : Type} (limb : (J → E) → ℕ → ℕ → E)

/-- The true value of sum number t: the sum W_t of limb products over all 2^lPd features, extended
over the positions at the point pv. -/
def sqTrue (s : SqSize) (m : J → E) (pv : Fin s.lt → E) (t : ℕ) : E :=
  Blocks.ext s.lt
    (fun a => Ledger.Wsum (2 ^ s.lPd) (fun l j => limb m l (2 ^ s.lt * j + a)) t) (Blocks.nat pv)

/-- The layer's sum is 2^-lPd times the batch of the nine true sums. -/
theorem sq_sum (s : SqSize) (h2 : (2 : E) ≠ 0) (g : E) (pv : Fin s.lt → E) (m : J → E) :
    ∑ b : Fin (s.lPd + s.lt) → Bool,
        Alg.eqk (Fin.append (fun _ : Fin s.lPd => (2 : E)⁻¹) pv) b *
          (sqVec limb g m (Alg.num b) * sqVec limb g m (Alg.num b)) =
      (2 : E)⁻¹ ^ s.lPd * ∑ t ∈ range 9, g ^ t * sqTrue limb s m pv t := by
  have key : ∀ a : ℕ,
      ∑ i ∈ range (2 ^ s.lPd),
          sqVec limb g m (2 ^ s.lt * i + a) * sqVec limb g m (2 ^ s.lt * i + a) =
        ∑ t ∈ range 9,
          g ^ t * Ledger.Wsum (2 ^ s.lPd) (fun l j => limb m l (2 ^ s.lt * j + a)) t := by
    intro a
    rw [Ledger.sum_pow_Wsum]
    exact sum_congr rfl fun i _ => (pow_two _).symm
  have e1 : ∑ i ∈ range (2 ^ s.lPd),
        Alg.mleN (fun a => sqVec limb g m (2 ^ s.lt * i + a) * sqVec limb g m (2 ^ s.lt * i + a))
          pv =
      ∑ t ∈ range 9, g ^ t * sqTrue limb s m pv t := by
    have e2 : ∑ i ∈ range (2 ^ s.lPd),
          Alg.mleN
            (fun a => sqVec limb g m (2 ^ s.lt * i + a) * sqVec limb g m (2 ^ s.lt * i + a)) pv =
        Blocks.ext s.lt (fun a => ∑ i ∈ range (2 ^ s.lPd),
          sqVec limb g m (2 ^ s.lt * i + a) * sqVec limb g m (2 ^ s.lt * i + a))
          (Blocks.nat pv) := by
      rw [Blocks.ext_sum]
      exact sum_congr rfl fun i _ => (ext_mleN _ _ _).symm
    rw [e2, funext key, Blocks.ext_sum]
    exact sum_congr rfl fun t _ => Blocks.ext_smul _ _ _ _
  calc ∑ b : Fin (s.lPd + s.lt) → Bool,
        Alg.eqk (Fin.append (fun _ : Fin s.lPd => (2 : E)⁻¹) pv) b *
          (sqVec limb g m (Alg.num b) * sqVec limb g m (Alg.num b))
      = Alg.mleN (fun c => sqVec limb g m c * sqVec limb g m c)
          (Fin.append (fun _ : Fin s.lPd => (2 : E)⁻¹) pv) :=
        (Alg.mleN_eq_mle (fun c => sqVec limb g m c * sqVec limb g m c) _).symm
    _ = ∑ i ∈ range (2 ^ s.lPd), Alg.eqN (fun _ : Fin s.lPd => (2 : E)⁻¹) i *
          Alg.mleN
            (fun a => sqVec limb g m (2 ^ s.lt * i + a) * sqVec limb g m (2 ^ s.lt * i + a)) pv :=
        Alg.mleN_append _ _ _
    _ = ∑ i ∈ range (2 ^ s.lPd), (2 : E)⁻¹ ^ s.lPd *
          Alg.mleN
            (fun a => sqVec limb g m (2 ^ s.lt * i + a) * sqVec limb g m (2 ^ s.lt * i + a)) pv :=
        sum_congr rfl fun i _ => by rw [eqN_half _ _ _ (one_sub_half h2)]
    _ = (2 : E)⁻¹ ^ s.lPd * ∑ t ∈ range 9, g ^ t * sqTrue limb s m pv t := by
        rw [← mul_sum, e1]

/-- The extension of the limbs' batch at a point, in two steps: over the features under the first
lPd coordinates, and for each feature over the positions under the last lt coordinates. -/
theorem sq_end_value (s : SqSize) (g : E) (m : J → E) (z : Fin (s.lPd + s.lt) → E) :
    Alg.mle (fun b => sqVec limb g m (Alg.num b)) z =
      ∑ j ∈ range (2 ^ s.lPd), Alg.eqN (fun i : Fin s.lPd => z (Fin.castAdd s.lt i)) j *
        Blocks.ext s.lt (fun a => sqVec limb g m (2 ^ s.lt * j + a))
          (Blocks.nat fun i : Fin s.lt => z (Fin.natAdd s.lPd i)) := by
  have hz : z = Fin.append (fun i : Fin s.lPd => z (Fin.castAdd s.lt i))
      (fun i : Fin s.lt => z (Fin.natAdd s.lPd i)) := (Fin.append_castAdd_natAdd).symm
  rw [← Alg.mleN_eq_mle (fun c => sqVec limb g m c) z]
  conv_lhs => rw [hz]
  rw [Alg.mleN_append]
  exact sum_congr rfl fun j _ => by rw [ext_mleN]

end

section
variable {E : Type} [Field E] [Fintype E] {J P : Type} [Fintype J] [DecidableEq J]
variable (limb : (J → E) → ℕ → ℕ → E) (slot : ℕ → J)

/-- The layer's claim at its target says that the nine hidden values and the nine true sums have
the same batch under the powers of g. -/
theorem sq_batch (s : SqSize) (h2 : (2 : E) ≠ 0) (st : SqSt E P s) (m : J → E) :
    (sqKind (P := P) limb slot s).par.SumHolds (sqTarget s st, st) m ↔
      ∑ t : Fin 9, st.g ^ (t : ℕ) * (st.sent t - m (slot t)) =
        ∑ t : Fin 9, st.g ^ (t : ℕ) * sqTrue limb s m st.pv t := by
  rw [sq_in, sq_sum limb s h2,
    ← Fin.sum_univ_eq_sum_range (fun t => st.g ^ t * sqTrue limb s m st.pv t) 9]
  have hp : (2 : E)⁻¹ ^ s.lPd ≠ 0 := pow_ne_zero _ (inv_ne_zero h2)
  have e : ∑ t : Fin 9, sqCoef s st.g t * (st.sent t - m (slot t)) =
      (2 : E)⁻¹ ^ s.lPd * ∑ t : Fin 9, st.g ^ (t : ℕ) * (st.sent t - m (slot t)) := by
    rw [mul_sum]
    exact sum_congr rfl fun t _ => by unfold sqCoef; ring
  rw [e]
  constructor
  · intro h
    exact (mul_left_cancel₀ hp h).symm
  · intro h
    rw [h]

end

end Cb.Pv.Head

#print axioms Cb.Pv.Head.sq_sum
#print axioms Cb.Pv.Head.sq_end_value
#print axioms Cb.Pv.Head.sq_batch
