-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/EmbSide.lean: the extension over both indices of Cb/Pv/Lay/Emb.lean, written out as the
sum that the programs' two claims on the embedding add up to.

The programs read the stream that comes in, and the embedding's rows, at a feature's high part kh
under the equality vector of one drawn point, at its low part r and at the position p under the
equality vectors of the other (OnBytes/Model/Layer.lean, claimEmbedding;
OnBytes/Model/LayerPanels.lean, claimE). A feature is kh 2^ls + r; only nb high parts occur.

Main names:
  embGap nb ls lT f: the gaps of Cb/Pv/Lay/Emb.lean from a function f of a feature and a position:
    at U, V it is f (V 2^ls + U / 2^lT) (U % 2^lT) if V is below nb, else 0.
  emb_side: the extension of embGap over both indices, at the points pa and pb, is the sum over kh
    below nb, r below 2^ls and p below 2^lT of the three equality weights times f (kh 2^ls + r) p.
  emb_zero: all gaps vanish on the two cubes if and only if f vanishes at every feature kh 2^ls +
    r with kh below nb, r below 2^ls, and every position below 2^lT.

Limits. Sums and indices alone: no protocol, no claim of the programs occurs here. Nothing is said
on hiding.
-/
import Cb.Pv.Lay.Emb
import Cb.Pv.Att.Step18Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Finset

variable {E : Type} [Field E]

/-- The gaps, from a function of a feature and a position. -/
def embGap (nb ls lT : ℕ) (f : ℕ → ℕ → E) (U V : ℕ) : E :=
  if V < nb then f (V * 2 ^ ls + U / 2 ^ lT) (U % 2 ^ lT) else 0

/-- The extension over both indices, written out. -/
theorem emb_side (nb ls lT gB : ℕ) (hnb : nb ≤ 2 ^ gB) (f : ℕ → ℕ → E) (pa pb : ℕ → E) :
    Blocks.ext gB (fun V => Blocks.ext (ls + lT) (fun U => embGap nb ls lT f U V) pa) pb =
      ∑ kh ∈ range nb, Blocks.eqN gB 0 pb kh *
        ∑ r ∈ range (2 ^ ls), Blocks.eqN ls 0 pa r *
          ∑ p ∈ range (2 ^ lT), Blocks.eqN lT ls pa p * f (kh * 2 ^ ls + r) p := by
  unfold Blocks.ext
  refine (Finset.sum_subset (Finset.range_subset_range.2 hnb) fun V _ hV => ?_).symm.trans ?_
  · have hV' : ¬ V < nb := fun h => hV (mem_range.2 h)
    simp only [embGap, if_neg hV', mul_zero, sum_const_zero]
  · refine sum_congr rfl fun kh hkh => ?_
    congr 1
    have e := Cb.Pv.Att.ext_two ls lT (fun r p => f (kh * 2 ^ ls + r) p) pa
    unfold Blocks.ext at e
    simp only [embGap, if_pos (mem_range.1 hkh)]
    rw [e]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun p _ => mul_assoc _ _ _

/-- What the vanishing of all gaps says. -/
theorem emb_zero (nb ls lT gB : ℕ) (hnb : nb ≤ 2 ^ gB) (f : ℕ → ℕ → E) :
    (∀ V < 2 ^ gB, ∀ U < 2 ^ (ls + lT), embGap nb ls lT f U V = 0) ↔
      ∀ kh < nb, ∀ r < 2 ^ ls, ∀ p < 2 ^ lT, f (kh * 2 ^ ls + r) p = 0 := by
  have hp : 0 < 2 ^ lT := Nat.two_pow_pos lT
  constructor
  · intro h kh hkh r hr p hpp
    have hU : r * 2 ^ lT + p < 2 ^ (ls + lT) := by
      rw [pow_add]
      calc r * 2 ^ lT + p < r * 2 ^ lT + 2 ^ lT := Nat.add_lt_add_left hpp _
        _ = (r + 1) * 2 ^ lT := by ring
        _ ≤ 2 ^ ls * 2 ^ lT := Nat.mul_le_mul_right _ hr
    have e := h kh (lt_of_lt_of_le hkh hnb) (r * 2 ^ lT + p) hU
    have e1 : (r * 2 ^ lT + p) / 2 ^ lT = r := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hpp, Nat.zero_add]
    have e2 : (r * 2 ^ lT + p) % 2 ^ lT = p := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpp]
    simpa only [embGap, if_pos hkh, e1, e2] using e
  · intro h V _ U hU
    unfold embGap
    split
    · rename_i hV
      refine h V hV _ ?_ _ (Nat.mod_lt _ hp)
      rw [pow_add] at hU
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hU)
    · rfl

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.emb_side
#print axioms Cb.Pv.Lay.emb_zero
