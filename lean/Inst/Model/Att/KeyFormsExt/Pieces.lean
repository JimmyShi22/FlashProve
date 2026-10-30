-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/Pieces.lean: the multilinear extension of a vector of two families of
pieces and padding.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `ext_split'`: an extension over two-part indices (x | y) is the extension over x of the extensions
    over y (from `Blocks.ext_two`, Blocks/LookupCalls.lean).
  `blk`, `blk_ext`: nb pieces of 2^l entries from block number n0 on, and 0 elsewhere; its extension
    is the sum over b < nb of eq(the first coordinates, n0 + b) times the extension of the b-th of
    them at the last l coordinates.
  `twoFam_eq`, `twoFam_ext`: the vector `twoFam nb l l' f f' pad` (Inst/Model/Att/Trace.lean) as two
    blocks and a padded rest; its extension is the two weighted sums plus pad times (1 - the two
    sums of weights). This is the form of `wp`, `inn`, `LL` (Inst/Model/Att/Points.lean).
Limits: `blk_ext` stands under n0 + nb ≤ 2^g; `twoFam_ext` under l' ≤ l ≤ a and nb 2^l + nb 2^l' ≤
2^a. pad is the padding value of a lookup table. Coordinate 0 of a point belongs to the most
significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyForms
import Blocks.LookupCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

theorem ext_def (g : ℕ) (v pt : ℕ → E) :
    Blocks.ext g v pt = ∑ X ∈ range (2 ^ g), Blocks.eqN g 0 pt X * v X := rfl

/-- An extension over two-part indices (x | y) is the extension over x of the extensions over y. -/
theorem ext_split' (g g' : ℕ) (v pt : ℕ → E) :
    Blocks.ext (g + g') v pt =
      Blocks.ext g (fun x => Blocks.ext g' (fun y => v (x * 2 ^ g' + y)) (AttSeg.sh pt g)) pt := by
  rw [Blocks.ext_two]
  unfold Blocks.ext
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e : Blocks.eqN g' g pt y = Blocks.eqN g' 0 (AttSeg.sh pt g) y := by
    unfold Blocks.eqN AttSeg.sh
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Nat.zero_add]
  rw [e, mul_assoc]

theorem div_pow (l x : ℕ) {y : ℕ} (hy : y < 2 ^ l) : (x * 2 ^ l + y) / 2 ^ l = x := by
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos l), Nat.div_eq_of_lt hy, Nat.add_zero]

theorem mod_pow (l x : ℕ) {y : ℕ} (hy : y < 2 ^ l) : (x * 2 ^ l + y) % 2 ^ l = y := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]

/-- nb pieces of 2^l entries, from block number n0 on; 0 elsewhere -/
def blk (l n0 nb : ℕ) (f : ℕ → ℕ → E) (X : ℕ) : E :=
  if n0 ≤ X / 2 ^ l ∧ X / 2 ^ l < n0 + nb then f (X / 2 ^ l - n0) (X % 2 ^ l) else 0

/-- The extension of a block of pieces. -/
theorem blk_ext (g l n0 nb : ℕ) (hfit : n0 + nb ≤ 2 ^ g) (f : ℕ → ℕ → E) (pt : ℕ → E) :
    Blocks.ext (g + l) (blk l n0 nb f) pt =
      ∑ b ∈ range nb, Blocks.eqN g 0 pt (n0 + b) * Blocks.ext l (f b) (AttSeg.sh pt g) := by
  rw [ext_split', ext_def]
  have inner : ∀ x, Blocks.ext l (fun y => blk l n0 nb f (x * 2 ^ l + y)) (AttSeg.sh pt g) =
      if n0 ≤ x ∧ x < n0 + nb then Blocks.ext l (f (x - n0)) (AttSeg.sh pt g) else 0 := by
    intro x
    by_cases hx : n0 ≤ x ∧ x < n0 + nb
    · rw [if_pos hx]
      refine Blocks.ext_congr (fun y hy => ?_) _
      unfold blk
      rw [div_pow l x hy, mod_pow l x hy, if_pos hx]
    · rw [if_neg hx]
      refine Blocks.ext_zero_of_forall (fun y hy => ?_) _
      unfold blk
      rw [div_pow l x hy, if_neg hx]
  simp only [inner]
  have hsub : Finset.Ico n0 (n0 + nb) ⊆ range (2 ^ g) := fun x hx => by
    have := (Finset.mem_Ico.1 hx).2
    exact Finset.mem_range.2 (by omega)
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.1 hb
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · intro x _ hn
    have : ¬ (n0 ≤ x ∧ x < n0 + nb) := fun h => hn (Finset.mem_Ico.2 h)
    rw [if_neg this, mul_zero]

/-- a two-family vector, piece by piece -/
theorem twoFam_eq (nb l l' : ℕ) (hl : l' ≤ l) (f f' : ℕ → ℕ → E) (pad : E) (X : ℕ) :
    AttSeg.twoFam nb l l' f f' pad X =
      blk l 0 nb f X + blk l' (nb * 2 ^ (l - l')) nb f' X +
        pad * (1 - blk l 0 nb (fun _ _ => 1) X - blk l' (nb * 2 ^ (l - l')) nb (fun _ _ => 1) X) :=
            by
  have hp : nb * 2 ^ l = nb * 2 ^ (l - l') * 2 ^ l' := by
    rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hl]
  have p1 : 0 < 2 ^ l := Nat.two_pow_pos l
  have p2 : 0 < 2 ^ l' := Nat.two_pow_pos l'
  unfold AttSeg.twoFam blk
  by_cases h1 : X < nb * 2 ^ l
  · have c1 : 0 ≤ X / 2 ^ l ∧ X / 2 ^ l < 0 + nb := ⟨Nat.zero_le _, by
      rw [Nat.zero_add]; exact (Nat.div_lt_iff_lt_mul p1).2 h1⟩
    have c2 : ¬ (nb * 2 ^ (l - l') ≤ X / 2 ^ l' ∧ X / 2 ^ l' < nb * 2 ^ (l - l') + nb) := fun h =>
        by
      have := (Nat.le_div_iff_mul_le p2).1 h.1
      omega
    rw [if_pos h1, if_pos c1, if_neg c2, if_pos c1, if_neg c2, Nat.sub_zero]
    ring
  · have c1 : ¬ (0 ≤ X / 2 ^ l ∧ X / 2 ^ l < 0 + nb) := fun h => by
      have := h.2
      rw [Nat.zero_add] at this
      exact h1 ((Nat.div_lt_iff_lt_mul p1).1 this)
    rw [if_neg h1, if_neg c1, if_neg c1]
    by_cases h2 : X - nb * 2 ^ l < nb * 2 ^ l'
    · have hX : nb * 2 ^ (l - l') * 2 ^ l' ≤ X := by omega
      have c2 : nb * 2 ^ (l - l') ≤ X / 2 ^ l' ∧ X / 2 ^ l' < nb * 2 ^ (l - l') + nb :=
        ⟨(Nat.le_div_iff_mul_le p2).2 hX, (Nat.div_lt_iff_lt_mul p2).2 (by rw [Nat.add_mul]; omega)⟩
      obtain ⟨r, hr⟩ : ∃ r, X = nb * 2 ^ (l - l') * 2 ^ l' + r :=
          ⟨X - nb * 2 ^ (l - l') * 2 ^ l', by omega⟩
      have sub : X - nb * 2 ^ (l - l') * 2 ^ l' = r := by omega
      have d : X / 2 ^ l' = nb * 2 ^ (l - l') + r / 2 ^ l' := by
        rw [hr, Nat.mul_comm (nb * 2 ^ (l - l')) (2 ^ l'), Nat.mul_add_div p2]
      have m : X % 2 ^ l' = r % 2 ^ l' := by
        rw [hr, Nat.mul_comm (nb * 2 ^ (l - l')) (2 ^ l'), Nat.mul_add_mod]
      rw [if_pos h2, if_pos c2, if_pos c2, hp, sub, d, m, Nat.add_sub_cancel_left]
      ring
    · have c2 : ¬ (nb * 2 ^ (l - l') ≤ X / 2 ^ l' ∧ X / 2 ^ l' < nb * 2 ^ (l - l') + nb) := fun h =>
        by
        have := (Nat.div_lt_iff_lt_mul p2).1 h.2
        rw [Nat.add_mul] at this
        omega
      rw [if_neg h2, if_neg c2, if_neg c2]
      ring

/-- The extension of a vector of two families of pieces and padding. -/
theorem twoFam_ext (a nb l l' : ℕ) (hl : l' ≤ l) (ha : l ≤ a)
    (hfit : nb * 2 ^ l + nb * 2 ^ l' ≤ 2 ^ a)
    (f f' : ℕ → ℕ → E) (pad : E) (pt : ℕ → E) :
    Blocks.ext a (AttSeg.twoFam nb l l' f f' pad) pt =
      ∑ b ∈ range nb, Blocks.eqN (a - l) 0 pt (0 + b) * Blocks.ext l (f b) (AttSeg.sh pt (a - l)) +
      ∑ b ∈ range nb, Blocks.eqN (a - l') 0 pt (nb * 2 ^ (l - l') + b) *
          Blocks.ext l' (f' b) (AttSeg.sh pt (a - l')) +
      pad * (1 - ∑ b ∈ range nb, Blocks.eqN (a - l) 0 pt (0 + b) -
        ∑ b ∈ range nb, Blocks.eqN (a - l') 0 pt (nb * 2 ^ (l - l') + b)) := by
  have e1 : a - l + l = a := Nat.sub_add_cancel ha
  have e2 : a - l' + l' = a := Nat.sub_add_cancel (le_trans hl ha)
  have f1 : 0 + nb ≤ 2 ^ (a - l) := by
    have h : nb * 2 ^ l ≤ 2 ^ (a - l) * 2 ^ l := by rw [← pow_add, e1]; omega
    rw [Nat.zero_add]
    exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos l)
  have f2 : nb * 2 ^ (l - l') + nb ≤ 2 ^ (a - l') := by
    have h : (nb * 2 ^ (l - l') + nb) * 2 ^ l' ≤ 2 ^ (a - l') * 2 ^ l' := by
      rw [← pow_add, e2, Nat.add_mul, Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hl]
      exact hfit
    exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos l')
  have B1 := fun f => blk_ext (a - l) l 0 nb f1 f pt
  have B2 := fun f => blk_ext (a - l') l' (nb * 2 ^ (l - l')) nb f2 f pt
  rw [e1] at B1
  rw [e2] at B2
  rw [show AttSeg.twoFam nb l l' f f' pad = fun X =>
      blk l 0 nb f X + blk l' (nb * 2 ^ (l - l')) nb f' X +
        pad * (1 - blk l 0 nb (fun _ _ => 1) X - blk l' (nb * 2 ^ (l - l')) nb (fun _ _ => 1) X)
    from funext fun X => twoFam_eq nb l l' hl f f' pad X]
  rw [Blocks.ext_add, Blocks.ext_add, Blocks.ext_smul, Blocks.ext_sub, Blocks.ext_sub,
      Blocks.ext_const, B1, B2, B1, B2]
  simp only [Blocks.ext_const, mul_one]

end Inst.Model.AttSeg.KeyFormsExt
