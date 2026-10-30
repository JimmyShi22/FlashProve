-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Rows/LayerNormsPort.lean: three claims of the verifier on the norms of a layers'
sub-proof are worth what the library-side claims are worth, in every world and at all entries that
plain premises tie to each other.

Johnson/Road/FormsKeysClaims.lean writes the claims behind the product layer of the squares as a
list of forms, normsL: the layer's own claim; "the two end values are one"; the end value against
the reads of the stream's limbs. Johnson/Road/FormsKeysIdnW.lean has the form of the claim that the
token sumcheck of the row products starts from the batch, rowBatchForm. Cb/Pv/Lay/End/NormsCl.lean
lists them in the library's names: cSame, cEnd, cBatch (parts "sq" and "bat" of the ledger LayCl).
This file holds them against each other on values, after the pattern of
Johnson/Road/Rows/LayerTermsPort.lean.

Main names:
  `same_val`, `sqEnd_val`, `batch_val`: one value each, under plain premises: numerals; five limbs;
    the sizes; the hidden values under the slots; the verifier's weights and powers read as the
    library's; the reads' entries that the verifier's form names are worth the library-side
    entries of the same names.
Limits. These premises are premises. The layer's OWN claim (H.wpl.row; the library's u1) is not
spoken of here. Nothing on whether the reads are true, on soundness or on hiding.


-/
import Johnson.Road.Rows.LayerGatedPort
import Johnson.Road.FormsKeysIdnW
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff tenCell)
open OnBytes.Model.Layer (Env Lay Ten Heard)
open Cb.Pv.Lay.End (NormsNames NormsE cSame cBatch hL hR hCl hP)
open Blocks (Form eqN)

variable {K : Type} [Field K] {J : Type} [Fintype J] [DecidableEq J]
variable {ρ : Reading K} {W : World K} {N : NormsNames J} {e : NormsE K} {y : J → K}

/-- "The two end values of the product layer are one." -/
theorem same_val {sL sR : ℕ} (hl : W.slot sL = e.shL - e.β1 * y N.mL)
    (hr : W.slot sR = e.shR - e.β1 * y N.mR) :
    (Aff.slot sL - Aff.slot sR).value ρ W = Form.val y (cSame N e) := by
  unfold cSame Cb.Pv.Lay.End.hL Cb.Pv.Lay.End.hR
  rw [Aff.value_sub, Aff.value_slot, Aff.value_slot, hl, hr]
  simp only [map_sub, map_smul, Form.val_const, Form.val_ent, smul_eq_mul]

/-- "The hidden sum of the token sumcheck is the batch of the hidden products." n: the norms. -/
theorem batch_val (hρ : Numerals ρ) (yl : Lay) (H : Heard) {n : ℕ}
    (hn : Model.ledNP yl.h.xl * yl.NI = 7 * n)
    (hcl : W.slot H.tV.sCl = e.shCl - y N.mCl)
    (hp : ∀ x, x < 7 * n → W.slot (H.sPv + x) = e.shP x - y (N.mP x))
    (hom : ∀ x, x < 7 * n → ρ.val (H.omV.getD x zeroE) = e.ω ^ x) :
    (rowBatchForm yl H).value ρ W = Form.val y (cBatch N e n) := by
  unfold cBatch Cb.Pv.Lay.End.hCl Cb.Pv.Lay.End.hP
  rw [rowBatch_value ρ W hρ, hn, hcl, map_sub, Form.val_masked, map_sum]
  congr 1
  refine sum_congr rfl fun x hx => ?_
  have hx' := mem_range.mp hx
  rw [hom x hx', hp x hx', map_smul, Form.val_masked, smul_eq_mul]

/-- The end value of the product layer of the squares against the reads of the stream's limbs. -/
theorem sqEnd_val (hρ : Numerals ρ) {yl : Lay} {v : Env} {tI tA sL : ℕ} {txs : Ten}
    {eT gp : Array E} {lNI b B n : ℕ}
    (hnl : yl.xb.nl = 5) (hB : yl.h.d / yl.S2 = B) (hn : yl.NI = n)
    (hl : W.slot sL = e.shL - e.β1 * y N.mL)
    (hw : ∀ i kh, i < n → kh < B →
      ρ.val (eT.getD (i * yl.Pd / yl.S2 + kh) zeroE) = eqN (lNI + b) 0 e.r1 (i * 2 ^ b + kh))
    (hg : ∀ l, l < 5 → ρ.val (gp.getD l zeroE) = e.γ ^ l)
    (hI : ∀ l kh, l < 5 → kh < B →
      readAtW W v tI (tenCell yl.xb l 0 0 / yl.S2 + kh) = y (N.uXi 0 l kh))
    (hA : ∀ i l kh, 0 < i → i < n → l < 5 → kh < B →
      readAtW W v tA (tenCell txs.place l (i - 1) 0 / yl.S2 + kh) = y (N.uXi i l kh))
    {s : Aff} (h : normsSum yl v tI tA txs eT gp = some s) :
    (Aff.slot sL + s).value ρ W = Form.val y (Cb.Pv.Lay.End.cEnd N e lNI b B n) := by
  have hB0 : ∀ x, x < n * B * 5 → x / 5 % B < B ∧ x / 5 / B < n ∧ x % 5 < 5 := by
    intro x hx
    have h5 : x / 5 < n * B := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    have hBp : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · rw [h0, Nat.mul_zero] at h5
        exact absurd h5 (Nat.not_lt_zero _)
      · exact h0
    exact ⟨Nat.mod_lt _ hBp, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h5),
      Nat.mod_lt _ (by omega)⟩
  have hv : s.value ρ W = ∑ x ∈ range (n * B * 5),
      -((eqN (lNI + b) 0 e.r1 (x / 5 / B * 2 ^ b + x / 5 % B) * e.γ ^ (x % 5)) *
        y (N.uXi (x / 5 / B) (x % 5) (x / 5 % B))) := by
    unfold normsSum at h
    rw [hnl, hB, hn] at h
    refine sumForms_value_lt _ _ _ (fun x hx c k hc => ?_) h
    obtain ⟨k1, k2, k3⟩ := hB0 x hx
    obtain ⟨a, ha, ec⟩ := map_some hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ec
    rw [hρ.neg, ρ.mul, hw _ _ k2 k1, hg _ k3]
    by_cases h0 : (x / 5 / B == 0) = true
    · rw [if_pos h0] at ha
      have e0 : x / 5 / B = 0 := by simpa using h0
      rw [U3at_read ha, hI _ _ k3 k1, e0]
      ring
    · rw [if_neg h0] at ha
      have e0 : 0 < x / 5 / B := Nat.pos_of_ne_zero (by simpa using h0)
      rw [U3at_read ha, hA _ _ _ e0 k2 k3 k1]
      ring
  unfold Cb.Pv.Lay.End.cEnd Cb.Pv.Lay.End.hL
  rw [Aff.value_add, Aff.value_slot, hl, hv, map_sub, map_sub, Form.val_const, map_smul,
    Form.val_ent, smul_eq_mul, map_sum, sum_neg_distrib]
  simp only [map_smul, Form.val_ent, smul_eq_mul]
  ring

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.same_val
#print axioms OnBytes.Road.Rows.batch_val
#print axioms OnBytes.Road.Rows.sqEnd_val
