-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port4.lean: the tie at the row and at what the row says: at a shape with one
answer the kind's sample row has, on each real entry, the coefficient of the row of the library's
oracle message of the shape (OMsg.row of Johnson/Pack/PortZ.lean's portOmZ), and it says of words
that hold a message of the library's code that the library's sample map has the answer.

Main names: ReadsOne (a drawn seed reads as a seed of the library's sample map); coef_port_main,
coef_port_mask; says_port.

What is not claimed. One answer a message. The premise that every code's length is a power of two is
used. Nothing on lists, on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood

variable {cs : Codes} {s : OracleShape}

/-- A drawn point and factor read as a seed of the library's sample map of the shape. -/
structure ReadsOne (cs : Codes) (s : OracleShape) (z : List E) (β : E)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) : Prop where
  long : bitsZ cs s ≤ z.length
  point : ∀ t : Fin (bitsZ cs s), readL z t.val = ρ.1 t
  factor : readE β = (ρ.2 : GE)

theorem ReadsOne.agree {z : List E} {β : E} {ρ : (Fin (bitsZ cs s) → GE) × GEˣ}
    (r : ReadsOne cs s z β ρ) : ∀ t, t < (Msg.of cs s).v → readL z t = pointOf ρ.1 t := by
  intro t ht
  rw [v_bitsZ] at ht
  unfold pointOf
  rw [dif_pos ht]
  exact r.point ⟨t, ht⟩

theorem Tie.some (h : Tie cs s) :
    ((Msg.of cs s).K != 0 || (Msg.of cs s).Kzk != 0) = true := by
  have := h.rows
  show (s.mainRows != 0 || s.maskRows != 0) = true
  by_cases hm : s.mainRows = 0
  · have : s.maskRows ≠ 0 := by omega
    simp [this]
  · simp [hm]

/-- **On a real entry of the main table the kind's sample row has the coefficient of the library's
row.** -/
theorem coef_port_main (h : Tie cs s) (e o : Nat) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (r : ReadsOne cs s z β ρ)
    (x : Fin s.mainRows × Fin (pMain cs s).ell) :
    coefAt (sampleRow (Msg.of cs s) o z β 0 y) o .main (x.1.val + 2 ^ k1 s * x.2.val) =
      (portOmZ cs s e).row () ρ (Sum.inl x) := by
  have h0 : 0 < s.mainRows := by have := x.1.isLt; omega
  obtain ⟨_, _, _, hc⟩ := meansLaw (Msg.of cs s) o z β 0 y h.some (by rw [v_bitsZ]; exact r.long)
  rw [hc .main _ (by rw [bits_main cs s h0]; exact main_lt cs s x),
    (Msg.of cs s).weight_congr _ _ r.agree, r.factor, weight_main h ρ x]
  rfl

/-- **The like of the mask table.** -/
theorem coef_port_mask (h : Tie cs s) (e o : Nat) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (r : ReadsOne cs s z β ρ)
    (x : Fin s.maskRows × Fin (pMask cs s).ell) :
    coefAt (sampleRow (Msg.of cs s) o z β 0 y) o .mask (x.1.val + 2 ^ k2 s * x.2.val) =
      (portOmZ cs s e).row () ρ (Sum.inr x) := by
  have h0 : 0 < s.maskRows := by have := x.1.isLt; omega
  obtain ⟨_, _, _, hc⟩ := meansLaw (Msg.of cs s) o z β 0 y h.some (by rw [v_bitsZ]; exact r.long)
  rw [hc .mask _ (by rw [bits_mask cs s h0]; exact mask_lt cs s x),
    (Msg.of cs s).weight_congr _ _ r.agree, r.factor, weight_mask h ρ x]
  rfl

/-- **What the kind's sample row says of words that hold a message of the library's code: the
library's sample map has the answer.** -/
theorem says_port (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (h : Tie S.codes x.shape) (z : List E) (β y : E)
    (ρ : (Fin (bitsZ S.codes x.shape) → GE) × GEˣ) (r : ReadsOne S.codes x.shape z β ρ)
    (w : Means.Words GE) (msg : (portCode S.codes x.shape).J → GE)
    (hw : w o = tabOf S.codes x.shape msg) :
    Means.Says rdE S (sampleRow (Msg.of S.codes x.shape) o z β 0 y) w ↔
      (portZ S.codes x.shape).val ρ msg () = readE y := by
  rw [says_iff S o x hx z β 0 y w h.some (by rw [v_bitsZ]; exact r.long), hw,
    (Msg.of S.codes x.shape).form_congr _ _ r.agree, r.factor, port_val h ρ msg]

end VerifiableInference.Desc.K1
