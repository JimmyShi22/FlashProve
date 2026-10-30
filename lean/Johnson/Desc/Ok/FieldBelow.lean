-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/FieldBelow.lean: FOR EVERY ROUND THAT DRAWS FIELD ELEMENTS ALONE, none of them bound
to be other than 0, of a kind other than seeds and sealed, with at most 62 bits of work: a count of
the form degree times q^(m - 1), of the q^m points that the round draws, is at most 2^-128 of the
round's written verifier messages, whatever the degree up to 2^61 and whatever the number m of
elements up to 2^60. A theorem for all such rounds: no test is evaluated and no plan is read.

Why. Many forms of round are priced by a polynomial's degree over the field's size, which is above
2^191. So one coarse bound serves them all, and a kind that owes «my own count is at most 2^-128 of
the written round's verifier messages» owes there only: its count has this form, and its degree is
at most 2^61.

Main names:
  `below_of_share`: for ANY written round: a count c with c 2^130 at most the number of the round's
    typed values meets `RoundBelow` at 2^-128, if the round draws at most 2^60 elements, and has at
    most 62 bits of work where it draws one.
  `field_share`: degree q^(m - 1) 2^130 is at most q^m, for a degree of at most 2^61 and m at least
    1.
  `fieldBelow`: **the two together**, at a written round that draws m elements and nothing else.
  `unitBelow`: the same at a round that draws one element other than 0 and nothing else: a count of
    at most 2^60.

Limits: THAT A COUNT IS A BLOCK's, AND THAT IT HAS THIS FORM, IS NOT SAID HERE. What the round draws
is a hypothesis on the written round's entry. One round's share; no sum over rounds. Nothing on a
verifier or a file. It imports Johnson/Bridge/RowPriced.lean for `KindFits` and `below_of_num`, and
so stands above the files under ThirdParty/ by imports; it uses nothing on codes. FOR PROOFS ONLY:
no module that runs imports this file.

-/
import Johnson.Bridge.RowPriced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.Ok
open OnBytes OnBytes.Slice Cb _root_.Run Johnson.Bridge
open scoped ENNReal

/-- **A share of at most 2^-130 of the typed values**, in any written round. -/
theorem below_of_share (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (hnz : d.entry.drawNZ ≤ d.entry.drawE)
    (hw : d.entry.drawE ≠ 0 → d.entry.work + 66 ≤ 128) (hE : d.entry.drawE ≤ 2 ^ 60) (c V : ℕ)
    (hV : nVals (Fmt.dsOf d.entry d.kind) = V) (hV0 : 0 < V) (h : c * 2 ^ 130 ≤ V) :
    RoundBelow c d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  refine below_of_num d hlog hnz hw c V hV hV0 ?_
  have h1 : c * 2 ^ 193 ≤ V * 2 ^ 63 := by
    calc c * 2 ^ 193 = c * 2 ^ 130 * 2 ^ 63 := by ring
      _ ≤ V * 2 ^ 63 := Nat.mul_le_mul_right _ h
  have h2 : 3 * (d.entry.drawE + d.entry.drawNZ) ≤ 2 ^ 63 := by omega
  have h3 : 3 * (d.entry.drawE + d.entry.drawNZ) * V ≤ V * 2 ^ 63 := by
    rw [Nat.mul_comm V]
    exact Nat.mul_le_mul_right _ h2
  have h4 : V * 2 ^ 63 + V * 2 ^ 63 ≤ V * 2 ^ (d.entry.work + 65) := by
    have : (2 : ℕ) ^ 64 ≤ 2 ^ (d.entry.work + 65) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc V * 2 ^ 63 + V * 2 ^ 63 = V * 2 ^ 64 := by ring
      _ ≤ V * 2 ^ (d.entry.work + 65) := Nat.mul_le_mul_left _ this
  exact le_trans (Nat.add_le_add h1 h3) h4

/-- The field has more than 2^191 elements. -/
theorem q_large : 2 ^ 191 ≤ Cb.Gl.p ^ 3 := by decide +kernel

theorem field_share (deg m : ℕ) (hd : deg ≤ 2 ^ 61) (hm : 1 ≤ m) :
    deg * (Cb.Gl.p ^ 3) ^ (m - 1) * 2 ^ 130 ≤ (Cb.Gl.p ^ 3) ^ m := by
  have h1 : deg * 2 ^ 130 ≤ Cb.Gl.p ^ 3 :=
    le_trans (le_trans (Nat.mul_le_mul_right _ hd) (by norm_num)) q_large
  have hk : (Cb.Gl.p ^ 3) ^ m = (Cb.Gl.p ^ 3) ^ (m - 1) * (Cb.Gl.p ^ 3) := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [hk]
  calc deg * (Cb.Gl.p ^ 3) ^ (m - 1) * 2 ^ 130
      = (Cb.Gl.p ^ 3) ^ (m - 1) * (deg * 2 ^ 130) := by ring
    _ ≤ (Cb.Gl.p ^ 3) ^ (m - 1) * (Cb.Gl.p ^ 3) := Nat.mul_le_mul_left _ h1

/-- **A round that draws m field elements and nothing else**: degree times q^(m - 1). -/
theorem fieldBelow (d : PQ.RD) (deg m : ℕ) (hd : deg ≤ 2 ^ 61) (hm : 1 ≤ m) (hm' : m ≤ 2 ^ 60)
    (hlog : d.entry.logN ≤ 64) (hP : d.entry.poss = 0) (hE : d.entry.drawE = m)
    (hZ : d.entry.drawNZ = 0) (hT : d.entry.trits = 0) (hW : d.entry.work + 66 ≤ 128)
    (hk : KindFits false d.kind) :
    RoundBelow (deg * (Cb.Gl.p ^ 3) ^ (m - 1)) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hV : nVals (Fmt.dsOf d.entry d.kind) = (Cb.Gl.p ^ 3) ^ m := by
    rw [nVals_dsOf _ _ hk.1 hk.2, hP, hE, hZ, hT]
    simp
    rfl
  exact below_of_share d hlog (by rw [hZ]; exact Nat.zero_le _) (fun _ => hW)
    (by rw [hE]; exact hm') _ _ hV (Nat.pow_pos (lt_of_lt_of_le (by norm_num) q_large))
    (field_share deg m hd hm)

/-- **A round that draws one element other than 0 and nothing else.** -/
theorem unitBelow (d : PQ.RD) (c : ℕ) (hc : c ≤ 2 ^ 60) (hlog : d.entry.logN ≤ 64)
    (hP : d.entry.poss = 0) (hE : d.entry.drawE = 1) (hZ : d.entry.drawNZ = 1)
    (hT : d.entry.trits = 0) (hW : d.entry.work + 66 ≤ 128) (hk : KindFits false d.kind) :
    RoundBelow c d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hV : nVals (Fmt.dsOf d.entry d.kind) = Cb.Gl.p ^ 3 - 1 := by
    rw [nVals_dsOf _ _ hk.1 hk.2, hP, hE, hZ, hT]
    simp
    rfl
  have hq := q_large
  refine below_of_share d hlog (by rw [hZ, hE]) (fun _ => hW) (by rw [hE]; norm_num) _ _ hV
    (by omega) ?_
  have : c * 2 ^ 130 ≤ 2 ^ 190 := le_trans (Nat.mul_le_mul_right _ hc) (by norm_num)
  omega

end Johnson.Desc.Ok

#print axioms Johnson.Desc.Ok.below_of_share
#print axioms Johnson.Desc.Ok.fieldBelow
#print axioms Johnson.Desc.Ok.unitBelow
