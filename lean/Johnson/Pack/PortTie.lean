-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Pack/PortTie.lean: the numbers of Johnson/Pack/PortZ.lean are those of the block SEND of the
verifier that is written after the programs.

Statements and proofs, on the imported functions `OnBytes.Send.cube` and `OnBytes.Send.pad`
(OnBytes/Iop/Send.lean). Johnson/Pack/PortZ.lean defines the cube's bits, the corners and the pad's
places of a shape by formulas of its own. This file ties them to the verifier's functions. The facts
on `Send.cube` and, for a pad of one place, on `Send.pad` are calls of OnBytes/Slice/BlkSend.lean.
Main names:
  `cube_bits`: `(Send.cube cs s).bits = bitsZ cs s`, for all codes and shapes.
  `cube_main`, `cube_mask`: where a table has a row: its row bits and index bits are `k1`, `B1` or
    `k2`, `B2`.
  `partZ`, `locZ`, `idxZ_loc`: an entry's table and its index inside the table; `idxZ` is that
    index, plus 2^(bits - 1) for the mask table exactly if both tables stand.
  `pad_mask`, `pad_main`: the value of `Send.pad` at one answer, with and without mask rows.
  `pad_mem`: at one answer, if `Send.pad cs s = some pl`: an entry is a place of the pad (`padP`) if
    and only if pl holds a place with its table and index.
Limits: one answer. Nothing here says that the pad's weights (`Cb.Gl.padW`) are the verifier's basis
elements (`OnBytes.thetaE`) read in the field, or that the row of `Sample.pad` is the row of
`Send.form`: the coefficients are not compared in this file.
-/
import Johnson.Pack.PortZ
import OnBytes.Slice.BlkSend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Pack
open OnBytes.Slice

section
variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape)

theorem cube_bits : (OnBytes.Send.cube cs s).bits = bitsZ cs s := by
  rw [cube_bits_eq, cube_mainBits_eq, cube_maskBits_eq, cube_mainRowBits_eq, cube_maskRowBits_eq,
    cube_hasMain_eq, cube_hasMask_eq]
  unfold bitsZ B1 B2 k1 k2 pMain pMask OnBytes.Code.logEll
  by_cases h1 : 0 < s.mainRows <;> by_cases h2 : 0 < s.maskRows <;> simp [h1, h2]

theorem cube_main (h : 0 < s.mainRows) :
    (OnBytes.Send.cube cs s).mainRowBits = k1 s ∧ (OnBytes.Send.cube cs s).mainBits = B1 cs s ∧
      (OnBytes.Send.cube cs s).hasMain = true := by
  rw [cube_mainBits_eq, cube_mainRowBits_eq, cube_hasMain_eq]
  unfold B1 k1 pMain OnBytes.Code.logEll
  simp [h]

theorem cube_mask (h : 0 < s.maskRows) :
    (OnBytes.Send.cube cs s).maskRowBits = k2 s ∧ (OnBytes.Send.cube cs s).maskBits = B2 cs s ∧
      (OnBytes.Send.cube cs s).hasMask = true := by
  rw [cube_maskBits_eq, cube_maskRowBits_eq, cube_hasMask_eq]
  unfold B2 k2 pMask OnBytes.Code.logEll
  simp [h]

/-- An entry's table. -/
def partZ : (portCode cs s).J → OnBytes.Part
  | .inl _ => .main
  | .inr _ => .mask

/-- Its index inside the table. -/
def locZ : (portCode cs s).J → ℕ
  | .inl x => x.1.val + 2 ^ k1 s * x.2.val
  | .inr x => x.1.val + 2 ^ k2 s * x.2.val

theorem idxZ_loc (j : (portCode cs s).J) :
    idxZ cs s j = locZ cs s j +
      (if partZ cs s j = .mask ∧ 0 < s.mainRows then 2 ^ (bitsZ cs s - 1) else 0) := by
  rcases j with x | x
  · show x.1.val + 2 ^ k1 s * x.2.val = x.1.val + 2 ^ k1 s * x.2.val + _
    rw [if_neg (fun h => by cases h.1)]
    rfl
  · have h2 : 0 < s.maskRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
    show x.1.val + 2 ^ k2 s * x.2.val +
      (if 0 < s.mainRows then 2 ^ max (B1 cs s) (B2 cs s) else 0) =
        x.1.val + 2 ^ k2 s * x.2.val + _
    by_cases h1 : 0 < s.mainRows
    · rw [if_pos h1, if_pos ⟨rfl, h1⟩]
      unfold bitsZ
      rw [if_pos ⟨h1, h2⟩]
      rfl
    · rw [if_neg h1, if_neg (fun h => h1 h.2)]

/-! ### The pad -/

theorem pad_mask (hm : 0 < s.maskRows) (h1 : s.answers = 1) :
    OnBytes.Send.pad cs s =
      if (pMask cs s).ell < 1 then none
      else some [⟨.mask, (s.maskRows - 1) + ((pMask cs s).ell - 1) * 2 ^ k2 s, 0,
        OnBytes.thetaE 0⟩] := by
  have hk := (cube_mask cs s hm).2.2
  rw [pad_cases cs s h1 (by rw [hk]; rfl)]
  unfold padLen padPart padIndex padLen
  rw [hk, (cube_mask cs s hm).1]
  rfl

theorem pad_main (hm : s.maskRows = 0) (h0 : 0 < s.mainRows) (h1 : s.answers = 1) :
    OnBytes.Send.pad cs s =
      if (pMain cs s).ell < eachZ s then none
      else some ((List.range (eachZ s)).map fun t =>
        ⟨.main, (s.mainRows - 1) + ((pMain cs s).ell - eachZ s + t) * 2 ^ k1 s, 0,
          OnBytes.thetaE t⟩) := by
  unfold OnBytes.Send.pad OnBytes.Send.cube k1 pMain eachZ
  by_cases h3 : s.mainDeg = 3 <;> simp [hm, h0, h1, h3]

/-- At one answer `padP` is the list of places of `Send.pad`. -/
theorem pad_mem (h1 : s.answers = 1) (pl : List OnBytes.PadPlace)
    (hp : OnBytes.Send.pad cs s = some pl) (j : (portCode cs s).J) :
    padP cs s j ↔ ∃ p ∈ pl, p.part = partZ cs s j ∧ p.index = locZ cs s j := by
  by_cases hm : 0 < s.maskRows
  · rw [pad_mask cs s hm h1] at hp
    by_cases hl : (pMask cs s).ell < 1
    · rw [if_pos hl] at hp
      cases hp
    · rw [if_neg hl] at hp
      cases hp
      rcases j with x | x
      · constructor
        · intro h
          have := h.1
          omega
        · rintro ⟨p, hp, h, _⟩
          rw [List.mem_singleton] at hp
          subst hp
          cases h
      · have hx : x.1.val < 2 ^ k2 s := lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 _)
        have hr : s.maskRows - 1 < 2 ^ k2 s :=
          lt_of_lt_of_le (by omega) (le_two_pow_ceilLog2 s.maskRows)
        constructor
        · intro h
          refine ⟨_, List.mem_singleton_self _, rfl, ?_⟩
          show (s.maskRows - 1) + ((pMask cs s).ell - 1) * 2 ^ k2 s = x.1.val + 2 ^ k2 s * x.2.val
          have a := h.1
          have b := h.2
          rw [show s.maskRows - 1 = x.1.val by omega, show (pMask cs s).ell - 1 = x.2.val by omega,
            Nat.mul_comm]
        · rintro ⟨p, hp, _, h⟩
          rw [List.mem_singleton] at hp
          subst hp
          have h' : (s.maskRows - 1) + 2 ^ k2 s * ((pMask cs s).ell - 1) =
              x.1.val + 2 ^ k2 s * x.2.val := by
            rw [Nat.mul_comm]
            exact h
          obtain ⟨a, b⟩ := idx_inj (k2 s) hr hx h'
          exact ⟨by omega, by omega⟩
  · have hz : s.maskRows = 0 := by omega
    rcases j with x | x
    · have h0 : 0 < s.mainRows := lt_of_le_of_lt (Nat.zero_le _) x.1.isLt
      rw [pad_main cs s hz h0 h1] at hp
      by_cases hl : (pMain cs s).ell < eachZ s
      · rw [if_pos hl] at hp
        cases hp
      · rw [if_neg hl] at hp
        cases hp
        have hx : x.1.val < 2 ^ k1 s := lt_of_lt_of_le x.1.isLt (le_two_pow_ceilLog2 _)
        have hr : s.mainRows - 1 < 2 ^ k1 s :=
          lt_of_lt_of_le (by omega) (le_two_pow_ceilLog2 s.mainRows)
        have hc : x.2.val < (pMain cs s).ell := x.2.isLt
        constructor
        · intro h
          have a := h.2.1
          have b := h.2.2
          refine ⟨_, List.mem_map.2 ⟨x.2.val + eachZ s - (pMain cs s).ell,
            List.mem_range.2 (by omega), rfl⟩, rfl, ?_⟩
          show (s.mainRows - 1) +
            ((pMain cs s).ell - eachZ s + (x.2.val + eachZ s - (pMain cs s).ell)) * 2 ^ k1 s =
              x.1.val + 2 ^ k1 s * x.2.val
          rw [show s.mainRows - 1 = x.1.val by omega,
            show (pMain cs s).ell - eachZ s + (x.2.val + eachZ s - (pMain cs s).ell) = x.2.val
              by omega,
            Nat.mul_comm]
        · rintro ⟨p, hp, _, h⟩
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hp
          have ht' := List.mem_range.1 ht
          have h' : (s.mainRows - 1) + 2 ^ k1 s * ((pMain cs s).ell - eachZ s + t) =
              x.1.val + 2 ^ k1 s * x.2.val := by
            rw [Nat.mul_comm]
            exact h
          obtain ⟨a, b⟩ := idx_inj (k1 s) hr hx h'
          exact ⟨hz, by omega, by omega⟩
    · exfalso
      have hx : x.1.val < s.maskRows := x.1.isLt
      omega

end
end Johnson.Pack

#print axioms Johnson.Pack.pad_mask
#print axioms Johnson.Pack.pad_main
#print axioms Johnson.Pack.pad_mem
#print axioms Johnson.Pack.cube_bits
#print axioms Johnson.Pack.cube_main
#print axioms Johnson.Pack.cube_mask
#print axioms Johnson.Pack.idxZ_loc
