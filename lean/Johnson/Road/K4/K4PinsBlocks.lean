-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsBlocks.lean: THE BATCH's SUM FOR AN ELEMENT OF AN ARRAY IS ONE ENTRY OF THE
TABLE, OR NONE. `cellOfBlock` (Johnson/Desc/First/Batch/Law/AsRow.lean) is a sum over all entries J
of a table: "Meant: one entry, or none. Not proved here." Here it is proved, at a block that passes
the programs' own test `laidBlockOk`: the entry is the one at the row and place that `laidIn`
(Johnson/Desc/First/Look/K3CallerBase.lean) names. So `BlocksOne` (Johnson/Road/K4/K4PinsCellQ.lean)
holds of a list of such blocks no two of which hold one element. Arithmetic on numbers. No draw, no
count of a protocol.

  `dm`: quotient and rest of c + b d, where c < b.
  `idx_iff`: THE ARITHMETIC, in plain numbers: an index J of a table of a k rows and p k' places
    lies in the rectangle number (q, q') of a rows and p places, and has the number x within it, if
    and only if J is (a q + x / p) + (p q' + x % p) (a k).
  `elemNo`: the number of element (i, c) within a block (`laidIn`'s own text).
  `elem_of`, `elem_unique`: `iOf` and `cOf` (Johnson/Desc/First/Batch/Law/Laid.lean) of that number
    are i and c less the block's first ones; and they name the number.
  **`cellOfBlock_holds`**: at a block that holds (i, c): the sum is the one entry.
  `cellOfBlock_out`: at a block that does not hold (i, c): the sum is 0.
  **`blocksOne_of`**: `BlocksOne bs R P`, from: every block of bs passes `laidBlockOk` at R and P ·
    no two blocks of bs hold one element.

OBJECT: none of its own. USER: none yet; meant: whoever pays the field blocks of `CellOne`
(K4PinsCellQ.lean). LETTERS: the blocks, R, P, the table: free.

Limits. K04_law IS NOT PROVED BY THIS. THE TWO PREMISES OF `blocksOne_of` ARE TESTS ON THE LAYOUT
(the programs' `laidMatrixOk` asks both: OnBytes/Iop/ReqRows.lean: that a yes of it gives them in
this form is not typed here). R and P are the table's numbers of bits as the record's statement has
them: that these are the plan's is not said here. Over the one field of the first chain.

-/
import Johnson.Road.K4.K4PinsCellQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Params (LaidBlock)
open VerifiableInference.Desc.First.Look (laidHolds laidIn laidPlace)
open VerifiableInference.Desc.K9L (BlockFacts blockFacts xOf iOf cOf inBlock cellOfBlock xOf_lt
  iOf_lt cOf_lt)

/-! ## 1 The arithmetic -/

/-- Quotient and rest of c + b d, where c < b. -/
theorem dm {b c : ℕ} (d : ℕ) (hc : c < b) : (c + b * d) / b = d ∧ (c + b * d) % b = c :=
  (Nat.div_mod_unique (Nat.lt_of_le_of_lt (Nat.zero_le _) hc)).2 ⟨rfl, hc⟩

/-- **The arithmetic.** -/
theorem idx_iff (a k p k' q q' x J : ℕ) (hp : 0 < p) (hq : q < k) (hq' : q' < k')
    (hx : x < p * a) (hJ : J < a * k * (p * k')) :
    (J / a % k = q ∧ J / (a * k * p) % k' = q' ∧ p * (J % a) + J / (a * k) % p = x) ↔
      J = a * q + x / p + (p * q' + x % p) * (a * k) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hJ0 : J % (a * k) + a * k * (J / (a * k)) = J := Nat.mod_add_div J (a * k)
    have e1 : J % (a * k) / a = J / a % k := Nat.mod_mul_right_div_self J a k
    have e2 : J / (a * k * p) = J / (a * k) / p := (Nat.div_div_eq_div_mul J (a * k) p).symm
    have e3 : J % (a * k) % a = J % a := Nat.mod_mod_of_dvd J (Dvd.intro k rfl)
    have hπ : J / (a * k) < p * k' := Nat.div_lt_of_lt_mul hJ
    have hπ' : J / (a * k) / p < k' := Nat.div_lt_of_lt_mul hπ
    have e4 : J / (a * k) / p = q' := by
      rw [e2, Nat.mod_eq_of_lt hπ'] at h2
      exact h2
    have e5 : J % (a * k) / a = q := e1.trans h1
    have dρ : J % (a * k) % a + a * (J % (a * k) / a) = J % (a * k) := Nat.mod_add_div _ a
    have dπ : J / (a * k) % p + p * (J / (a * k) / p) = J / (a * k) := Nat.mod_add_div _ p
    rw [e3, e5] at dρ
    rw [e4] at dπ
    obtain ⟨x1, x2⟩ := dm (J % a) (Nat.mod_lt (J / (a * k)) hp)
    have hx' : x = J / (a * k) % p + p * (J % a) := by omega
    rw [hx', x1, x2, show a * q + J % a = J % (a * k) by omega,
      show p * q' + J / (a * k) % p = J / (a * k) by omega, Nat.mul_comm (J / (a * k))]
    exact hJ0.symm
  · intro h
    have hu : x / p < a := Nat.div_lt_of_lt_mul hx
    have hv : x % p < p := Nat.mod_lt _ hp
    have hr : a * q + x / p < a * k := by
      have h0 : a * (q + 1) ≤ a * k := Nat.mul_le_mul_left a hq
      rw [Nat.mul_succ] at h0
      omega
    have hJ' : J = a * q + x / p + a * k * (p * q' + x % p) := by
      rw [h, Nat.mul_comm (p * q' + x % p)]
    obtain ⟨j1, j2⟩ := dm (p * q' + x % p) hr
    rw [← hJ'] at j1 j2
    obtain ⟨r1, r2⟩ := dm q hu
    rw [Nat.add_comm (x / p)] at r1 r2
    obtain ⟨s1, s2⟩ := dm q' hv
    rw [Nat.add_comm (x % p)] at s1 s2
    refine ⟨?_, ?_, ?_⟩
    · rw [← Nat.mod_mul_right_div_self, j2, r1]
    · rw [← Nat.div_div_eq_div_mul, j1, s1, Nat.mod_eq_of_lt hq']
    · rw [← Nat.mod_mod_of_dvd J (Dvd.intro k rfl : a ∣ a * k), j2, r2, j1, s2]
      exact Nat.div_add_mod x p

/-! ## 2 An element's number within a block -/

/-- The number of element (i, c) within a block. -/
def elemNo (b : LaidBlock) (i c : ℕ) : ℕ :=
  if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
  else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)

theorem laidIn_eq (b : LaidBlock) (i c : ℕ) : laidIn b i c =
    (b.firstRow + elemNo b i c / 2 ^ b.placeBits, b.firstPlace + elemNo b i c % 2 ^ b.placeBits) :=
  rfl

theorem holds_parts {b : LaidBlock} {i c : ℕ} (h : laidHolds b i c = true) :
    b.firstI ≤ i ∧ i - b.firstI < 2 ^ b.bitsI ∧ b.firstC ≤ c ∧ c - b.firstC < 2 ^ b.bitsC := by
  simp only [laidHolds, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, by omega, h3, by omega⟩

/-- The number lies below the block's size, and names the element. -/
theorem elem_of {b : LaidBlock} {i c : ℕ} (hi : i - b.firstI < 2 ^ b.bitsI)
    (hc : c - b.firstC < 2 ^ b.bitsC) :
    elemNo b i c < 2 ^ (b.bitsI + b.bitsC) ∧ iOf b (elemNo b i c) = i - b.firstI ∧
      cOf b (elemNo b i c) = c - b.firstC := by
  unfold elemNo iOf cOf
  by_cases hl : b.iIsLow = true
  · rw [if_pos hl, if_pos hl, if_pos hl]
    obtain ⟨d1, d2⟩ := dm (c - b.firstC) hi
    rw [Nat.add_comm, Nat.mul_comm] at d1 d2
    refine ⟨?_, d2, d1⟩
    have h0 : (c - b.firstC + 1) * 2 ^ b.bitsI ≤ 2 ^ b.bitsC * 2 ^ b.bitsI :=
      Nat.mul_le_mul_right _ hc
    rw [Nat.succ_mul] at h0
    rw [Nat.pow_add, Nat.mul_comm (2 ^ b.bitsI)]
    omega
  · rw [if_neg hl, if_neg hl, if_neg hl]
    obtain ⟨d1, d2⟩ := dm (i - b.firstI) hc
    rw [Nat.add_comm, Nat.mul_comm] at d1 d2
    refine ⟨?_, d1, d2⟩
    have h0 : (i - b.firstI + 1) * 2 ^ b.bitsC ≤ 2 ^ b.bitsI * 2 ^ b.bitsC :=
      Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at h0
    rw [Nat.pow_add]
    omega

/-- `iOf` and `cOf` name the number. -/
theorem elem_unique {b : LaidBlock} {i c x : ℕ} (h1 : iOf b x = i - b.firstI)
    (h2 : cOf b x = c - b.firstC) : x = elemNo b i c := by
  unfold iOf at h1
  unfold cOf at h2
  unfold elemNo
  by_cases hl : b.iIsLow = true
  · rw [if_pos hl] at h1 h2 ⊢
    rw [← h1, ← h2, Nat.mul_comm]
    exact (Nat.div_add_mod x _).symm
  · rw [if_neg hl] at h1 h2 ⊢
    rw [← h1, ← h2, Nat.mul_comm]
    exact (Nat.div_add_mod x _).symm

/-! ## 3 One block -/

section
variable (b : LaidBlock) (R P : ℕ) (F : BlockFacts b R P) (tab : ℕ → Cb.Gl.E) (i c : ℕ)
include F

/-- At a block that does not hold (i, c) the sum is 0. -/
theorem cellOfBlock_out (h : laidHolds b i c = false) : cellOfBlock b R P tab i c = 0 := by
  unfold cellOfBlock
  refine Finset.sum_eq_zero fun J _ => ?_
  rw [if_neg, mul_zero]
  rintro ⟨h1, h2⟩
  have hx : xOf b R J < 2 ^ (b.bitsI + b.bitsC) := by
    rw [← F.hs, Nat.add_comm]
    exact xOf_lt b R J
  have hi := iOf_lt b _ hx
  have hc := cOf_lt b _ hx
  have : laidHolds b i c = true := by
    simp only [laidHolds, Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [h] at this
  exact Bool.false_ne_true this

/-- **At a block that holds (i, c) the sum is the one entry at the row and place that `laidIn`
names.** -/
theorem cellOfBlock_holds (h : laidHolds b i c = true) :
    cellOfBlock b R P tab i c = tab ((laidIn b i c).1 + (laidIn b i c).2 * 2 ^ R) := by
  obtain ⟨hI, hi, hC, hc⟩ := holds_parts h
  obtain ⟨hx, ei, ec⟩ := elem_of hi hc
  -- the table's and the block's sides
  have eR : 2 ^ R = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' F.hR]
  have eP : 2 ^ P = 2 ^ b.placeBits * 2 ^ (P - b.placeBits) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' F.hP]
  have hq : b.firstRow / 2 ^ b.rowBits < 2 ^ (R - b.rowBits) :=
    Nat.div_lt_of_lt_mul (eR ▸ F.rowLt)
  have hq' : b.firstPlace / 2 ^ b.placeBits < 2 ^ (P - b.placeBits) :=
    Nat.div_lt_of_lt_mul (eP ▸ F.placeLt)
  have fr : 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits) = b.firstRow := by
    have := Nat.mod_add_div b.firstRow (2 ^ b.rowBits)
    rw [F.alRow, Nat.zero_add] at this
    exact this
  have fp : 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits) = b.firstPlace := by
    have := Nat.mod_add_div b.firstPlace (2 ^ b.placeBits)
    rw [F.alPlace, Nat.zero_add] at this
    exact this
  have hx' : elemNo b i c < 2 ^ b.placeBits * 2 ^ b.rowBits := by
    rw [← Nat.pow_add, Nat.add_comm, F.hs]
    exact hx
  have key : ∀ J, J < 2 ^ (R + P) →
      ((J / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) =
          b.firstRow / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) ∧
        J / 2 ^ (R + b.placeBits) % 2 ^ (P - b.placeBits) =
          b.firstPlace / 2 ^ b.placeBits % 2 ^ (P - b.placeBits) ∧
        xOf b R J = elemNo b i c) ↔
      J = (laidIn b i c).1 + (laidIn b i c).2 * 2 ^ R) := by
    intro J hJ
    have I := idx_iff (2 ^ b.rowBits) (2 ^ (R - b.rowBits)) (2 ^ b.placeBits)
      (2 ^ (P - b.placeBits)) (b.firstRow / 2 ^ b.rowBits) (b.firstPlace / 2 ^ b.placeBits)
      (elemNo b i c) J (Nat.two_pow_pos _) hq hq' hx' (by rw [← eR, ← eP, ← Nat.pow_add]; exact hJ)
    rw [← eR, fr, fp, ← Nat.pow_add] at I
    rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq', laidIn_eq]
    exact I
  have hst : (laidIn b i c).1 + (laidIn b i c).2 * 2 ^ R < 2 ^ (R + P) := by
    rw [laidIn_eq]
    show b.firstRow + elemNo b i c / 2 ^ b.placeBits +
      (b.firstPlace + elemNo b i c % 2 ^ b.placeBits) * 2 ^ R < 2 ^ (R + P)
    have hu : elemNo b i c / 2 ^ b.placeBits < 2 ^ b.rowBits := Nat.div_lt_of_lt_mul hx'
    have hv : elemNo b i c % 2 ^ b.placeBits < 2 ^ b.placeBits :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have r0 : 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits + 1) ≤ 2 ^ R := by
      rw [eR]
      exact Nat.mul_le_mul_left _ hq
    have p0 : 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits + 1) ≤ 2 ^ P := by
      rw [eP]
      exact Nat.mul_le_mul_left _ hq'
    rw [Nat.mul_succ, fr] at r0
    rw [Nat.mul_succ, fp] at p0
    have m0 : (b.firstPlace + elemNo b i c % 2 ^ b.placeBits + 1) * 2 ^ R ≤ 2 ^ P * 2 ^ R :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at m0
    rw [Nat.pow_add, Nat.mul_comm (2 ^ R)]
    omega
  unfold cellOfBlock
  rw [Finset.sum_eq_single_of_mem _ (Finset.mem_range.2 hst)]
  · obtain ⟨t1, t2, t3⟩ := (key _ hst).2 rfl
    unfold inBlock
    rw [if_pos t1, if_pos t2, t3, ei, ec, if_pos ⟨by omega, by omega⟩, one_mul, one_mul]
  · intro J hJ hne
    unfold inBlock
    by_cases t1 : J / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) =
        b.firstRow / 2 ^ b.rowBits % 2 ^ (R - b.rowBits)
    · by_cases t2 : J / 2 ^ (R + b.placeBits) % 2 ^ (P - b.placeBits) =
          b.firstPlace / 2 ^ b.placeBits % 2 ^ (P - b.placeBits)
      · rw [if_pos t1, if_pos t2, one_mul, one_mul, if_neg]
        rintro ⟨c1, c2⟩
        exact hne ((key J (Finset.mem_range.1 hJ)).1
          ⟨t1, t2, elem_unique (by omega) (by omega)⟩)
      · rw [if_neg t2, mul_zero, zero_mul]
    · rw [if_neg t1, zero_mul, zero_mul]

end

/-! ## 4 A list of blocks -/

/-- **`BlocksOne`**, from: every block passes `laidBlockOk` at R and P · no two blocks hold one
element. -/
theorem blocksOne_of (R P : ℕ) : ∀ bs : List LaidBlock,
    (∀ b ∈ bs, OnBytes.laidBlockOk b R P = true) →
    bs.Pairwise (fun x y => ∀ i c, laidHolds x i c = true → laidHolds y i c = false) →
    BlocksOne bs R P
  | [], _, _ => fun _ _ _ _ h => nomatch h
  | b :: l, hok, hd => by
    intro tab i c rp h
    have Fb := blockFacts b R P (hok b List.mem_cons_self)
    obtain ⟨hb, hl⟩ := List.pairwise_cons.1 hd
    rw [List.map_cons, List.sum_cons]
    unfold laidPlace at h
    by_cases hh : laidHolds b i c = true
    · rw [List.find?_cons_of_pos (p := fun y => laidHolds y i c) (a := b) (l := l) hh] at h
      have e : rp = laidIn b i c := (Option.some.inj h).symm
      have z : (l.map fun y => cellOfBlock y R P tab i c).sum = 0 := by
        refine List.sum_eq_zero fun v hv => ?_
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
        exact cellOfBlock_out y R P (blockFacts y R P (hok y (List.mem_cons_of_mem _ hy))) tab i c
          (hb y hy i c hh)
      rw [z, add_zero, e]
      exact cellOfBlock_holds b R P Fb tab i c hh
    · rw [List.find?_cons_of_neg (p := fun y => laidHolds y i c) (a := b) (l := l) hh] at h
      rw [cellOfBlock_out b R P Fb tab i c (by simpa using hh), zero_add]
      exact blocksOne_of R P l (fun y hy => hok y (List.mem_cons_of_mem _ hy)) hl tab i c rp h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.idx_iff
#print axioms OnBytes.Road.K4.elem_of
#print axioms OnBytes.Road.K4.elem_unique
#print axioms OnBytes.Road.K4.cellOfBlock_out
#print axioms OnBytes.Road.K4.cellOfBlock_holds
#print axioms OnBytes.Road.K4.blocksOne_of
