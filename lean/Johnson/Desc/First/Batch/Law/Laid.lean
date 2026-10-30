-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Laid.lean
(kind K9's soundness lemma, (T2b)): THEOREMS: what the layout's functions
(OnBytes/Iop/ReqRows.lean: laidTensor, laidForm, ReqRows.addTerms) put on each entry of a table. The
library had no law on their values.
An array is cut into aligned blocks; a block's element number x (its row index i and column index c
interleaved as the block says) lies in row firstRow + x / 2^placeBits of the table, at place
firstPlace + x % 2^placeBits; the table's entry (row, place) has the index row + 2^R * place.
  laidTensor_entry  **the entry J of laidTensor b R P onI onC scalar reads as 0 outside the block,
                    and inside as scalar * onI[i] * onC[c] at the element (i, c) that the layout
                    puts at J.** For onI a product form and onC written out: as K9's terms are.
  laidForm_entry    the sum over an array's blocks.
  addTerms_coef     the row that ReqRows.addTerms makes: on each entry of each main table the sum of
                    what the terms put there; nothing on a mask table.
The measures: xOf b R J (the element's number at the index J) · iOf, cOf (its row and column within
the block) · inBlock (1 or 0: the index's high row bits and high place bits are the block's) ·
laidVal · termAt · weightAt (Law/Measure.lean).
Beneath: pushBits_spec (which pairs and dense variables the bits of x leave) · laidTensor_parts (the
inversion) · prodX, prodI (the pairs' product is the product form at i's low bits) · weight_split,
above_val (the high bits are those of the block's first row) · denseIndex_cOf (the index within the
written-out vector is c). CARRIED from OnBytes/Iop/TensorLaws.lean: Tensor.entry_val, entry_scale,
pairsVal_append, pairsVal_choice, Form.entry_add; from RowLaws.lean: Row.coefficient_val.
Every equation is between readings in a commutative ring. Nothing where a function returns nothing.
Nothing on soundness by itself.

-/
import OnBytes.Iop.RowLaws
import Johnson.Desc.First.Batch.Law.Equation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray)

variable {K : Type} [CommRing K] (ρ : Reading K)

theorem some_bind {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : (x >>= f) = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => exact absurd h (by simp)
  | some a => exact ⟨a, rfl, h⟩

/-! ## The bits of an element's number within a block -/

/-- How many low bits of an element's number belong to the index that is low. -/
def lowBits (b : LaidBlock) : Nat := if b.iIsLow then b.bitsI else b.bitsC

/-- Bit xb of an element's number is a bit of the array's row index i. -/
def ofI (b : LaidBlock) (xb : Nat) : Bool := decide (xb < lowBits b) == b.iIsLow

/-- Which bit of its index bit xb of an element's number is. -/
def bitOf (b : LaidBlock) (xb : Nat) : Nat := if xb < lowBits b then xb else xb - lowBits b

/-- The pair of the variable that carries bit xb: the product form's factors, or (1, 1). -/
def pairOf (b : LaidBlock) (onI : IndexWeights) (xb : Nat) : E × E :=
  if ofI b xb then (onI.lo.getD (bitOf b xb) zeroE, onI.hi.getD (bitOf b xb) zeroE)
  else (oneE, oneE)

/-- The dense variables that a list of bits leaves: (bit of the column index, variable). -/
def denseFrom (b : LaidBlock) : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | pos, xb :: xs => (if ofI b xb then [] else [(bitOf b xb, pos)]) ++ denseFrom b (pos + 1) xs

theorem pushBit_spec (b : LaidBlock) (onI onC : IndexWeights) (hI : onI.values = none)
    (L : Array E) (hC : onC.values = some L) (d e : LaidDraft) (xb : Nat)
    (h : d.pushBit b onI onC xb = some e) :
    e.t = { d.t with pairs := d.t.pairs ++ [pairOf b onI xb] } ∧
      e.dense = d.dense ++ (if ofI b xb then [] else [(bitOf b xb, d.t.pairs.length)]) ∧
      (ofI b xb = true → bitOf b xb < onI.lo.size) := by
  have h' : (if (if ofI b xb = true then onI else onC).writtenOut = true then
        some ({ t := d.t.push oneE oneE, dense := d.dense ++ [(bitOf b xb, d.t.vars)] } :
          LaidDraft)
      else
        match (if ofI b xb = true then onI else onC).lo[bitOf b xb]?,
          (if ofI b xb = true then onI else onC).hi[bitOf b xb]? with
        | some l, some h => some { d with t := d.t.push l h }
        | _, _ => none) = some e := h
  by_cases ho : ofI b xb = true
  · simp only [ho, if_true, IndexWeights.writtenOut, hI, Option.isSome_none, Bool.false_eq_true,
      if_false] at h'
    split at h'
    · rename_i l hh h1 h2
      have e1 := Option.some.inj h'
      obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.mp h1
      refine ⟨?_, ?_, fun _ => hlt⟩
      · rw [← e1]
        simp only [Tensor.push, pairOf, ho, if_true, Array.getD_eq_getD_getElem?, h1, h2,
          Option.getD_some]
      · rw [← e1]
        simp [ho]
    · simp at h'
  · simp only [ho, Bool.false_eq_true, if_false, IndexWeights.writtenOut, hC, Option.isSome_some,
      if_true] at h'
    have e1 := Option.some.inj h'
    refine ⟨?_, ?_, fun hx => absurd hx ho⟩
    · rw [← e1]
      simp only [Tensor.push, pairOf, ho, Bool.false_eq_true, if_false]
    · rw [← e1]
      simp [ho, Tensor.vars]

theorem pushBits_spec (b : LaidBlock) (onI onC : IndexWeights) (hI : onI.values = none)
    (L : Array E) (hC : onC.values = some L) : ∀ (xs : List Nat) (d e : LaidDraft),
    d.pushBits b onI onC xs = some e →
    e.t = { d.t with pairs := d.t.pairs ++ xs.map (pairOf b onI) } ∧
      e.dense = d.dense ++ denseFrom b d.t.pairs.length xs ∧
      ∀ xb ∈ xs, ofI b xb = true → bitOf b xb < onI.lo.size
  | [], d, e, h => by
    have e1 : d = e := Option.some.inj h
    subst e1
    simp [denseFrom]
  | xb :: xs, d, e, h => by
    have h' : (d.pushBit b onI onC xb).bind (fun e' => e'.pushBits b onI onC xs) = some e := h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨a1, a2, a3⟩ := pushBit_spec b onI onC hI L hC d d1 xb h1
    obtain ⟨b1, b2, b3⟩ := pushBits_spec b onI onC hI L hC xs d1 e h2
    refine ⟨?_, ?_, ?_⟩
    · rw [b1, a1]
      simp
    · rw [b2, a2, a1]
      simp [denseFrom]
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact a3
      · exact b3 y hy'

/-! ## What laidTensor returns -/

/-- The dense variables in the order of the column index's bits, as laidTensor lists them. -/
def varsOf (dense : List (Nat × Nat)) : List Nat :=
  (List.range dense.length).map fun i => ((dense.find? fun x => x.1 == i).map (·.2)).getD 0

theorem laidTensor_parts (b : LaidBlock) (R P : Nat) (onI onC : IndexWeights)
    (hI : onI.values = none) (L : Array E) (hC : onC.values = some L) (scalar : E) (t : Tensor)
    (h : laidTensor b R P onI onC scalar = some t) :
    laidBlockOk b R P = true ∧ ∃ aI d1 d3,
      onI.above b.firstI b.bitsI = some aI ∧
      LaidDraft.pushBits { t := { scalar := scalar } } b onI onC
        ((List.range b.rowBits).map (· + b.placeBits)) = some d1 ∧
      LaidDraft.pushBits { d1 with
        t := d1.t.insertChoice d1.t.vars (R - b.rowBits) (b.firstRow / 2 ^ b.rowBits) } b onI onC
        (List.range b.placeBits) = some d3 ∧
      ((d3.dense.isEmpty = true ∧ ∃ v, L[b.firstC]? = some v ∧
          t = (((d3.t.insertChoice d3.t.vars (P - b.placeBits)
            (b.firstPlace / 2 ^ b.placeBits)).scale aI).scale oneE).scale v) ∨
        (d3.dense.isEmpty = false ∧
          t = ({ ((d3.t.insertChoice d3.t.vars (P - b.placeBits)
            (b.firstPlace / 2 ^ b.placeBits)).scale aI).scale oneE with
              denseVars := varsOf d3.dense }).setValues L b.firstC)) := by
  unfold laidTensor at h
  dsimp only at h
  split at h
  · simp at h
  rename_i hg
  obtain ⟨_, _, h⟩ := some_bind h
  obtain ⟨d1, h1, h⟩ := some_bind h
  obtain ⟨d3, h3, h⟩ := some_bind h
  obtain ⟨aI, ha, h⟩ := some_bind h
  obtain ⟨aC, hc, h⟩ := some_bind h
  have hok : laidBlockOk b R P = true := by
    by_contra hn
    exact hg (by simp [hn])
  have hac : aC = oneE := by
    simp [IndexWeights.above, IndexWeights.writtenOut, hC] at hc
    exact hc.symm
  subst hac
  simp only [IndexWeights.writtenOut, hI, hC, Option.isSome_none, Bool.false_eq_true,
    if_false] at h
  refine ⟨hok, aI, d1, d3, ha, h1, h3, ?_⟩
  by_cases hd : d3.dense.isEmpty = true
  · left
    simp only [hd, if_true] at h
    obtain ⟨t6, h6, h⟩ := some_bind h
    have ht : t6 = t := by
      split at h
      · exact Option.some.inj h
      · simp at h
    subst ht
    obtain ⟨v, hv, e⟩ := Option.map_eq_some_iff.mp h6
    exact ⟨hd, v, hv, e.symm⟩
  · right
    have hd' : d3.dense.isEmpty = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, if_false] at h
    obtain ⟨t6, h6, h⟩ := some_bind h
    have ht : t6 = t := by
      split at h
      · exact Option.some.inj h
      · simp at h
    subst ht
    exact ⟨hd', (Option.some.inj h6).symm⟩

/-! ## Bits and products -/

theorem bit_eq (j k : Nat) : (j / 2 ^ k % 2 == 1) = j.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq, beq_eq_decide]

/-- The product of the pairs' halves, as a product over the bits of the index. -/
theorem pairsVal_prod : ∀ (l : List (E × E)) (j : Nat),
    pairsVal ρ l j = ∏ k ∈ Finset.range l.length,
      ρ.val (if j.testBit k then (l.getD k default).2 else (l.getD k default).1)
  | [], j => by simp [pairsVal]
  | p :: l, j => by
    rw [pairsVal, pairsVal_prod l (j / 2), List.length_cons, Finset.prod_range_succ', mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      rw [List.getD_cons_succ, Nat.testBit_succ]
    · have h0 : (j % 2 == 1) = j.testBit 0 := by
        have := bit_eq j 0
        simpa using this
      rw [h0, List.getD_cons_zero]

theorem pairsVal_range (f : Nat → E × E) (n s j : Nat) :
    pairsVal ρ (((List.range n).map (· + s)).map f) j = ∏ k ∈ Finset.range n,
      ρ.val (if j.testBit k then (f (k + s)).2 else (f (k + s)).1) := by
  rw [pairsVal_prod]
  simp only [List.length_map, List.length_range]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  simp [List.getD_eq_getElem?_getD, hk']

theorem pairsVal_range0 (f : Nat → E × E) (n j : Nat) :
    pairsVal ρ ((List.range n).map f) j = ∏ k ∈ Finset.range n,
      ρ.val (if j.testBit k then (f k).2 else (f k).1) := by
  rw [pairsVal_prod]
  simp only [List.length_map, List.length_range]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  simp [List.getD_eq_getElem?_getD, hk']

/-- The half of the pair of bit xb that the bit's value picks. -/
def hv (b : LaidBlock) (onI : IndexWeights) (xb : Nat) (β : Bool) : K :=
  ρ.val (if β then (pairOf b onI xb).2 else (pairOf b onI xb).1)

/-- The factor of a product form for bit t. -/
def fI (onI : IndexWeights) (t : Nat) (β : Bool) : K :=
  if β then ρ.val (onI.hi.getD t zeroE) else ρ.val (onI.lo.getD t zeroE)

theorem hv_I (b : LaidBlock) (onI : IndexWeights) (xb : Nat) (β : Bool) (h : ofI b xb = true) :
    hv ρ b onI xb β = fI ρ onI (bitOf b xb) β := by
  cases β <;> simp [hv, fI, pairOf, h]

theorem hv_C (b : LaidBlock) (onI : IndexWeights) (xb : Nat) (β : Bool) (h : ofI b xb = false) :
    hv ρ b onI xb β = 1 := by
  cases β <;> simp [hv, pairOf, h, ρ.one]

/-- The number within the block of the element at the table's index J, if J is in the block. -/
def xOf (b : LaidBlock) (R J : Nat) : Nat :=
  2 ^ b.placeBits * (J % 2 ^ b.rowBits) + J / 2 ^ R % 2 ^ b.placeBits

theorem x_low (b : LaidBlock) (R J k : Nat) (hk : k < b.placeBits) :
    (xOf b R J).testBit k = (J / 2 ^ R).testBit k := by
  unfold xOf
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)), if_pos hk,
    Nat.testBit_mod_two_pow]
  simp [hk]

theorem x_high (b : LaidBlock) (R J k : Nat) (hk : k < b.rowBits) :
    (xOf b R J).testBit (b.placeBits + k) = J.testBit k := by
  unfold xOf
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
    if_neg (by omega), Nat.add_sub_cancel_left, Nat.testBit_mod_two_pow]
  simp [hk]

/-- The two stretches of variables that carry the element's number. -/
theorem prodX (b : LaidBlock) (onI : IndexWeights) (R J : Nat) :
    pairsVal ρ (((List.range b.rowBits).map (· + b.placeBits)).map (pairOf b onI)) J *
      pairsVal ρ ((List.range b.placeBits).map (pairOf b onI)) (J / 2 ^ R) =
    ∏ xb ∈ Finset.range (b.placeBits + b.rowBits), hv ρ b onI xb ((xOf b R J).testBit xb) := by
  rw [pairsVal_range, pairsVal_range0, Finset.prod_range_add, mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro k hk
    rw [x_low b R J k (Finset.mem_range.mp hk)]
    rfl
  · apply Finset.prod_congr rfl
    intro k hk
    rw [x_high b R J k (Finset.mem_range.mp hk), Nat.add_comm k]
    rfl

/-- The array's row and column, within the block, of element number x. -/
def iOf (b : LaidBlock) (x : Nat) : Nat := if b.iIsLow then x % 2 ^ b.bitsI else x / 2 ^ b.bitsC
def cOf (b : LaidBlock) (x : Nat) : Nat := if b.iIsLow then x / 2 ^ b.bitsI else x % 2 ^ b.bitsC

/-- Of these variables those of the row index give the product form's factors. -/
theorem prodI (b : LaidBlock) (onI : IndexWeights) (x : Nat) :
    ∏ xb ∈ Finset.range (b.bitsI + b.bitsC), hv ρ b onI xb (x.testBit xb) =
      ∏ t ∈ Finset.range b.bitsI, fI ρ onI t ((iOf b x).testBit t) := by
  by_cases hl : b.iIsLow = true
  · rw [Finset.prod_range_add]
    have h2 : ∏ k ∈ Finset.range b.bitsC, hv ρ b onI (b.bitsI + k) (x.testBit (b.bitsI + k)) = 1 :=
      Finset.prod_eq_one fun k _ => hv_C ρ b onI _ _ (by simp [ofI, lowBits, hl])
    rw [h2, mul_one]
    apply Finset.prod_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [hv_I ρ b onI t _ (by simp [ofI, lowBits, hl, ht'])]
    simp [bitOf, lowBits, iOf, hl, ht', Nat.testBit_mod_two_pow]
  · have hl' : b.iIsLow = false := by simpa using hl
    rw [Nat.add_comm, Finset.prod_range_add]
    have h1 : ∏ k ∈ Finset.range b.bitsC, hv ρ b onI k (x.testBit k) = 1 :=
      Finset.prod_eq_one fun k hk => hv_C ρ b onI _ _ (by
        simp [ofI, lowBits, hl', Finset.mem_range.mp hk])
    rw [h1, one_mul]
    apply Finset.prod_congr rfl
    intro t _
    rw [hv_I ρ b onI _ _ (by simp [ofI, lowBits, hl'])]
    have e1 : bitOf b (b.bitsC + t) = t := by simp [bitOf, lowBits, hl']
    have e2 : (iOf b x).testBit t = x.testBit (b.bitsC + t) := by
      simp only [iOf, hl', Bool.false_eq_true, if_false, Nat.testBit_div_two_pow]
      first
        | rfl
        | rw [Nat.add_comm]
    rw [e1, e2]

/-! ## The product form's weight at an index of the block -/

theorem foldl_mulE (g : Nat → E) : ∀ (l : List Nat) (a : E),
    ρ.val (l.foldl (fun s i => mulE s (g i)) a) = ρ.val a * (l.map fun i => ρ.val (g i)).prod
  | [], a => by simp
  | i :: l, a => by
    rw [List.foldl_cons, foldl_mulE g l, ρ.mul, List.map_cons, List.prod_cons, mul_assoc]

theorem drop_range (n k : Nat) : (List.range n).drop k = (List.range (n - k)).map (k + ·) := by
  apply List.ext_getElem?
  intro i
  by_cases h : k + i < n
  · simp [show i < n - k by omega]
  · simp [show ¬ i < n - k by omega]

theorem prod_map_range (g : ℕ → K) :
    ∀ n, ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_map_range g n,
      Finset.prod_range_succ]
    simp

/-- IndexWeights.above: the factors of the bits from "bits" on, at the bits of "first". -/
theorem above_val (onI : IndexWeights) (hI : onI.values = none) (first bits : Nat) (aI : E)
    (h : onI.above first bits = some aI) :
    ρ.val aI = ∏ k ∈ Finset.range (onI.lo.size - bits),
      fI ρ onI (bits + k) (first.testBit (bits + k)) := by
  unfold IndexWeights.above at h
  simp only [IndexWeights.writtenOut, hI, Option.isSome_none, Bool.false_eq_true, if_false] at h
  split at h
  · simp at h
  · have e := Option.some.inj h
    rw [← e, foldl_mulE, ρ.one, one_mul, drop_range, List.map_map, prod_map_range]
    apply Finset.prod_congr rfl
    intro k _
    simp only [Function.comp, bit_eq, fI]
    split <;> rfl

/-- The weight of a product form at first + i', where first is a multiple of 2^bits and i' is below
2^bits: the low bits are those of i', the others those of first. -/
theorem weight_split (onI : IndexWeights) (hI : onI.values = none) (first bits i' : Nat) (aI : E)
    (hal : first % 2 ^ bits = 0) (hi' : i' < 2 ^ bits) (hle : bits ≤ onI.lo.size)
    (ha : onI.above first bits = some aI) :
    weightAt ρ onI (first + i') =
      ρ.val aI * ∏ t ∈ Finset.range bits, fI ρ onI t (i'.testBit t) := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hal
  rw [above_val ρ onI hI _ _ aI ha]
  unfold weightAt
  rw [hI]
  show (∏ t ∈ Finset.range onI.lo.size, _) = _
  obtain ⟨m, hm⟩ : ∃ m, onI.lo.size = bits + m := ⟨onI.lo.size - bits, by omega⟩
  rw [hm, Finset.prod_range_add, Nat.add_sub_cancel_left, mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    have hn : ¬ bits + k < bits := by omega
    have e0 : (2 ^ bits * q).testBit (bits + k) = q.testBit (bits + k - bits) := by
      have e := Nat.testBit_two_pow_mul_add q (Nat.two_pow_pos bits) (bits + k)
      rw [Nat.add_zero] at e
      rw [e]
      exact if_neg hn
    have e1 : (2 ^ bits * q + i').testBit (bits + k) = q.testBit (bits + k - bits) := by
      rw [Nat.testBit_two_pow_mul_add q hi']
      exact if_neg hn
    rw [e1, e0]
    rfl
  · apply Finset.prod_congr rfl
    intro t ht
    have e1 : (2 ^ bits * q + i').testBit t = i'.testBit t := by
      rw [Nat.testBit_two_pow_mul_add q hi']
      exact if_pos (Finset.mem_range.mp ht)
    rw [e1]
    rfl

/-! ## The written-out factor's index -/

/-- The variable of the table's index that carries bit xb of an element's number. -/
def varOfX (b : LaidBlock) (R xb : Nat) : Nat :=
  if xb < b.placeBits then R + xb else xb - b.placeBits

/-- The bit of an element's number that is bit i of the column index. -/
def xbC (b : LaidBlock) (i : Nat) : Nat := if b.iIsLow then b.bitsI + i else i

theorem denseFrom_length (b : LaidBlock) : ∀ (xs : List Nat) (pos : Nat),
    (denseFrom b pos xs).length = xs.countP fun xb => !ofI b xb
  | [], _ => rfl
  | xb :: xs, pos => by
    rw [denseFrom, List.length_append, denseFrom_length b xs, List.countP_cons]
    cases ofI b xb
    · simp
      omega
    · simp

theorem mem_denseFrom (b : LaidBlock) (y : Nat × Nat) : ∀ (xs : List Nat) (pos : Nat),
    y ∈ denseFrom b pos xs ↔
      ∃ k xb, xs[k]? = some xb ∧ ofI b xb = false ∧ y = (bitOf b xb, pos + k)
  | [], _ => by simp [denseFrom]
  | x0 :: xs, pos => by
    rw [denseFrom, List.mem_append, mem_denseFrom b y xs (pos + 1)]
    constructor
    · rintro (h | ⟨k, xb, h1, h2, h3⟩)
      · by_cases ho : ofI b x0 = true
        · simp [ho] at h
        · have ho' : ofI b x0 = false := by simpa using ho
          simp only [ho', Bool.false_eq_true, if_false, List.mem_singleton] at h
          exact ⟨0, x0, by simp, ho', by simpa using h⟩
      · exact ⟨k + 1, xb, by simpa using h1, h2, by rw [h3]; congr 1; omega⟩
    · rintro ⟨k, xb, h1, h2, h3⟩
      cases k with
      | zero =>
        left
        have e : x0 = xb := by simpa using h1
        subst e
        simp [h2, h3]
      | succ k =>
        right
        exact ⟨k, xb, by simpa using h1, h2, by rw [h3]; congr 1; omega⟩

theorem range_get (n k a : Nat) : (List.range n)[k]? = some a ↔ k < n ∧ a = k := by
  constructor
  · intro h
    obtain ⟨hk, e⟩ := List.getElem?_eq_some_iff.mp h
    simp only [List.length_range] at hk
    simp only [List.getElem_range] at e
    exact ⟨hk, e.symm⟩
  · rintro ⟨h, rfl⟩
    simp [h]

/-- The dense variables of the two stretches. -/
def denseAll (b : LaidBlock) (R : Nat) : List (Nat × Nat) :=
  denseFrom b 0 ((List.range b.rowBits).map (· + b.placeBits)) ++
    denseFrom b R (List.range b.placeBits)

theorem mem_denseAll (b : LaidBlock) (R : Nat) (y : Nat × Nat) :
    y ∈ denseAll b R ↔ ∃ xb, xb < b.placeBits + b.rowBits ∧ ofI b xb = false ∧
      y = (bitOf b xb, varOfX b R xb) := by
  rw [denseAll, List.mem_append, mem_denseFrom, mem_denseFrom]
  constructor
  · rintro (⟨k, xb, h1, h2, h3⟩ | ⟨k, xb, h1, h2, h3⟩)
    · simp only [List.getElem?_map, Option.map_eq_some_iff] at h1
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨hk, rfl⟩ := (range_get _ _ _).mp ha
      refine ⟨a + b.placeBits, by omega, h2, ?_⟩
      rw [h3, varOfX, if_neg (by omega)]
      congr 1
      omega
    · obtain ⟨hk, rfl⟩ := (range_get _ _ _).mp h1
      exact ⟨xb, by omega, h2, by rw [h3, varOfX, if_pos hk]⟩
  · rintro ⟨xb, h1, h2, h3⟩
    by_cases hp : xb < b.placeBits
    · right
      exact ⟨xb, xb, by simp [hp], h2, by rw [h3, varOfX, if_pos hp]⟩
    · left
      refine ⟨xb - b.placeBits, xb, ?_, h2, ?_⟩
      · rw [List.getElem?_map, (range_get _ _ _).mpr ⟨by omega, rfl⟩, Option.map_some]
        congr 1
        omega
      · rw [h3, varOfX, if_neg hp, Nat.zero_add]

theorem xbC_spec (b : LaidBlock) (i : Nat) (hi : i < b.bitsC) :
    xbC b i < b.bitsI + b.bitsC ∧ ofI b (xbC b i) = false ∧ bitOf b (xbC b i) = i := by
  by_cases hl : b.iIsLow = true
  · simp [xbC, ofI, bitOf, lowBits, hl, hi]
  · have hl' : b.iIsLow = false := by simpa using hl
    simp [xbC, ofI, bitOf, lowBits, hl', hi]
    omega

theorem xbC_unique (b : LaidBlock) (xb i : Nat) (h1 : ofI b xb = false) (h2 : bitOf b xb = i) :
    xb = xbC b i := by
  by_cases hl : b.iIsLow = true
  · simp only [ofI, lowBits, hl, if_true, beq_true, decide_eq_false_iff_not] at h1
    simp only [bitOf, lowBits, hl, if_true, if_neg h1] at h2
    simp only [xbC, hl, if_true]
    omega
  · have hl' : b.iIsLow = false := by simpa using hl
    simp only [ofI, lowBits, hl', Bool.false_eq_true, if_false, beq_false, Bool.not_eq_false',
      decide_eq_true_eq] at h1
    simp only [bitOf, lowBits, hl', Bool.false_eq_true, if_false, if_pos h1] at h2
    simp only [xbC, hl', Bool.false_eq_true, if_false]
    omega

theorem countC (b : LaidBlock) :
    (List.range (b.bitsI + b.bitsC)).countP (fun xb => !ofI b xb) = b.bitsC := by
  by_cases hl : b.iIsLow = true
  · rw [List.range_add, List.countP_append]
    have h1 : (List.range b.bitsI).countP (fun xb => !ofI b xb) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      simp [ofI, lowBits, hl, List.mem_range.mp ha]
    have h2 : ((List.range b.bitsC).map (b.bitsI + ·)).countP (fun xb => !ofI b xb) =
        ((List.range b.bitsC).map (b.bitsI + ·)).length := by
      rw [List.countP_eq_length]
      intro a ha
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      simp [ofI, lowBits, hl]
    rw [h1, h2]
    simp
  · have hl' : b.iIsLow = false := by simpa using hl
    rw [Nat.add_comm, List.range_add, List.countP_append]
    have h1 : (List.range b.bitsC).countP (fun xb => !ofI b xb) = (List.range b.bitsC).length := by
      rw [List.countP_eq_length]
      intro a ha
      simp [ofI, lowBits, hl', List.mem_range.mp ha]
    have h2 : ((List.range b.bitsI).map (b.bitsC + ·)).countP (fun xb => !ofI b xb) = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
      simp [ofI, lowBits, hl']
    rw [h1, h2]
    simp

theorem denseAll_length (b : LaidBlock) (R : Nat)
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) : (denseAll b R).length = b.bitsC := by
  rw [denseAll, List.length_append, denseFrom_length, denseFrom_length, Nat.add_comm,
    ← List.countP_append]
  have e : List.range b.placeBits ++ (List.range b.rowBits).map (· + b.placeBits) =
      List.range (b.bitsI + b.bitsC) := by
    rw [← hs, Nat.add_comm b.rowBits, List.range_add]
    congr 1
    apply List.map_congr_left
    intro a _
    omega
  rw [e, countC]

theorem find_dense (dense : List (Nat × Nat)) (i v : Nat) (hmem : (i, v) ∈ dense)
    (huniq : ∀ y ∈ dense, y.1 = i → y.2 = v) :
    ((dense.find? fun x => x.1 == i).map (·.2)).getD 0 = v := by
  cases hf : dense.find? (fun x => x.1 == i) with
  | none =>
    have h := List.find?_eq_none.mp hf (i, v) hmem
    simp at h
  | some y =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [Option.map_some, Option.getD_some]
    exact huniq y h2 (by simpa using h1)

/-- laidTensor's list of dense variables: bit i of the column index is carried by the variable of
bit xbC i of the element's number. -/
theorem varsOf_denseAll (b : LaidBlock) (R : Nat)
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) :
    varsOf (denseAll b R) = (List.range b.bitsC).map fun i => varOfX b R (xbC b i) := by
  rw [varsOf, denseAll_length b R hs]
  apply List.map_congr_left
  intro i hi
  obtain ⟨c1, c2, c3⟩ := xbC_spec b i (List.mem_range.mp hi)
  apply find_dense
  · rw [mem_denseAll]
    exact ⟨xbC b i, by omega, c2, by rw [c3]⟩
  · intro y hy hyi
    obtain ⟨xb, _, h2, rfl⟩ := (mem_denseAll b R y).mp hy
    rw [xbC_unique b xb i h2 hyi]

theorem bit_val (a i : Nat) : a / 2 ^ i % 2 = if a.testBit i then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ i) with h | h <;> simp [h]

theorem denseIndex_bits (J : Nat) : ∀ (n s : Nat) (g : Nat → Nat) (m : Nat),
    (∀ i, i < n → J.testBit (g (s + i)) = m.testBit i) →
    denseIndex ((List.range' s n).map g) s J = 2 ^ s * (m % 2 ^ n)
  | 0, s, g, m, _ => by simp [denseIndex, Nat.mod_one]
  | n + 1, s, g, m, H => by
    rw [List.range'_succ, List.map_cons, denseIndex,
      denseIndex_bits J n (s + 1) g (m / 2) (fun i hi => by
        have h := H (i + 1) (by omega)
        rw [show s + (i + 1) = s + 1 + i by omega, Nat.testBit_succ] at h
        exact h)]
    have h0 := H 0 (by omega)
    have e : J / 2 ^ g s % 2 = m % 2 := by
      have e1 := bit_val J (g s)
      have e2 := bit_val m 0
      rw [Nat.add_zero] at h0
      rw [h0] at e1
      rw [e1, ← e2]
      simp
    rw [e, Nat.pow_succ' (n := n), mod_two_mul, pow_succ]
    ring

/-- **The index within the written-out vector is the column within the block.** -/
theorem denseIndex_cOf (b : LaidBlock) (R J : Nat)
    (hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC) :
    denseIndex (varsOf (denseAll b R)) 0 J = cOf b (xOf b R J) % 2 ^ b.bitsC := by
  rw [varsOf_denseAll b R hs, List.range_eq_range',
    denseIndex_bits J b.bitsC 0 _ (cOf b (xOf b R J)) ?_]
  · simp
  · intro i hi
    obtain ⟨c1, _, _⟩ := xbC_spec b i hi
    rw [Nat.zero_add]
    have e1 : J.testBit (varOfX b R (xbC b i)) = (xOf b R J).testBit (xbC b i) := by
      unfold varOfX
      by_cases hp : xbC b i < b.placeBits
      · rw [if_pos hp, x_low b R J _ hp, Nat.testBit_div_two_pow, Nat.add_comm]
      · rw [if_neg hp]
        have hx := x_high b R J (xbC b i - b.placeBits) (by omega)
        rw [show b.placeBits + (xbC b i - b.placeBits) = xbC b i by omega] at hx
        exact hx.symm
    rw [e1]
    by_cases hl : b.iIsLow = true
    · simp only [cOf, xbC, hl, if_true, Nat.testBit_div_two_pow]
      rw [Nat.add_comm]
    · have hl' : b.iIsLow = false := by simpa using hl
      simp [cOf, xbC, hl', Nat.testBit_mod_two_pow, hi]

/-! ## The entries of laidTensor -/

/-- What laidBlockOk says. -/
structure BlockFacts (b : LaidBlock) (R P : Nat) : Prop where
  hs : b.rowBits + b.placeBits = b.bitsI + b.bitsC
  hR : b.rowBits ≤ R
  hP : b.placeBits ≤ P
  alI : b.firstI % 2 ^ b.bitsI = 0
  alC : b.firstC % 2 ^ b.bitsC = 0
  alRow : b.firstRow % 2 ^ b.rowBits = 0
  alPlace : b.firstPlace % 2 ^ b.placeBits = 0
  rowLt : b.firstRow < 2 ^ R
  placeLt : b.firstPlace < 2 ^ P

theorem blockFacts (b : LaidBlock) (R P : Nat) (h : laidBlockOk b R P = true) :
    BlockFacts b R P := by
  simp only [laidBlockOk, laidAligned, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4.2, h5.2, h6.2, h7.2, h8, h9⟩

theorem xOf_lt (b : LaidBlock) (R J : Nat) : xOf b R J < 2 ^ (b.placeBits + b.rowBits) := by
  unfold xOf
  have h1 : J % 2 ^ b.rowBits + 1 ≤ 2 ^ b.rowBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : J / 2 ^ R % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 := Nat.mul_le_mul_left (2 ^ b.placeBits) h1
  rw [Nat.mul_add, Nat.mul_one] at h3
  rw [Nat.pow_add]
  omega

theorem iOf_lt (b : LaidBlock) (x : Nat) (hx : x < 2 ^ (b.bitsI + b.bitsC)) :
    iOf b x < 2 ^ b.bitsI := by
  unfold iOf
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hx

theorem cOf_lt (b : LaidBlock) (x : Nat) (hx : x < 2 ^ (b.bitsI + b.bitsC)) :
    cOf b x < 2 ^ b.bitsC := by
  unfold cOf
  split
  · apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    exact hx
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem insertChoice_end (v : Tensor) (hd : v.denseVars = []) (n val : Nat) :
    v.insertChoice v.vars n val = { v with pairs := v.pairs ++ choicePairs n val } := by
  simp [Tensor.insertChoice, Tensor.vars, hd]

/-- All pairs of the tensor: the high bits of the element's number; the choice of the block's rows;
the low bits; the choice of the block's places. -/
def pairsAll (b : LaidBlock) (R P : Nat) (onI : IndexWeights) : List (E × E) :=
  ((List.range b.rowBits).map (· + b.placeBits)).map (pairOf b onI) ++
    choicePairs (R - b.rowBits) (b.firstRow / 2 ^ b.rowBits) ++
    (List.range b.placeBits).map (pairOf b onI) ++
    choicePairs (P - b.placeBits) (b.firstPlace / 2 ^ b.placeBits)

/-- 1 if the table's index J is in the block's rows and places, else 0. -/
def inBlock (b : LaidBlock) (R P J : Nat) : K :=
  (if J / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) =
      b.firstRow / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) then 1 else 0) *
  (if J / 2 ^ (R + b.placeBits) % 2 ^ (P - b.placeBits) =
      b.firstPlace / 2 ^ b.placeBits % 2 ^ (P - b.placeBits) then 1 else 0)

theorem pairsAll_val (b : LaidBlock) (R P : Nat) (onI : IndexWeights) (F : BlockFacts b R P)
    (J : Nat) :
    pairsVal ρ (pairsAll b R P onI) J = inBlock b R P J *
      ∏ t ∈ Finset.range b.bitsI, fI ρ onI t ((iOf b (xOf b R J)).testBit t) := by
  have hR := F.hR
  unfold pairsAll
  rw [pairsVal_append, pairsVal_append, pairsVal_append, pairsVal_choice, pairsVal_choice]
  simp only [List.length_append, List.length_map, List.length_range, choicePairs_length]
  rw [show b.rowBits + (R - b.rowBits) = R by omega]
  have e := prodX ρ b onI R J
  rw [Nat.add_comm b.placeBits, F.hs, prodI] at e
  rw [← e]
  unfold inBlock
  ring

/-- **What laidTensor puts on the entry J of the table**: 0 outside the block; inside,
scalar * onI[i] * onC[c] at the element (i, c) that the layout puts there. onI: a product form;
onC: written out (as K9's terms have them). -/
theorem laidTensor_entry (b : LaidBlock) (R P : Nat) (onI onC : IndexWeights)
    (hI : onI.values = none) (L : Array E) (hC : onC.values = some L) (scalar : E) (t : Tensor)
    (h : laidTensor b R P onI onC scalar = some t) (J : Nat) :
    ρ.val (t.entry J) = inBlock b R P J * (ρ.val scalar *
      weightAt ρ onI (b.firstI + iOf b (xOf b R J)) *
      weightAt ρ onC (b.firstC + cOf b (xOf b R J))) := by
  obtain ⟨hok, aI, d1, d3, ha, h1, h3, hcase⟩ := laidTensor_parts b R P onI onC hI L hC scalar t h
  have F := blockFacts b R P hok
  have hR := F.hR
  obtain ⟨a1, a2, a3⟩ := pushBits_spec b onI onC hI L hC _ _ _ h1
  obtain ⟨b1, b2, b3⟩ := pushBits_spec b onI onC hI L hC _ _ _ h3
  have hd1 : d1.t.denseVars = [] := by rw [a1]
  have e2 : d1.t.insertChoice d1.t.vars (R - b.rowBits) (b.firstRow / 2 ^ b.rowBits) =
      { d1.t with pairs := d1.t.pairs ++
        choicePairs (R - b.rowBits) (b.firstRow / 2 ^ b.rowBits) } := insertChoice_end _ hd1 _ _
  simp only [e2] at b1 b2
  have hd3 : d3.t.denseVars = [] := by rw [b1, a1]
  have e4 : d3.t.insertChoice d3.t.vars (P - b.placeBits) (b.firstPlace / 2 ^ b.placeBits) =
      { scalar := scalar, pairs := pairsAll b R P onI } := by
    rw [insertChoice_end _ hd3, b1, a1]
    simp [pairsAll]
  have hdense : d3.dense = denseAll b R := by
    rw [b2, a2, a1]
    simp only [List.nil_append, List.length_append, List.length_map, List.length_range,
      choicePairs_length, List.length_nil, denseAll]
    rw [show b.rowBits + (R - b.rowBits) = R by omega]
  have hx : xOf b R J < 2 ^ (b.bitsI + b.bitsC) := by
    rw [← F.hs, Nat.add_comm]
    exact xOf_lt b R J
  have hle : b.bitsI ≤ onI.lo.size := by
    by_contra hn
    have hpos : 0 < b.bitsI := by omega
    have key : ∀ xb, xb < b.placeBits + b.rowBits → ofI b xb = true →
        bitOf b xb < onI.lo.size := by
      intro xb hxb ho
      by_cases hp : xb < b.placeBits
      · exact b3 xb (List.mem_range.mpr hp) ho
      · exact a3 xb (List.mem_map.mpr ⟨xb - b.placeBits, List.mem_range.mpr (by omega),
          by omega⟩) ho
    have hs := F.hs
    by_cases hl : b.iIsLow = true
    · have := key (b.bitsI - 1) (by omega) (by simp [ofI, lowBits, hl]; omega)
      simp only [bitOf, lowBits, hl, if_true] at this
      rw [if_pos (by omega)] at this
      omega
    · have hl' : b.iIsLow = false := by simpa using hl
      have := key (b.bitsC + (b.bitsI - 1)) (by omega) (by simp [ofI, lowBits, hl'])
      simp only [bitOf, lowBits, hl', Bool.false_eq_true, if_false] at this
      rw [if_neg (by omega)] at this
      omega
  have hw := weight_split ρ onI hI b.firstI b.bitsI (iOf b (xOf b R J)) aI F.alI
    (iOf_lt b _ hx) hle ha
  have hwC : ∀ c, weightAt ρ onC c = ρ.val (L.getD c zeroE) := fun c => by
    unfold weightAt
    rw [hC]
  rw [hw, hwC]
  rcases hcase with ⟨hd, v, hv, rfl⟩ | ⟨hd, rfl⟩
  · have hb0 : b.bitsC = 0 := by
      rw [← denseAll_length b R F.hs, ← hdense]
      simpa using hd
    have hc0 : cOf b (xOf b R J) = 0 := by
      have := cOf_lt b _ hx
      rw [hb0] at this
      omega
    rw [hc0, Nat.add_zero, Array.getD_eq_getD_getElem?, hv, Option.getD_some, Tensor.entry_scale,
      Tensor.entry_scale, Tensor.entry_scale, e4, Tensor.entry_val, ρ.one]
    simp only [Tensor.denseVal, List.isEmpty_nil, if_true]
    rw [pairsAll_val ρ b R P onI F]
    ring
  · have hne : (varsOf d3.dense).isEmpty = false := by
      cases hq : d3.dense with
      | nil => simp [hq] at hd
      | cons y l => simp [varsOf, List.range_succ]
    rw [Tensor.entry_val]
    simp only [Tensor.setValues, Tensor.scale, Tensor.denseVal, hne, Bool.false_eq_true, if_false,
      e4, ρ.mul, ρ.one]
    rw [pairsAll_val ρ b R P onI F, hdense, denseIndex_cOf b R J F.hs,
      Nat.mod_eq_of_lt (cOf_lt b _ hx)]
    ring

/-! ## A form, the terms, the row -/

/-- What one block's tensor puts on the entry J of the table. -/
def laidVal (b : LaidBlock) (R P : Nat) (onI onC : IndexWeights) (scalar : E) (J : Nat) : K :=
  inBlock b R P J * (ρ.val scalar * weightAt ρ onI (b.firstI + iOf b (xOf b R J)) *
    weightAt ρ onC (b.firstC + cOf b (xOf b R J)))

theorem laidForm_entry (blocks : List LaidBlock) (R P : Nat) (onI onC : IndexWeights)
    (hI : onI.values = none) (L : Array E) (hC : onC.values = some L) (scalar : E) (f : Form)
    (h : laidForm blocks R P onI onC scalar = some f) (J : Nat) :
    ρ.val (f.entry J) = (blocks.map fun b => laidVal ρ b R P onI onC scalar J).sum := by
  unfold laidForm at h
  have e := foldlM_adds (fun (f : Form) b => (laidTensor b R P onI onC scalar).map f.add)
    (fun _ => True) (fun f => ρ.val (f.entry J)) (fun b => laidVal ρ b R P onI onC scalar J)
    (fun s b s' _ hs => ⟨trivial, by
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hs
      beta_reduce
      rw [Form.entry_add, laidTensor_entry ρ b R P onI onC hI L hC scalar t ht J]
      rfl⟩) blocks {} f trivial h
  have e2 := e.2
  beta_reduce at e2
  rw [e2, Form.entry_empty, zero_add]

/-- A term as K9 makes them: a product form on the rows, a written-out vector on the columns. -/
structure K9Term (t : ReqTerm) : Prop where
  rows : t.onRows.values = none
  cols : ∃ L, t.onColumns.values = some L

/-- What a term puts on the entry J of the main table of the oracle message o. -/
def termAt (Rr : ReqRows) (f : ReqFrame) (S : Statement) (t : ReqTerm) (o J : Nat) : K :=
  match reqArray Rr.layout t.born t.array with
  | none => 0
  | some a =>
    match f.whereIs t.born a.message with
    | none => 0
    | some o' =>
      if o' = o then
        (a.blocks.map fun b => laidVal ρ b (S.rowBits o' .main) (S.placeBits o' .main) t.onRows
          t.onColumns t.scale J).sum
      else 0

theorem coef_empty (o : Nat) (part : OnBytes.Part) (J : Nat) :
    ρ.val (({} : OnBytes.Row).coefficient o part J) = 0 := by
  simp [Row.coefficient_val]

theorem coef_addForm (row : OnBytes.Row) (o' : Nat) (c : Form) (o : Nat) (part : OnBytes.Part)
    (J : Nat) :
    ρ.val ((row.addForm o' c).coefficient o part J) = ρ.val (row.coefficient o part J) +
      if o' = o ∧ part = .main then ρ.val (c.entry J) else 0 := by
  simp only [Row.coefficient_val, Row.addForm, Array.toList_push, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

theorem coef_addRun (row : OnBytes.Row) (o' : Nat) (p : OnBytes.Part) (first step : Nat)
    (c : Coeffs) (o : Nat) (part : OnBytes.Part) (J : Nat) :
    ρ.val ((row.addRun o' p first step c).coefficient o part J) =
      ρ.val (row.coefficient o part J) +
        if o' = o ∧ p = part then Run.val ρ ⟨o', p, first, step, c⟩ J else 0 := by
  simp only [Row.coefficient_val, Row.addRun, Array.toList_push, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring

/-- **The terms as a row**: entry by entry. -/
theorem addTerms_coef (Rr : ReqRows) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), (∀ t ∈ ts, K9Term t) →
      Rr.addTerms f S ts row = some row' →
      (∀ o J, ρ.val (row'.coefficient o .main J) = ρ.val (row.coefficient o .main J) +
        (ts.map fun t => termAt ρ Rr f S t o J).sum) ∧
      ∀ o J, ρ.val (row'.coefficient o .mask J) = ρ.val (row.coefficient o .mask J)
  | [], row, row', _, h => by
    have e : row = row' := Option.some.inj h
    subst e
    simp
  | t :: ts, row, row', hk, h => by
    rw [ReqRows.addTerms] at h
    obtain ⟨a, ha, h⟩ := some_bind h
    obtain ⟨o', ho, h⟩ := some_bind h
    obtain ⟨c, hc, h⟩ := some_bind h
    obtain ⟨i1, i2⟩ := addTerms_coef Rr f S ts (row.addForm o' c) row'
      (fun t' ht' => hk t' (List.mem_cons_of_mem _ ht')) h
    have kt := hk t (List.mem_cons_self ..)
    obtain ⟨L, hL⟩ := kt.cols
    refine ⟨fun o J => ?_, fun o J => ?_⟩
    · rw [i1, coef_addForm, List.map_cons, List.sum_cons]
      have e : termAt ρ Rr f S t o J =
          if o' = o ∧ OnBytes.Part.main = OnBytes.Part.main then ρ.val (c.entry J) else 0 := by
        unfold termAt
        rw [ha]
        dsimp only
        rw [ho]
        simp only [and_true]
        split
        · rw [laidForm_entry ρ _ _ _ _ _ kt.rows L hL _ c hc J]
        · rfl
      rw [e]
      ring
    · rw [i2, coef_addForm]
      simp

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.laidTensor_entry
#print axioms VerifiableInference.Desc.K9L.addTerms_coef
