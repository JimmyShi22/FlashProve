-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PadTensor.lean: THE TENSOR THAT THE BATCHING's DOOR MAKES FOR ONE LAID BLOCK OF AN ARRAY (`blockTensor`,
Johnson/Desc/First/Batch/Lay.lean) HAS THE ENTRY 0 AT EVERY INDEX OF ITS TABLE THAT THE BLOCK DOES NOT COVER, word for word, whatever the weights and
the scalar are. So has the sum over an array's blocks (`blocksForm`) at an index that none of the blocks covers. The text's own comment
says "0 elsewhere"; here it is a theorem. General: no description, no state, no hypothesis of the library.

Why it holds. The tensor's variables are: the block's row bits; then variables that pick the bits of the block's first row above its
side; the block's place bits; then variables that pick the bits of the block's first place above its side. A variable that picks a
bit has the pair (1, 0) or (0, 1): at an index with the other bit the product takes the factor 0, and a product with the word 0
is the word 0 (OnBytes/Field/ZeroE.lean).

  `pairsAt_zeroE`, `pairsAt_append`, **`pairsAt_choice_off`**   the product over the pairs
  `pairsAt_four`        at a list of pairs of the four stretches
  `bitVar_pairs`, `bitVars_pairs`, `tail_pairs`, **`blockTensor_pairs`**   the pairs of the tensor that is made are of that form
  `inside_of_div`, **`off_of_uncovered`**   an index inside the table that the block does not cover differs from the block in a picked bit
  **`blockTensor_off`**   the entry is 0
  `form_entry_zero`, **`blocksForm_off`**   so is the entry of the sum over the blocks

Limits. Indices inside the table alone (below 2 ^ (row bits + place bits)): bits of an index above the variables are not looked at. Nothing
on the entries inside a block. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.First.Batch.Shape.DoorMk
import OnBytes.Field.ZeroE
import OnBytes.Iop.TensorLaws
import OnBytes.Iop.ReqRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock)
open VerifiableInference.Desc.K9 (Ans need there blockTensor blocksForm bitVar bitVars blockFits aligned tensorFits)
open VerifiableInference.Desc.K9.Shape (ans_bind need_ok there_ok denseOf)

/-! ## The product over the pairs -/

theorem addE_zero_zero' : addE zeroE zeroE = zeroE := by
  unfold addE zeroE
  simp only [E.c0_mk3, E.c1_mk3, E.c2_mk3, OnBytes.addF_zero_zero]

theorem pairsAt_zeroE : ∀ (ps : List (E × E)) (j : ℕ), pairsAt ps j zeroE = zeroE
  | [], j => pairsAt_nil j zeroE
  | p :: ps, j => by
    rw [pairsAt_cons, mulE_zero_left]
    exact pairsAt_zeroE ps _

theorem pairsAt_append : ∀ (a b : List (E × E)) (j : ℕ) (r : E),
    pairsAt (a ++ b) j r = pairsAt b (j / 2 ^ a.length) (pairsAt a j r)
  | [], b, j, r => by
    rw [List.nil_append, pairsAt_nil, List.length_nil, Nat.pow_zero, Nat.div_one]
  | p :: a, b, j, r => by
    rw [List.cons_append, pairsAt_cons, pairsAt_cons, pairsAt_append a b, List.length_cons,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- **Variables that pick the low n bits of a value: at an index with other low n bits the product is 0.** -/
theorem pairsAt_choice_off : ∀ (n value j : ℕ) (r : E), j % 2 ^ n ≠ value % 2 ^ n →
    pairsAt (choicePairs n value) j r = zeroE
  | 0, value, j, r, h => absurd (by simp [Nat.mod_one]) h
  | n + 1, value, j, r, h => by
    rw [show choicePairs (n + 1) value =
      (if value % 2 == 1 then (zeroE, oneE) else (oneE, zeroE)) :: choicePairs n (value / 2) from rfl,
      pairsAt_cons]
    by_cases hb : j % 2 = value % 2
    · refine pairsAt_choice_off n (value / 2) (j / 2) _ fun e => h ?_
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul, Nat.mod_mul, hb, e]
    · have hz : (if j % 2 == 1 then (if value % 2 == 1 then (zeroE, oneE) else (oneE, zeroE)).2
          else (if value % 2 == 1 then (zeroE, oneE) else (oneE, zeroE)).1) = zeroE := by
        rcases Nat.mod_two_eq_zero_or_one j with a | a <;> rcases Nat.mod_two_eq_zero_or_one value with c | c
        · exact absurd (a.trans c.symm) hb
        · simp [a, c]
        · simp [a, c]
        · exact absurd (a.trans c.symm) hb
      rw [hz, mulE_zero_right]
      exact pairsAt_zeroE _ _

/-- The four stretches. -/
theorem pairsAt_four (P1 P2 : List (E × E)) (n1 v1 n2 v2 j : ℕ) (r : E)
    (h : (j / 2 ^ P1.length) % 2 ^ n1 ≠ v1 % 2 ^ n1 ∨
      (j / 2 ^ (P1.length + n1 + P2.length)) % 2 ^ n2 ≠ v2 % 2 ^ n2) :
    pairsAt (P1 ++ choicePairs n1 v1 ++ P2 ++ choicePairs n2 v2) j r = zeroE := by
  rw [pairsAt_append, pairsAt_append, pairsAt_append]
  rcases h with h | h
  · rw [pairsAt_choice_off n1 v1 _ _ h, pairsAt_zeroE, pairsAt_zeroE]
  · refine pairsAt_choice_off n2 v2 _ _ ?_
    rw [List.length_append, List.length_append, choicePairs_length]
    exact h

/-! ## The pairs of the tensor that is made -/

theorem bitVar_pairs (d e : LaidDraft) (b : LaidBlock) (onI onC : IndexWeights) (xBit : ℕ)
    (h : bitVar d b onI onC xBit = .ok e) : ∃ p, e.t.pairs = d.t.pairs ++ [p] := by
  unfold bitVar at h
  simp only at h
  generalize (if (decide (xBit < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
    then onI else onC) = w at h
  generalize (if xBit < (if b.iIsLow = true then b.bitsI else b.bitsC) then xBit
    else xBit - (if b.iIsLow = true then b.bitsI else b.bitsC)) = bit at h
  by_cases hv : w.values.isSome = true
  · rw [if_pos hv] at h
    obtain rfl := Except.ok.inj h
    exact ⟨(oneE, oneE), rfl⟩
  · rw [if_neg hv] at h
    cases e1 : w.lo[bit]? with
    | none =>
      rw [e1] at h
      exact nomatch h
    | some l =>
      cases e2 : w.hi[bit]? with
      | none =>
        rw [e1, e2] at h
        exact nomatch h
      | some hh =>
        rw [e1, e2] at h
        obtain rfl := Except.ok.inj h
        exact ⟨(l, hh), rfl⟩

theorem bitVars_pairs (b : LaidBlock) (onI onC : IndexWeights) : ∀ (xs : List ℕ) (d e : LaidDraft),
    bitVars d b onI onC xs = .ok e → ∃ P, P.length = xs.length ∧ e.t.pairs = d.t.pairs ++ P
  | [], d, e, h => by
    obtain rfl : d = e := Except.ok.inj h
    exact ⟨[], rfl, by simp⟩
  | x :: xs, d, e, h => by
    have h' : (bitVar d b onI onC x).bind (fun e' => bitVars e' b onI onC xs) = .ok e := h
    cases h1 : bitVar d b onI onC x with
    | error m =>
      rw [h1] at h'
      exact nomatch h'
    | ok d₁ =>
      rw [h1] at h'
      obtain ⟨p, hp⟩ := bitVar_pairs d d₁ b onI onC x h1
      obtain ⟨P, hl, hP⟩ := bitVars_pairs b onI onC xs d₁ e h'
      exact ⟨p :: P, by simp [hl], by rw [hP, hp, List.append_assoc]; rfl⟩

theorem scale_pairs (t : Tensor) (x : E) : (t.scale x).pairs = t.pairs := by
  cases t
  rfl

/-- Picking variables laid behind all others. -/
theorem insertChoice_end_pairs (v : Tensor) (n val : ℕ) :
    (v.insertChoice v.vars n val).pairs = v.pairs ++ choicePairs n val := by
  show v.pairs.take v.pairs.length ++ choicePairs n val ++ v.pairs.drop v.pairs.length = _
  rw [List.take_length, List.drop_length, List.append_nil]

/-- The last steps of the text leave the pairs. -/
theorem tail_pairs (t₀ t : Tensor) (dense : List (ℕ × ℕ)) (vals : Option (Array E)) (first : ℕ)
    (h : (match vals with
      | none =>
        (pure t₀ : Ans Tensor) >>= fun t => need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t
      | some values =>
        if dense.isEmpty then
          (there "K9.written-value-there" values[first]?).map t₀.scale >>= fun t =>
            need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t
        else
          (pure ({ t₀ with denseVars := denseOf dense }.setValues values first) : Ans Tensor) >>=
            fun t => need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t) = .ok t) :
    t.pairs = t₀.pairs := by
  cases vals with
  | none =>
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨t', e, -, e2⟩ := h
    obtain rfl := Except.ok.inj e
    obtain rfl := Except.ok.inj e2
    rfl
  | some values =>
    by_cases he : dense.isEmpty = true
    · simp only [he, if_true, ans_bind, need_ok, exists_const] at h
      obtain ⟨t', e, -, e2⟩ := h
      obtain rfl := Except.ok.inj e2
      cases hx : values[first]? with
      | none =>
        rw [hx] at e
        exact nomatch e
      | some x =>
        rw [hx] at e
        obtain rfl : t₀.scale x = t' := Except.ok.inj e
        exact scale_pairs t₀ x
    · simp only [he, Bool.false_eq_true, if_false, ans_bind, need_ok, exists_const] at h
      obtain ⟨t', e, -, e2⟩ := h
      obtain rfl := Except.ok.inj e
      obtain rfl := Except.ok.inj e2
      rfl

/-- **The pairs of a block's tensor.** -/
theorem blockTensor_pairs (b : LaidBlock) (tR tP : ℕ) (onI onC : IndexWeights) (sc : E) (t : Tensor)
    (h : blockTensor b tR tP onI onC sc = .ok t) :
    blockFits b tR tP = true ∧ ∃ P1 P2 : List (E × E), P1.length = b.rowBits ∧ P2.length = b.placeBits ∧
      t.pairs = P1 ++ choicePairs (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits) ++ P2 ++
        choicePairs (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits) := by
  unfold blockTensor at h
  simp only [ans_bind, need_ok, exists_const] at h
  obtain ⟨hf, -, -, d1, c1, d2, c2, aI, -, aC, -, h⟩ := h
  obtain ⟨P1, l1, e1⟩ := bitVars_pairs b onI onC _ _ _ c1
  obtain ⟨P2, l2, e2⟩ := bitVars_pairs b onI onC _ _ _ c2
  have l1' : P1.length = b.rowBits := by simpa using l1
  have l2' : P2.length = b.placeBits := by simpa using l2
  have e1' : d1.t.pairs = P1 := by simpa using e1
  have k1 : (d1.t.insertChoice d1.t.vars (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits)).pairs =
      P1 ++ choicePairs (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits) := by
    rw [insertChoice_end_pairs, e1']
  have e2' : d2.t.pairs = P1 ++ choicePairs (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits) ++ P2 := by
    rw [e2]
    exact congrArg (· ++ P2) k1
  have k2 : (d2.t.insertChoice d2.t.vars (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits)).pairs =
      P1 ++ choicePairs (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits) ++ P2 ++
        choicePairs (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits) := by
    rw [insertChoice_end_pairs, e2']
  refine ⟨hf, P1, P2, l1', l2', ?_⟩
  rw [← k2]
  generalize d2.t.insertChoice d2.t.vars (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits) = T₀ at h
  have hm := tail_pairs ((T₀.scale aI).scale aC) t d2.dense
    (if onI.values.isSome then onI.values else onC.values)
    (if onI.values.isSome then b.firstI else b.firstC) (by
      revert h
      generalize (if onI.values.isSome = true then onI.values else onC.values) = vals
      intro h
      cases vals with
      | none => simpa only [ans_bind, need_ok, exists_const] using h
      | some values =>
        by_cases he : d2.dense.isEmpty = true
        · simpa only [he, if_true, ans_bind, need_ok, exists_const] using h
        · simpa only [he, Bool.false_eq_true, if_false, ans_bind, need_ok, exists_const] using h)
  rw [hm, scale_pairs, scale_pairs]

/-! ## An index that the block does not cover -/

/-- Two numbers with the same quotient by K, of which the one is a multiple of K. -/
theorem inside_of_div {a f K : ℕ} (hK : 0 < K) (hf : f % K = 0) (h : a / K = f / K) : f ≤ a ∧ a < f + K := by
  have h1 := Nat.div_add_mod a K
  have h2 := Nat.div_add_mod f K
  have h3 := Nat.mod_lt a hK
  rw [h] at h1
  omega

/-- **An index inside the table that the block does not cover differs from the block in a picked bit.** -/
theorem off_of_uncovered (b : LaidBlock) (tR tP j : ℕ) (hf : blockFits b tR tP = true) (hj : j < 2 ^ (tR + tP))
    (hc : laidCovers b tR j = false) :
    (j / 2 ^ b.rowBits) % 2 ^ (tR - b.rowBits) ≠ (b.firstRow / 2 ^ b.rowBits) % 2 ^ (tR - b.rowBits) ∨
      (j / 2 ^ (b.rowBits + (tR - b.rowBits) + b.placeBits)) % 2 ^ (tP - b.placeBits) ≠
        (b.firstPlace / 2 ^ b.placeBits) % 2 ^ (tP - b.placeBits) := by
  unfold blockFits aligned at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hr⟩, hp⟩, -⟩, -⟩, ⟨-, ar⟩⟩, ⟨-, ap⟩⟩, fr⟩, fp⟩ := hf
  by_contra hn
  rw [not_or, not_not, not_not] at hn
  obtain ⟨m1, m2⟩ := hn
  have pR : (2 : ℕ) ^ tR = 2 ^ b.rowBits * 2 ^ (tR - b.rowBits) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have pP : (2 : ℕ) ^ tP = 2 ^ b.placeBits * 2 ^ (tP - b.placeBits) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  -- the row
  have q1 : j % 2 ^ tR / 2 ^ b.rowBits = b.firstRow / 2 ^ b.rowBits := by
    rw [pR, Nat.mod_mul_right_div_self, m1]
    refine Nat.mod_eq_of_lt ?_
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← pR]
    exact fr
  -- the place
  have hpl : j / 2 ^ tR < 2 ^ tP := by
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← Nat.pow_add]
    exact hj
  have eS : b.rowBits + (tR - b.rowBits) + b.placeBits = tR + b.placeBits := by omega
  have q2 : j / 2 ^ tR / 2 ^ b.placeBits = b.firstPlace / 2 ^ b.placeBits := by
    rw [eS, Nat.pow_add, ← Nat.div_div_eq_div_mul] at m2
    have a1 : j / 2 ^ tR / 2 ^ b.placeBits < 2 ^ (tP - b.placeBits) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← pP]
      exact hpl
    have a2 : b.firstPlace / 2 ^ b.placeBits < 2 ^ (tP - b.placeBits) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), Nat.mul_comm, ← pP]
      exact fp
    rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2] at m2
    exact m2
  obtain ⟨r1, r2⟩ := inside_of_div (Nat.pow_pos (by decide)) ar q1
  obtain ⟨p1, p2⟩ := inside_of_div (Nat.pow_pos (by decide)) ap q2
  have : laidCovers b tR j = true := by
    unfold laidCovers
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨r1, r2⟩, p1⟩, p2⟩
  rw [this] at hc
  exact nomatch hc

/-- **The entry of a block's tensor off its block is 0.** -/
theorem blockTensor_off (b : LaidBlock) (tR tP : ℕ) (onI onC : IndexWeights) (sc : E) (t : Tensor)
    (h : blockTensor b tR tP onI onC sc = .ok t) {j : ℕ} (hj : j < 2 ^ (tR + tP))
    (hc : laidCovers b tR j = false) : t.entry j = zeroE := by
  obtain ⟨hf, P1, P2, l1, l2, e⟩ := blockTensor_pairs b tR tP onI onC sc t h
  have hz : pairsAt t.pairs j t.scalar = zeroE := by
    rw [e]
    refine pairsAt_four P1 P2 _ _ _ _ j _ ?_
    rw [l1, l2]
    exact off_of_uncovered b tR tP j hf hj hc
  unfold Tensor.entry
  simp only [hz]
  split
  · rfl
  · exact mulE_zero_left _

/-! ## The sum over an array's blocks -/

/-- A form without single entries, all of whose tensors have the entry 0 at j. -/
theorem form_entry_zero (f : Form) (j : ℕ) (he : f.entries = []) (ht : ∀ v ∈ f.tensors, v.entry j = zeroE) :
    f.entry j = zeroE := by
  unfold Form.entry
  rw [he]
  show f.tensors.foldl (fun r v => addE r (v.entry j)) zeroE = zeroE
  generalize f.tensors = l at ht
  induction l with
  | nil => rfl
  | cons v l ih =>
    rw [List.foldl_cons, ht v (by simp), addE_zero_zero']
    exact ih fun v' hv' => ht v' (List.mem_cons_of_mem _ hv')

theorem blocks_off_from (tR tP : ℕ) (onI onC : IndexWeights) (sc : E) (j : ℕ) (hj : j < 2 ^ (tR + tP)) :
    ∀ (blocks : List LaidBlock) (f c : Form), (∀ b ∈ blocks, laidCovers b tR j = false) →
      f.entries = [] → (∀ v ∈ f.tensors, v.entry j = zeroE) →
      blocks.foldlM (fun (f : Form) b => (blockTensor b tR tP onI onC sc).map f.add) f = .ok c →
      c.entries = [] ∧ ∀ v ∈ c.tensors, v.entry j = zeroE
  | [], f, c, _, he, ht, h => by
    obtain rfl : f = c := Except.ok.inj h
    exact ⟨he, ht⟩
  | b :: bs, f, c, hb, he, ht, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨f₁, h1, h2⟩ := (ans_bind _ _ _).1 h
    cases hT : blockTensor b tR tP onI onC sc with
    | error e =>
      rw [hT] at h1
      exact nomatch h1
    | ok t =>
      rw [hT] at h1
      obtain rfl : f.add t = f₁ := Except.ok.inj h1
      refine blocks_off_from tR tP onI onC sc j hj bs (f.add t) c
        (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) he ?_ h2
      intro v hv
      have hv' : v ∈ t :: f.tensors := hv
      rcases List.mem_cons.1 hv' with rfl | hv
      · exact blockTensor_off b tR tP onI onC sc _ hT hj (hb b (by simp))
      · exact ht v hv

/-- **The entry of the sum over an array's blocks, at an index that none of them covers, is 0.** -/
theorem blocksForm_off (blocks : List LaidBlock) (tR tP : ℕ) (onI onC : IndexWeights) (sc : E) (c : Form)
    (h : blocksForm blocks tR tP onI onC sc = .ok c) {j : ℕ} (hj : j < 2 ^ (tR + tP))
    (hb : ∀ b ∈ blocks, laidCovers b tR j = false) : c.entry j = zeroE := by
  obtain ⟨he, ht⟩ := blocks_off_from tR tP onI onC sc j hj blocks {} c hb rfl (fun _ hv => nomatch hv) h
  exact form_entry_zero c j he ht

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.pairsAt_zeroE
#print axioms ProofFile.Honest.K9.pairsAt_append
#print axioms ProofFile.Honest.K9.scale_pairs
#print axioms ProofFile.Honest.K9.insertChoice_end_pairs
#print axioms ProofFile.Honest.K9.pairsAt_choice_off
#print axioms ProofFile.Honest.K9.pairsAt_four
#print axioms ProofFile.Honest.K9.bitVar_pairs
#print axioms ProofFile.Honest.K9.bitVars_pairs
#print axioms ProofFile.Honest.K9.tail_pairs
#print axioms ProofFile.Honest.K9.blockTensor_pairs
#print axioms ProofFile.Honest.K9.inside_of_div
#print axioms ProofFile.Honest.K9.off_of_uncovered
#print axioms ProofFile.Honest.K9.blockTensor_off
#print axioms ProofFile.Honest.K9.form_entry_zero
#print axioms ProofFile.Honest.K9.blocks_off_from
#print axioms ProofFile.Honest.K9.blocksForm_off
#print axioms ProofFile.Honest.K9.addE_zero_zero'
