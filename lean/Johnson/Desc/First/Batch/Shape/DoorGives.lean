-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorGives.lean: WHAT A TERM OF THE ONE EQUATION ON ONE BLOCK IS,
WHERE THE TEXT RETURNS (K9.blockTensor and K9.blocksForm, Johnson/Desc/First/Batch/Lay.lean): the
tensor has tR + tP variables (the two numbers of bits that the text is handed), and it is in order
in the sense in which the adding of a row asks it (Own.tensorInOrder, Own.formFits,
Johnson/Desc/Own/Shapes.lean). General laws, from a return; nothing is evaluated.

  `bitVar_len`, `bitVars_len`: each variable laid is one pair more.
  `ins_len`: the choice of count bits, laid behind all variables, is count pairs more.
  `noTwice_nodup`: the text's test "no number twice" gives the library's Nodup.
  `fits_inOrder`: the text's last test (tensorFits) gives Own.tensorInOrder.
  **`blockTensor_gives`**: K9.blockTensor b tR tP onI onC sc = .ok t: then t has tR + tP pairs, and
    Own.tensorInOrder t = true.
  **`blocksForm_gives`**: K9.blocksForm blocks tR tP onI onC sc = .ok c: then
    Own.formFits c (tR + tP) = true.

Limits. From a return alone. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorMade
import Johnson.Desc.Own.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (LaidBlock)

theorem bitVar_len {d d' : LaidDraft} (b : LaidBlock) (onI onC : IndexWeights) (x : Nat)
    (h : bitVar d b onI onC x = .ok d') : d'.t.pairs.length = d.t.pairs.length + 1 := by
  unfold bitVar at h
  simp only at h
  generalize (if (decide (x < if b.iIsLow = true then b.bitsI else b.bitsC) == b.iIsLow) = true
    then onI else onC) = w at h
  generalize (if x < (if b.iIsLow = true then b.bitsI else b.bitsC) then x
    else x - (if b.iIsLow = true then b.bitsI else b.bitsC)) = bit at h
  by_cases hv : w.values.isSome = true
  · rw [if_pos hv] at h
    obtain rfl := Except.ok.inj h
    show (d.t.pairs ++ [(oneE, oneE)]).length = _
    simp
  · rw [if_neg hv] at h
    cases e1 : w.lo[bit]? with
    | none => rw [e1] at h; exact nomatch h
    | some l =>
      cases e2 : w.hi[bit]? with
      | none => rw [e1, e2] at h; exact nomatch h
      | some hh =>
        rw [e1, e2] at h
        obtain rfl := Except.ok.inj h
        show (d.t.pairs ++ [(l, hh)]).length = _
        simp

theorem bitVars_len (b : LaidBlock) (onI onC : IndexWeights) :
    ∀ (xs : List Nat) (d d' : LaidDraft), bitVars d b onI onC xs = .ok d' →
      d'.t.pairs.length = d.t.pairs.length + xs.length
  | [], d, d', h => by
    obtain rfl : d = d' := Except.ok.inj h
    rfl
  | x :: xs, d, d', h => by
    have h' : (bitVar d b onI onC x).bind (fun e => bitVars e b onI onC xs) = .ok d' := h
    cases h1 : bitVar d b onI onC x with
    | error e => rw [h1] at h'; exact nomatch h'
    | ok e =>
      rw [h1] at h'
      have := bitVars_len b onI onC xs e d' h'
      rw [this, bitVar_len b onI onC x h1, List.length_cons]
      omega

theorem ins_len (t : Tensor) (c v : Nat) :
    (t.insertChoice t.vars c v).pairs.length = t.pairs.length + c := by
  show (t.pairs.take t.vars ++ choicePairs c v ++ t.pairs.drop t.vars).length = _
  have e1 : t.pairs.take t.vars = t.pairs := List.take_length
  have e2 : t.pairs.drop t.vars = [] := List.drop_length
  rw [e1, e2, List.append_nil, List.length_append, choice_length]

theorem noTwice_nodup : ∀ l : List Nat, noTwice l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have h' : (!l.contains a && noTwice l) = true := h
    rw [Bool.and_eq_true] at h'
    refine List.nodup_cons.2 ⟨?_, noTwice_nodup l h'.2⟩
    intro hm
    have : l.contains a = true := List.contains_iff_mem.2 hm
    rw [this] at h'
    exact nomatch h'.1

theorem fits_inOrder (t : Tensor) (h : tensorFits t = true) : Own.tensorInOrder t = true := by
  unfold tensorFits at h
  unfold Own.tensorInOrder
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨⟨⟨h1, h2⟩, h3⟩, decide_eq_true (noTwice_nodup _ h4)⟩

/-- The text's tail: from a tensor t₀ to the tensor returned: the pairs stay, and the last test
held. -/
theorem tail_gives (t₀ u : Tensor) (dense : List (Nat × Nat)) (vals : Option (Array E))
    (first : Nat)
    (h : (match vals with
      | none =>
        (pure t₀ : Ans Tensor) >>= fun t => need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t
      | some values =>
        if dense.isEmpty then
          (there "K9.written-value-there" values[first]?).map t₀.scale >>= fun t =>
            need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t
        else
          (pure ({ t₀ with denseVars := denseOf dense }.setValues values first) : Ans Tensor) >>=
            fun t => need "K9.tensor-fits" (tensorFits t) >>= fun _ => pure t) = .ok u) :
    u.pairs = t₀.pairs ∧ tensorFits u = true := by
  cases vals with
  | none =>
    simp only [ans_bind, need_ok, exists_const] at h
    obtain ⟨t, e, hf, e2⟩ := h
    obtain rfl := Except.ok.inj e
    obtain rfl := Except.ok.inj e2
    exact ⟨rfl, hf⟩
  | some values =>
    by_cases he : dense.isEmpty = true
    · simp only [he, if_true, ans_bind, need_ok, exists_const] at h
      obtain ⟨t, e, hf, e2⟩ := h
      obtain rfl := Except.ok.inj e2
      cases hx : values[first]? with
      | none => rw [hx] at e; exact nomatch e
      | some x =>
        rw [hx] at e
        obtain rfl : t₀.scale x = t := Except.ok.inj e
        exact ⟨pairs_scale t₀ x, hf⟩
    · simp only [he, Bool.false_eq_true, if_false, ans_bind, need_ok, exists_const] at h
      obtain ⟨t, e, hf, e2⟩ := h
      obtain rfl := Except.ok.inj e
      obtain rfl := Except.ok.inj e2
      exact ⟨rfl, hf⟩

/-- **WHAT THE TENSOR IS, WHERE THE TEXT RETURNS.** -/
theorem blockTensor_gives (b : LaidBlock) (tR tP : Nat) (onI onC : IndexWeights) (sc : E)
    (t : Tensor) (h : blockTensor b tR tP onI onC sc = .ok t) :
    t.pairs.length = tR + tP ∧ Own.tensorInOrder t = true := by
  unfold blockTensor at h
  simp only [ans_bind, need_ok, exists_const] at h
  obtain ⟨g1, -, -, d1, c1, d2, c2, aI, -, aC, -, h⟩ := h
  have l1 := bitVars_len b onI onC _ _ _ c1
  have l2 := bitVars_len b onI onC _ _ _ c2
  obtain ⟨e, hf⟩ := tail_gives
    (((d2.t.insertChoice d2.t.vars (tP - b.placeBits) (b.firstPlace / 2 ^ b.placeBits)).scale
      aI).scale aC) t d2.dense (if onI.values.isSome then onI.values else onC.values)
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
  refine ⟨?_, fits_inOrder t hf⟩
  rw [e, pairs_scale, pairs_scale, ins_len, l2]
  have l1' :
      (d1.t.insertChoice d1.t.vars (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits)).pairs.length =
        d1.t.pairs.length + (tR - b.rowBits) := ins_len _ _ _
  show (d1.t.insertChoice d1.t.vars (tR - b.rowBits) (b.firstRow / 2 ^ b.rowBits)).pairs.length +
    (List.range b.placeBits).length + (tP - b.placeBits) = _
  rw [l1', l1, List.length_map, List.length_range, List.length_range]
  unfold blockFits at g1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, q1⟩, q2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := g1
  show 0 + b.rowBits + (tR - b.rowBits) + b.placeBits + (tP - b.placeBits) = tR + tP
  omega

/-- **WHAT THE FORM IS, WHERE THE TEXT RETURNS.** -/
theorem blocksForm_gives (blocks : List LaidBlock) (tR tP : Nat) (onI onC : IndexWeights) (sc : E)
    (c : Form) (h : blocksForm blocks tR tP onI onC sc = .ok c) :
    Own.formFits c (tR + tP) = true := by
  unfold blocksForm at h
  refine foldlM_keeps _ (fun f : Form => Own.formFits f (tR + tP) = true) _ _ _ rfl
    (fun b _ f f' hf hs => ?_) h
  cases ht : blockTensor b tR tP onI onC sc with
  | error e => rw [ht] at hs; exact nomatch hs
  | ok t =>
    rw [ht] at hs
    obtain rfl : f.add t = f' := Except.ok.inj hs
    obtain ⟨g1, g2⟩ := blockTensor_gives b tR tP onI onC sc t ht
    have hf : Own.formFits f (tR + tP) = true := hf
    show Own.formFits (f.add t) (tR + tP) = true
    unfold Own.formFits at hf ⊢
    rw [Bool.and_eq_true] at hf ⊢
    refine ⟨?_, hf.2⟩
    show ((t :: f.tensors).all fun v => v.pairs.length == tR + tP && Own.tensorInOrder v) = true
    rw [List.all_cons, Bool.and_eq_true]
    exact ⟨by rw [g1, g2]; simp, hf.1⟩

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.blockTensor_gives
#print axioms VerifiableInference.Desc.K9.Shape.blocksForm_gives
#print axioms VerifiableInference.Desc.K9.Shape.bitVars_len
#print axioms VerifiableInference.Desc.K9.Shape.fits_inOrder
