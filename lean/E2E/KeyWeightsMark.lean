--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyWeightsMark.lean: THE MARK ON THE ROW WEIGHTS (`weightsB`, E2E/KeyDotFits.lean) AT THE KEY
FILE's OWN ROW WEIGHTS, WHICH HAVE A WRITTEN-OUT FACTOR. The weights are made in the first chain:
"the rows on the table" makes, for each part of each lookup, weights on stretches of the matrix's
rows; the batching lays a factor in front of each. Here: every such weight lies below the matrix's
rows, so the cut at the matrix's rows leaves it as it is; laid on a table with room for it, it is
well-formed. So the one row that the batching hands on has the mark. Statements and proofs, at all
values. On what the verifier's steps make of public values and challenges: NOTHING IS SHOWN OF ANY
PROVER.

  1  `ok_iff`, `distinct_map`, `ok_of_map`, **`onTable_ok`**: a well-formed vector (the library's
     `Tensor.ok`), with or without a written-out factor, laid on a table of at most 63 index bits
     with room for it, is well-formed and has the table's index bits as its variables.
  2  `foldl_bits_le`; **`Low kRow len v`**: the weight is well-formed, has kRow variables, and every
     index at which it can be other than 0 has its bits among those of one number below len. It
     reads no factor in front: `low_scale`. **`low_cut`**: the library's `tensorBelow` leaves such a
     weight as it is: by its first short cut. **`weightsB_of_low`**: such weights have the mark.
  3  `choicePairs_get`, `rowBlockBits_aligned`, `low_single`, `low_block`, **`weightsFrom_low`**:
     the weights that the library's `Wf.weightsFrom` makes on a stretch of rows are `Low` at every
     length from the stretch's end on.
  4  **`pendingRow_low`**: so are the row weights of a part's row on the table (`Wf.pendingRow`),
     where every row that a run reads is a row of the matrix. **`rowOf_low`**: the batching's
  `Batt.rowOf` keeps it. 5  `runs_inside`, **`tableRowsOf_low`**, **`layPile_low`**: behind "the
     rows on the table" every row's weights are `Low`, under three tests on public values;
     `admitted_three`: these are parts of "the parameters are admitted", which the first chain asks
     behind the own message's sending, at its own ranges' parameters and matrix's size:
     `layPile_low_admitted`.
     **`batt_low`**: the batching's own text (`K13.batt`) keeps it. `claim_weights`: the third
     chain's start reads the claim's weights as the batching lays them. **`weightsB_rowOf`**: THE
     MARK at the one row.

Limits.
- Step by step, not along the chain: that the batching takes the rows which "the rows on the table"
  laid, and that the claim at the chain's end is the one that the batching laid:
  E2E/KeyMarkJoined.lean.
- The table's bounds (the matrix's row bits at most the table's index bits; these at most 63) are
  premises on public numbers.
- The library's file Johnson/Desc/Key/KeyTensorOk.lean is called: its limits hold here too.


-/
import E2E.KeyDotFits
import Johnson.Desc.Key.KeyTensorOk
import OnBytes.Iop.TensorLaws
import OnBytes.Slice.KeyLeavesTop
import OnBytes.Slice.ProgCodes
import Johnson.Desc.Key.One
import Johnson.Desc.K13.Text
import Johnson.Desc.Third.Law.Keeps

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Own (tensorInOrder)

/-! ## 1 A well-formed vector, laid on a table, is well-formed -/

theorem ok_iff (v : Tensor) : v.ok = true ↔ v.vars ≤ 63 ∧
    (v.denseVars.isEmpty = true ∨ v.first + 2 ^ v.denseVars.length ≤ v.values.size) ∧
    (∀ d ∈ v.denseVars, v.pairs[d]? = some (oneE, oneE)) ∧ distinctNats v.denseVars = true := by
  unfold Tensor.ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, d⟩⟩

theorem distinct_map (f : Nat → Nat) : ∀ l : List Nat,
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → distinctNats l = true →
    distinctNats (l.map f) = true
  | [], _, _ => rfl
  | a :: l, hi, h => by
    have h' : (!l.contains a && distinctNats l) = true := h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h'
    show (!(l.map f).contains (f a) && distinctNats (l.map f)) = true
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, distinct_map f l (fun x hx y hy => hi x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy)) h'.2⟩
    cases hc : (l.map f).contains (f a) with
    | false => rfl
    | true =>
      obtain ⟨b, hb, e⟩ := List.mem_map.1 (List.contains_iff_mem.1 hc)
      have := hi b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e
      subst this
      rw [List.contains_iff_mem.2 hb] at h'
      cases h'.1

/-- A vector with the same written-out values whose written-out variables are renumbered, each with
its pair. -/
theorem ok_of_map (v v' : Tensor) (f : Nat → Nat) (h : v.ok = true) (hv : v'.values = v.values)
    (hf : v'.first = v.first) (hd : v'.denseVars = v.denseVars.map f) (hl : v'.vars ≤ 63)
    (hp : ∀ d ∈ v.denseVars, v'.pairs[f d]? = v.pairs[d]?)
    (hi : ∀ a ∈ v.denseVars, ∀ b ∈ v.denseVars, f a = f b → a = b) : v'.ok = true := by
  obtain ⟨-, h2, h3, h4⟩ := (ok_iff v).1 h
  refine (ok_iff v').2 ⟨hl, ?_, ?_, ?_⟩
  · rw [hd, hv, hf, List.length_map]
    rcases h2 with e | e
    · exact Or.inl (by rw [List.isEmpty_iff] at e ⊢; rw [e]; rfl)
    · exact Or.inr e
  · intro d' hd'
    rw [hd] at hd'
    obtain ⟨d, hdm, rfl⟩ := List.mem_map.1 hd'
    rw [hp d hdm]
    exact h3 d hdm
  · rw [hd]
    exact distinct_map f _ hi h4

/-- **A well-formed vector, laid on a table with room for it, is well-formed and has the table's
index bits as its variables.** -/
theorem onTable_ok (lay : VectorLay) (v : Tensor) (h : v.ok = true) (hv : v.vars ≤ lay.bits)
    (hb : lay.bits ≤ 63) : (lay.onTable v).ok = true ∧ (lay.onTable v).vars = lay.bits := by
  obtain ⟨hin, -⟩ := _root_.Desc.K14.Law.dense_of_ok v h
  have hn : v.pairs.length = v.vars := rfl
  -- the widened vector's pairs
  have hw : (v.insertChoice v.vars (lay.bits - v.vars) 0).pairs =
      v.pairs ++ choicePairs (lay.bits - v.vars) 0 := by
    show v.pairs.take v.vars ++ choicePairs (lay.bits - v.vars) 0 ++ v.pairs.drop v.vars = _
    rw [← hn, List.take_length, List.drop_length, List.append_nil]
  have hwl : (v.insertChoice v.vars (lay.bits - v.vars) 0).pairs.length = lay.bits := by
    rw [hw, List.length_append, choicePairs_length, hn]
    omega
  have hwd : (v.insertChoice v.vars (lay.bits - v.vars) 0).denseVars =
      v.denseVars.map fun d => if v.vars ≤ d then d + (lay.bits - v.vars) else d := rfl
  have hwp : ∀ d ∈ v.denseVars,
      (v.insertChoice v.vars (lay.bits - v.vars) 0).pairs[d]? = v.pairs[d]? := fun d hd => by
    rw [hw, List.getElem?_append_left (by rw [hn]; exact hin d hd)]
  cases hr : lay.rowsHigh with
  | false =>
    have e : lay.onTable v = v.insertChoice v.vars (lay.bits - v.vars) 0 := by
      unfold VectorLay.onTable
      simp [hr]
    rw [e]
    refine ⟨ok_of_map v _ (fun d => if v.vars ≤ d then d + (lay.bits - v.vars) else d) h rfl rfl
      hwd (Nat.le_trans (Nat.le_of_eq hwl) hb) (fun d hd => ?_) (fun a ha b hb' => ?_), hwl⟩
    · dsimp only
      rw [if_neg (Nat.not_le.2 (hin d hd))]
      exact hwp d hd
    · dsimp only
      rw [if_neg (Nat.not_le.2 (hin a ha)), if_neg (Nat.not_le.2 (hin b hb'))]
      exact id
  | true =>
    have hbits : lay.bits = lay.rowBits + lay.placeBits := rfl
    have ep : (lay.onTable v).pairs =
        (v.insertChoice v.vars (lay.bits - v.vars) 0).pairs.drop lay.placeBits ++
          (v.insertChoice v.vars (lay.bits - v.vars) 0).pairs.take lay.placeBits := by
      unfold VectorLay.onTable
      simp only [hr, if_true]
      rfl
    have ed : (lay.onTable v).denseVars = v.denseVars.map fun d =>
        if lay.placeBits ≤ d then d - lay.placeBits else d + lay.rowBits := by
      unfold VectorLay.onTable
      simp only [hr, if_true]
      rw [hwd, List.map_map]
      refine List.map_congr_left fun d hd => ?_
      simp only [Function.comp, if_neg (Nat.not_le.2 (hin d hd))]
    have ev : (lay.onTable v).values = v.values := by
      unfold VectorLay.onTable
      simp [hr, Tensor.rotate, Tensor.insertChoice]
    have ef : (lay.onTable v).first = v.first := by
      unfold VectorLay.onTable
      simp [hr, Tensor.rotate, Tensor.insertChoice]
    have el : (lay.onTable v).vars = lay.bits := by
      show (lay.onTable v).pairs.length = _
      rw [ep, List.length_append, List.length_drop, List.length_take, hwl]
      omega
    refine ⟨ok_of_map v _ _ h ev ef ed (by rw [el]; exact hb) (fun d hd => ?_)
      (fun a ha b hb' => ?_), el⟩
    · have hdl : d < lay.bits := Nat.lt_of_lt_of_le (hin d hd) hv
      rw [ep, ← hwp d hd]
      split
      · rename_i c
        rw [List.getElem?_append_left (by rw [List.length_drop, hwl]; omega), List.getElem?_drop]
        congr 1
        omega
      · rename_i c
        rw [List.getElem?_append_right (by rw [List.length_drop, hwl]; omega), List.length_drop,
          hwl, List.getElem?_take_of_lt (by omega)]
        congr 1
        omega
    · have h1 : a < lay.bits := Nat.lt_of_lt_of_le (hin a ha) hv
      have h2 : b < lay.bits := Nat.lt_of_lt_of_le (hin b hb') hv
      intro e
      split at e <;> split at e <;> omega

/-! ## 2 A weight that lies below a length -/

/-- A sum of powers of two over bits that a number has is at most that number. -/
theorem foldl_bits_le (p : Nat → Bool) (X : Nat) : ∀ count : Nat,
    (∀ t, t < count → p t = true → X.testBit t = true) →
    (List.range count).foldl (fun s t => if p t = true then s + 2 ^ t else s) 0 ≤ X % 2 ^ count
  | 0, _ => Nat.zero_le _
  | c + 1, h => by
    have ih := foldl_bits_le p X c fun t ht => h t (Nat.lt_succ_of_lt ht)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.mod_pow_succ]
    split
    · rename_i hp
      have hb := h c (Nat.lt_succ_self c) hp
      rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
      rw [hb, Nat.mul_one]
      omega
    · omega

/-- **The weight lies below len**: it is well-formed, has kRow variables, and every index at which
it can be other than 0 has its bits among those of one number X below len. It reads no factor in
front.
-/
def Low (kRow len : Nat) (v : Tensor) : Prop :=
  v.ok = true ∧ v.vars = kRow ∧ len ≤ 2 ^ kRow ∧ ∃ X, X < len ∧ ∀ t, t < kRow →
    (v.denseVars.contains (0 + t) || !isZeroE (v.pairs.getD (0 + t) (zeroE, zeroE)).2) = true →
    X.testBit t = true

/-- A factor in front changes nothing of it. -/
theorem low_scale {kRow len : Nat} {v : Tensor} (h : Low kRow len v) (x : E) :
    Low kRow len (v.scale x) := by
  have e1 : (v.scale x).ok = v.ok := by
    unfold Tensor.ok Tensor.scale Tensor.vars
    dsimp only
  have e2 : (v.scale x).vars = v.vars := by
    unfold Tensor.scale Tensor.vars
    dsimp only
  have e3 : (v.scale x).denseVars = v.denseVars := by
    unfold Tensor.scale
    dsimp only
  have e4 : (v.scale x).pairs = v.pairs := by
    unfold Tensor.scale
    dsimp only
  unfold Low at h ⊢
  rw [e1, e2, e3, e4]
  exact h

/-- **The cut leaves such a weight as it is**: by its first short cut. -/
theorem low_cut {kRow len : Nat} {v : Tensor} (h : Low kRow len v) :
    tensorBelow v 0 kRow len = some [v] := by
  obtain ⟨-, hv, hl, X, hX, hb⟩ := h
  have hm := foldl_bits_le (fun t => v.denseVars.contains (0 + t) ||
    !isZeroE (v.pairs.getD (0 + t) (zeroE, zeroE)).2) X kRow hb
  have hm' : (List.range kRow).foldl (fun s t => if (v.denseVars.contains (0 + t) ||
      !isZeroE (v.pairs.getD (0 + t) (zeroE, zeroE)).2) = true then s + 2 ^ t else s) 0 < len :=
    Nat.lt_of_le_of_lt (Nat.le_trans hm (Nat.mod_le _ _)) hX
  unfold tensorBelow
  dsimp only
  rw [if_neg (by
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    omega)]
  rw [if_pos hm']
  split <;> rfl

/-- **Such weights have the mark.** -/
theorem weightsB_of_low (S : LinShape) (lay : VectorLay) (g : List Tensor)
    (h : ∀ v ∈ g, Low S.kRow S.matrixRows v) (h2 : S.kRow ≤ lay.bits) (h3 : lay.bits ≤ 63) :
    weightsB S lay g = true := by
  refine List.all_eq_true.2 fun v hv => ?_
  have c := low_cut (h v hv)
  obtain ⟨a, b, -⟩ := h v hv
  obtain ⟨o1, o2⟩ := onTable_ok lay v a (by rw [b]; exact h2) h3
  rw [VerifiableInference.Desc.Own.tensorInOrder_agrees] at o1
  rw [a, c, beq_iff_eq.2 b]
  simp only [Bool.and_self, List.all_cons, List.all_nil, o1, o2, beq_self_eq_true]

/-! ## 3 The weights on a stretch of rows lie below its end -/

/-- The pairs that pick a number's bits, one by one. -/
theorem choicePairs_get : ∀ (n u i : Nat), i < n →
    (choicePairs n u)[i]? = some (if u.testBit i then (zeroE, oneE) else (oneE, zeroE))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, u, 0, _ => by
    show some (if u % 2 == 1 then (zeroE, oneE) else (oneE, zeroE)) = _
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one u with e | e <;> simp [e]
  | n + 1, u, i + 1, h => by
    show (choicePairs n (u / 2))[i]? = _
    rw [choicePairs_get n (u / 2) i (Nat.lt_of_succ_lt_succ h), Nat.testBit_succ]

/-- The largest aligned stretch begins at a multiple of its length. -/
theorem rowBlockBits_aligned (kRow start stop : Nat) : ∀ (fuel d : Nat), start % 2 ^ d = 0 →
    start % 2 ^ Wf.rowBlockBits kRow start stop fuel d = 0
  | 0, _, h => h
  | fuel + 1, d, h => by
    unfold Wf.rowBlockBits
    split
    · rename_i c
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at c
      exact rowBlockBits_aligned kRow start stop fuel (d + 1) c.1.2
    · exact h

/-- The weight on one row. -/
theorem low_single (s : E) (kRow start len : Nat) (h63 : kRow ≤ 63) (hs : start < len)
    (hl : len ≤ 2 ^ kRow) :
    Low kRow len (({ scalar := s } : Tensor).insertChoice 0 kRow start) := by
  have hp : (({ scalar := s } : Tensor).insertChoice 0 kRow start).pairs =
      choicePairs kRow start := by
    simp [Tensor.insertChoice]
  refine ⟨VerifiableInference.Desc.Key.ok_choice s kRow start h63, ?_, hl, start, hs,
    fun t ht hb => ?_⟩
  · show (({ scalar := s } : Tensor).insertChoice 0 kRow start).pairs.length = kRow
    rw [hp, choicePairs_length]
  · have hd : (({ scalar := s } : Tensor).insertChoice 0 kRow start).denseVars = [] := rfl
    rw [hd, hp, Nat.zero_add, List.getD_eq_getElem?_getD, choicePairs_get kRow start t ht] at hb
    cases c : start.testBit t with
    | true => rfl
    | false =>
      rw [c] at hb
      cases hb

/-- The weight on an aligned stretch of 2 ^ d rows. -/
theorem low_block (s : E) (kRow d u len : Nat) (values : Array E) (first : Nat) (h63 : kRow ≤ 63)
    (hd : d ≤ kRow) (hv : first + 2 ^ d ≤ values.size) (hs : 2 ^ d * u + (2 ^ d - 1) < len)
    (hl : len ≤ 2 ^ kRow) :
    Low kRow len (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d)
      u).setValues values first) := by
  have hp : (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d) u).setValues
      values first).pairs = List.replicate d (oneE, oneE) ++ choicePairs (kRow - d) u := by
    simp [Tensor.setValues, Tensor.insertChoice, Tensor.pushDense]
  have hdv : ∀ y ∈ (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d)
      u).setValues values first).denseVars, y < d := by
    intro y hy
    have hy' : y ∈ (([] ++ (List.range d).map (· + ({ scalar := s } : Tensor).vars)).map
        fun x => if d ≤ x then x + (kRow - d) else x) := hy
    rw [List.nil_append, List.map_map] at hy'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy'
    have hx' : x < d := List.mem_range.1 hx
    show (if d ≤ x + 0 then x + 0 + (kRow - d) else x + 0) < d
    rw [if_neg (by omega)]
    omega
  have h2 : 2 ^ d - 1 < 2 ^ d := Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos
  refine ⟨VerifiableInference.Desc.Key.ok_block s kRow d u values first h63 hd hv, ?_, hl,
    2 ^ d * u + (2 ^ d - 1), hs, fun t ht hb => ?_⟩
  · show (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d) u).setValues values
      first).pairs.length = kRow
    rw [hp, List.length_append, List.length_replicate, choicePairs_length]
    omega
  · rw [Nat.testBit_two_pow_mul_add u h2 t]
    split
    · rename_i c
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true c
    · rename_i c
      have hno : (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d)
          u).setValues values first).denseVars.contains (0 + t) = false := by
        cases hc : (((({ scalar := s } : Tensor).pushDense d).insertChoice d (kRow - d)
          u).setValues values first).denseVars.contains (0 + t) with
        | false => rfl
        | true =>
          have := hdv _ (List.contains_iff_mem.1 hc)
          omega
      rw [hno, Bool.false_or, hp, Nat.zero_add, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [List.length_replicate]; omega), List.length_replicate,
        choicePairs_get (kRow - d) u (t - d) (by omega)] at hb
      cases e : u.testBit (t - d) with
      | true => rfl
      | false =>
        rw [e] at hb
        cases hb

/-- **The weights on a stretch of rows lie below every length from its end on.** -/
theorem weightsFrom_low (kRow : Nat) (values : Array E) (scale : E) (stop len : Nat)
    (h63 : kRow ≤ 63) (hs : stop ≤ len) (hl : len ≤ 2 ^ kRow) : ∀ (fuel start first : Nat),
    first + (stop - start) ≤ values.size →
    ∀ t ∈ Wf.weightsFrom kRow values scale stop fuel start first, Low kRow len t
  | 0, _, _, _, t, ht => by
    unfold Wf.weightsFrom at ht
    cases ht
  | fuel + 1, start, first, hsz, t, ht => by
    unfold Wf.weightsFrom at ht
    split at ht
    · rename_i hlt
      have hfit : start + 2 ^ Wf.rowBlockBits kRow start stop kRow 0 ≤ stop :=
        VerifiableInference.Desc.Key.rowBlockBits_fits kRow start stop kRow 0 (by simpa using hlt)
      have hle : Wf.rowBlockBits kRow start stop kRow 0 ≤ kRow :=
        VerifiableInference.Desc.Key.rowBlockBits_le kRow start stop kRow 0 (Nat.zero_le _)
      have hal : start % 2 ^ Wf.rowBlockBits kRow start stop kRow 0 = 0 :=
        rowBlockBits_aligned kRow start stop kRow 0 (by rw [Nat.pow_zero, Nat.mod_one])
      rcases List.mem_cons.1 ht with e | ht'
      · subst e
        split
        · exact low_single _ kRow start len h63 (by omega) hl
        · refine low_block scale kRow _ _ len values first h63 hle (by omega) ?_ hl
          rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hal)]
          have := Nat.two_pow_pos (Wf.rowBlockBits kRow start stop kRow 0)
          omega
      · exact weightsFrom_low kRow values scale stop len h63 hs hl fuel _ _ (by omega) t ht'
    · cases ht

/-! ## 4 The rows on the table, and the one row behind the batching -/

/-- **The row weights of a part's row on the table lie below the matrix's rows**, where every row
that a run reads is a row of the matrix. -/
theorem pendingRow_low (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (c : Lkp.Keys) (e : Array E)
    (h63 : m.kRow ≤ 63) (hl : m.rows ≤ 2 ^ m.kRow)
    (hr : ∀ r ∈ p.runs, r.firstPlace + r.places ≤ e.size)
    (hm : ∀ r ∈ p.runs, ∀ q, q < l.digitWeight.length →
      r.firstRow + q * r.stride + r.places ≤ m.rows) :
    ∀ t ∈ (Wf.pendingRow m l p c e).g, Low m.kRow m.rows t := by
  intro t ht
  unfold Wf.pendingRow at ht
  obtain ⟨r, hrm, ht⟩ := List.mem_flatMap.1 ht
  obtain ⟨w, hw, ht⟩ := List.mem_flatMap.1 ht
  unfold Wf.weightsOnRows at ht
  have hq : w.2 < l.digitWeight.length := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hw
    rw [List.getElem?_zipIdx] at hi
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hi
    have := (List.getElem?_eq_some_iff.1 ha).1
    show 0 + i < _
    omega
  exact weightsFrom_low m.kRow e (ofF w.1) _ m.rows h63 (hm r hrm w.2 hq) hl r.places _
    r.firstPlace (by have := hr r hrm; omega) t ht

/-- **The batching keeps it**: the one row's weights are the rows' weights, each with a factor in
front. -/
theorem rowOf_low {kRow len : Nat} (rows : List TensorRow) (o : Psc.Out)
    (h : ∀ r ∈ rows, ∀ t ∈ r.g, Low kRow len t) : ∀ t ∈ (Batt.rowOf rows o).g, Low kRow len t := by
  intro t ht
  obtain ⟨p, hp, ht⟩ := List.mem_flatMap.1 (show t ∈ (zipT rows o.rowMaps).flatMap fun p =>
    p.1.g.map fun t => t.scale p.2 from ht)
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ht
  rw [zipT_eq] at hp
  exact low_scale (h p.1 (List.of_mem_zip hp).1 v hv) p.2

/-! ## 5 At the key file's first chain -/

theorem runs_inside (lp : Nat) : ∀ (rs : List WfRun) (u : Nat), Wf.runsOk lp u rs = true →
    ∀ r ∈ rs, r.firstPlace + r.places ≤ 2 ^ lp
  | [], _, _, r, hr => by cases hr
  | a :: rs, u, h, r, hr => by
    obtain ⟨-, -, h3, h4⟩ := Slice.Leaves.runsOk_cons h
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h3
    · exact runs_inside lp rs _ h4 r hr

/-- **The rows on the table of one lookup**: their row weights lie below the matrix's rows, where
three tests on public values pass (`admitted_three` says where the first chain asks them). -/
theorem tableRowsOf_low (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys)
    (rows : List TensorRow) (h : VerifiableInference.Desc.Key.tableRowsOf m l keys = some rows)
    (hm : m.ok = true) (hf : Wf.fitsMatrix m l = true) (hl : Wf.lookupOk Wf.fBits l = true) :
    ∀ r ∈ rows, ∀ t ∈ r.g, Low m.kRow m.rows t := by
  simp only [Wf.Matrix.ok, Bool.and_eq_true, decide_eq_true_eq] at hm
  unfold VerifiableInference.Desc.Key.tableRowsOf at h
  split at h
  · intro r hr
    obtain ⟨x, hx, e⟩ := mapM_mem _ _ rows h r hr
    rw [zipT_eq] at hx
    have hp : x.1 ∈ l.parts := (List.of_mem_zip hx).1
    dsimp only at e
    split at e
    · rename_i c
      simp only [Bool.and_eq_true, beq_iff_eq] at c
      obtain rfl := Option.some.inj e
      refine pendingRow_low m l x.1 x.2 _ (by omega) (Slice.le_two_pow_ceilLog2 m.rows)
        (fun a ha => ?_) fun a ha q hq => ?_
      · unfold Wf.eqPlaces
        rw [OnBytes.Slice.size_eqTable, List.length_drop, c.1.1, Nat.add_sub_cancel_left]
        exact runs_inside _ _ 0 (Slice.Leaves.runsOk_of hl hp) a ha
      · obtain ⟨h1, h2, h3⟩ := Slice.Leaves.partsFit_mem m l l.parts 0 hf x.1 hp a ha
        have := Nat.mul_le_mul_right a.stride (by omega : q ≤ l.digitWeight.length - 1)
        omega
    · cases e
  · cases h

/-- **"The rows on the table"**: behind that step every row's weights lie below the matrix's rows.
-/
theorem layPile_low {β : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime)
    (s s' : VerifiableInference.Desc.Key.ChainState β)
    (h : VerifiableInference.Desc.Key.layPile keysOf one s = .ok s')
    (hm : (Wf.matrixOf one.lin).ok = true)
    (hl : ∀ l ∈ one.ranges.lookups, Wf.fitsMatrix (Wf.matrixOf one.lin) l = true ∧
      Wf.lookupOk Wf.fBits l = true) :
    ∀ r ∈ s'.pile, ∀ t ∈ r.g, Low one.lin.kRow one.lin.matrixRows t := by
  unfold VerifiableInference.Desc.Key.layPile at h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨rows, hr, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain rfl := Except.ok.inj h
  intro r hrm
  obtain ⟨L, hL, hrL⟩ := List.mem_flatten.1 (show r ∈ rows.flatten from hrm)
  obtain ⟨x, hx, e⟩ := mapM_mem _ _ rows (VerifiableInference.Desc.Third.Law.some_of_named hr) L hL
  rw [zipT_eq] at hx
  obtain ⟨a, b⟩ := hl x.1 (List.of_mem_zip hx).1
  exact tableRowsOf_low (Wf.matrixOf one.lin) x.1 x.2 L e hm a b r hrL

/-- The three tests are parts of the test "the parameters are admitted", which the first chain asks
behind the own message's sending (`openRangesGroup`, Johnson/Desc/Key/One.lean). -/
theorem admitted_three (codes : Codes) (x : WfPublic) (m : Wf.Matrix)
    (h : Wf.admitted codes x m = true) : m.ok = true ∧
      ∀ l ∈ x.lookups, Wf.fitsMatrix m l = true ∧ Wf.lookupOk Wf.fBits l = true := by
  unfold Wf.admitted at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hm⟩, hf⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  unfold Wf.publicOk at hp
  simp only [Bool.and_eq_true] at hp
  exact ⟨hm, fun l hl => ⟨List.all_eq_true.1 hf l hl, List.all_eq_true.1 hp.2 l hl⟩⟩

/-- "The rows on the table", under the very test that the first chain asks behind the own message's
sending: at the chain's own ranges' parameters and matrix's size. -/
theorem layPile_low_admitted {β : Type} (keysOf : β → List (List Lkp.Keys)) (one : OneTime)
    (s s' : VerifiableInference.Desc.Key.ChainState β)
    (h : VerifiableInference.Desc.Key.layPile keysOf one s = .ok s') (codes : Codes)
    (ha : Wf.admitted codes one.ranges (Wf.matrixOf one.lin) = true) :
    ∀ r ∈ s'.pile, ∀ t ∈ r.g, Low one.lin.kRow one.lin.matrixRows t :=
  layPile_low keysOf one s s' h (admitted_three _ _ _ ha).1 (admitted_three _ _ _ ha).2

/-- **The batching's own text keeps it**: the row that it returns is `Batt.rowOf` of the rows on the
table. -/
theorem batt_low {kRow len : Nat} (owed : Johnson.Desc.First.ForkGround.RowsOwed) (kCol n : Nat)
    (pile : List TensorRow) (ledger : Nat) (d : VerifiableInference.Desc.K13.St)
    (rs : List Fmt.RoundView) (y : TensorRow × VerifiableInference.Desc.K13.St)
    (h : VerifiableInference.Desc.K13.batt owed kCol n pile ledger d rs = .ok y)
    (hp : ∀ r ∈ pile, ∀ t ∈ r.g, Low kRow len t) : ∀ t ∈ y.1.g, Low kRow len t := by
  unfold VerifiableInference.Desc.K13.batt at h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
  cases rs with
  | nil => cases h
  | cons r rs' =>
    dsimp only at h
    obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
    obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
    obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
    obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
    obtain ⟨o, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
    obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Third.Law.ok_of_bind h
    obtain rfl := Except.ok.inj h
    exact rowOf_low pile o hp

/-- The third chain's start reads the claim's row weights as they are laid. -/
theorem claim_weights (row : TensorRow) :
    (VerifiableInference.Desc.Key.rowOfLinClaim (memberClaim row)).g = row.g := rfl

/-- **THE MARK AT THE REAL WEIGHTS**: the one row that the batching hands on, made of rows on the
table whose weights lie below the matrix's rows, has the mark on its row weights. -/
theorem weightsB_rowOf (S : LinShape) (lay : VectorLay) (pile : List TensorRow) (o : Psc.Out)
    (h : ∀ r ∈ pile, ∀ t ∈ r.g, Low S.kRow S.matrixRows t) (h2 : S.kRow ≤ lay.bits)
    (h3 : lay.bits ≤ 63) : weightsB S lay (Batt.rowOf pile o).g = true :=
  weightsB_of_low S lay _ (rowOf_low pile o h) h2 h3

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.ok_iff
#print axioms AtPublicFiles.AtFiles.distinct_map
#print axioms AtPublicFiles.AtFiles.ok_of_map
#print axioms AtPublicFiles.AtFiles.onTable_ok
#print axioms AtPublicFiles.AtFiles.foldl_bits_le
#print axioms AtPublicFiles.AtFiles.low_scale
#print axioms AtPublicFiles.AtFiles.low_cut
#print axioms AtPublicFiles.AtFiles.weightsB_of_low
#print axioms AtPublicFiles.AtFiles.choicePairs_get
#print axioms AtPublicFiles.AtFiles.rowBlockBits_aligned
#print axioms AtPublicFiles.AtFiles.low_single
#print axioms AtPublicFiles.AtFiles.low_block
#print axioms AtPublicFiles.AtFiles.weightsFrom_low
#print axioms AtPublicFiles.AtFiles.pendingRow_low
#print axioms AtPublicFiles.AtFiles.rowOf_low
#print axioms AtPublicFiles.AtFiles.runs_inside
#print axioms AtPublicFiles.AtFiles.tableRowsOf_low
#print axioms AtPublicFiles.AtFiles.layPile_low
#print axioms AtPublicFiles.AtFiles.admitted_three
#print axioms AtPublicFiles.AtFiles.layPile_low_admitted
#print axioms AtPublicFiles.AtFiles.batt_low
#print axioms AtPublicFiles.AtFiles.claim_weights
#print axioms AtPublicFiles.AtFiles.weightsB_rowOf
