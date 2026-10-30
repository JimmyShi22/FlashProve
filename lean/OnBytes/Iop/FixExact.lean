-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/FixExact.lean: `Form.fixLow` and `Form.fixLowPlain` (OnBytes/Iop/Tensor.lean) return the
same value, for every form, point and factor.

`Form.fixLow` folds a written-out slice that several tensors hold only once: it keeps the slices
folded so far in a table (`Std.HashMap`). `Form.fixLowPlain` fixes each tensor by itself.
OnBytes/Iop/FixLaws.lean shows that the two read as the same sum under any reading of E, for tensors
that are in order and have at least as many variables as the point has coordinates. Here they are
shown equal as values, with no condition. Why it is wanted: Lean's kernel does not evaluate a lookup
in such a table, so it does not evaluate `Form.fixLow` at a tensor whose slice is cut;
`Form.fixLowPlain` has no table. Statements with their proofs.
Main names:
  `fold_push_congr`: two loops that push onto an array, whose pushed values agree below the bound.
  `foldBit_index`: the two entries that `foldBit` reads for an index lie within the stretch, if the
    stretch has 2 ^ n entries and the bit's number is below n.
  `foldBit_congr`: so `foldBit` gives one array at two vectors that agree on the stretch.
  `sliceLoop_same`: the loop of `Tensor.foldedSlice`, from two vectors that agree on the slice: the
    two states are equal, or no bit was folded.
  `Tensor.foldedSlice_same`: two tensors with the same key and the same slice, which is cut, have
    the same folded slice.
  `fixLowShared_exact`: one step of the loop of `Form.fixLow`, from a table that is `SlicesOk`
    (OnBytes/Iop/FixLaws.lean): the table stays so, and the tensor added is `Tensor.fixLow`'s.
  `Form.fixLow_eq_plain`: `f.fixLow g times = f.fixLowPlain g times`.
Limits: an equality of two functions of the program. Nothing on what either computes: that is
OnBytes/Iop/FixLaws.lean's. Nothing on time or memory, in which the two differ. That Lean's kernel
evaluates `Form.fixLowPlain` is not claimed: both functions sort the single entries
(`mergeEntries`).

-/
import OnBytes.Iop.FixLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes

/-- Two loops that push onto an array. -/
theorem fold_push_congr {α : Type} (f₁ f₂ : Nat → α) : ∀ (m : Nat) (init : Array α),
    (∀ idx, idx < m → f₁ idx = f₂ idx) →
    Nat.fold m (fun idx _ (out : Array α) => out.push (f₁ idx)) init =
      Nat.fold m (fun idx _ (out : Array α) => out.push (f₂ idx)) init
  | 0, _, _ => rfl
  | m + 1, init, h => by
    rw [Nat.fold_succ, Nat.fold_succ, fold_push_congr f₁ f₂ m init fun idx hi => h idx (by omega),
      h m (by omega)]

/-- The entries that `foldBit` reads lie within the stretch. -/
theorem foldBit_index {n i idx : Nat} (hi : i < n) (h : idx < 2 ^ n / 2) :
    idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i) + 2 ^ i < 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - (i + 1), by omega⟩
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have e : 2 ^ (i + 1 + k) = 2 * 2 ^ i * 2 ^ k := by rw [pow_add, pow_succ]; ring
  rw [e] at h ⊢
  have h' : idx < 2 ^ i * 2 ^ k := by
    have e2 : 2 * 2 ^ i * 2 ^ k / 2 = 2 ^ i * 2 ^ k := by
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [e2] at h
    exact h
  have hq : idx / 2 ^ i < 2 ^ k := Nat.div_lt_of_lt_mul h'
  have hr : idx % 2 ^ i < 2 ^ i := Nat.mod_lt _ hp
  have h2 : 2 * 2 ^ i * (idx / 2 ^ i + 1) ≤ 2 * 2 ^ i * 2 ^ k := Nat.mul_le_mul_left _ hq
  have e3 : 2 * 2 ^ i * (idx / 2 ^ i + 1) = 2 * 2 ^ i * (idx / 2 ^ i) + 2 * 2 ^ i := by ring
  omega

/-- `foldBit` at two vectors that agree on the stretch. -/
theorem foldBit_congr (a b : Array E) (start n i : Nat) (x : E) (hi : i < n)
    (h : ∀ u, u < 2 ^ n → a.getD (start + u) zeroE = b.getD (start + u) zeroE) :
    foldBit a start (2 ^ n) i x = foldBit b start (2 ^ n) i x := by
  unfold foldBit
  dsimp only
  refine fold_push_congr _ _ _ _ fun idx hidx => ?_
  have hb := foldBit_index hi hidx
  have e1 := h (idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i)) (by omega)
  have e2 := h (idx % 2 ^ i + 2 * 2 ^ i * (idx / 2 ^ i) + 2 ^ i) hb
  rw [← Nat.add_assoc] at e1
  rw [← Nat.add_assoc, ← Nat.add_assoc] at e2
  rw [e1, e2]

/-- The step of the loop hangs on the tensor's dense variables alone. -/
theorem sliceStep_congr (v w : Tensor) (g : List E) (h : w.denseVars = v.denseVars) :
    sliceStep w g = sliceStep v g := by
  funext s i
  unfold sliceStep
  rw [h]

/-- The loop of `Tensor.foldedSlice`, from two vectors that agree on the slice. -/
theorem sliceLoop_same (v : Tensor) (g : List E) (a b : Array E) (start n : Nat)
    (h : ∀ u, u < 2 ^ n → a.getD (start + u) zeroE = b.getD (start + u) zeroE) :
    ∀ l : List Nat, (∀ i ∈ l, i < n) →
      l.foldl (sliceStep v g) (a, start, 2 ^ n) = l.foldl (sliceStep v g) (b, start, 2 ^ n) ∨
        ∀ i ∈ l, ∀ d, v.denseVars[i]? = some d → ¬ d < g.length
  | [], _ => Or.inr fun _ hi => absurd hi (List.not_mem_nil)
  | i :: l, hl => by
    have hi : i < n := hl i (List.mem_cons_self)
    rw [List.foldl_cons, List.foldl_cons]
    cases hd : v.denseVars[i]? with
    | none =>
      have e : ∀ s, sliceStep v g s i = s := fun s => by
        unfold sliceStep
        rw [hd]
      rw [e, e]
      refine (sliceLoop_same v g a b start n h l fun j hj => hl j (List.mem_cons_of_mem _ hj)).imp
        id fun hr j hj d hjd => ?_
      rcases List.mem_cons.1 hj with rfl | hj'
      · rw [hd] at hjd
        cases hjd
      · exact hr j hj' d hjd
    | some d₀ =>
      by_cases hc : d₀ < g.length
      · left
        have e : ∀ s : Array E × Nat × Nat, sliceStep v g s i =
            (foldBit s.1 s.2.1 s.2.2 i (g.getD d₀ zeroE), 0, s.2.2 / 2) := fun s => by
          unfold sliceStep
          rw [hd]
          exact if_pos hc
        rw [e, e]
        show l.foldl (sliceStep v g) (foldBit a start (2 ^ n) i (g.getD d₀ zeroE), 0, 2 ^ n / 2) =
          l.foldl (sliceStep v g) (foldBit b start (2 ^ n) i (g.getD d₀ zeroE), 0, 2 ^ n / 2)
        rw [foldBit_congr a b start n i _ hi h]
      · have e : ∀ s, sliceStep v g s i = s := fun s => by
          unfold sliceStep
          rw [hd]
          exact if_neg hc
        rw [e, e]
        refine (sliceLoop_same v g a b start n h l fun j hj =>
          hl j (List.mem_cons_of_mem _ hj)).imp id fun hr j hj d hjd => ?_
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [hd] at hjd
          obtain rfl := Option.some.inj hjd
          exact hc
        · exact hr j hj' d hjd

/-- Two tensors with the same key and the same slice, which is cut, have the same folded slice. -/
theorem Tensor.foldedSlice_same (v w : Tensor) (g : List E) (hk : w.sliceKey = v.sliceKey)
    (hs : v.sameSlice w = true) (hc : v.sliceIsCut g.length = true) :
    w.foldedSlice g = v.foldedSlice g := by
  unfold Tensor.sliceKey at hk
  dsimp only at hk
  have h1 : w.first = v.first := congrArg Prod.fst hk
  have h2 : w.denseVars = v.denseVars := congrArg (fun q => q.2.1) hk
  have hv : ∀ u, u < 2 ^ v.denseVars.length →
      w.values.getD (v.first + u) zeroE = v.values.getD (v.first + u) zeroE := fun u hu => by
    unfold Tensor.sameSlice at hs
    exact (beq_iff_eq.1 (all_below _ (fun i => v.values.getD (v.first + i) zeroE ==
      w.values.getD (v.first + i) zeroE) hs u hu)).symm
  rw [Tensor.foldedSlice_eq, Tensor.foldedSlice_eq, sliceStep_congr v w g h2, h1, h2]
  rcases sliceLoop_same v g w.values v.values v.first v.denseVars.length hv
    (List.range v.denseVars.length).reverse
    (fun i hi => List.mem_range.1 (List.mem_reverse.1 hi)) with e | e
  · rw [e]
  · exfalso
    unfold Tensor.sliceIsCut at hc
    obtain ⟨d, hd, hlt⟩ := List.any_eq_true.1 hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    exact e i (List.mem_reverse.2 (List.mem_range.2 hi)) _ (List.getElem?_eq_getElem hi)
      (of_decide_eq_true hlt)

/-- One step of the loop of `Form.fixLow`, as a value. -/
theorem fixLowShared_exact (g : List E) (s : List Tensor × Form.FoldedSlices) (v : Tensor)
    (hM : SlicesOk g s.2) :
    SlicesOk g (Form.fixLowShared g s v).2 ∧ (Form.fixLowShared g s v).1 = v.fixLow g :: s.1 := by
  unfold Form.fixLowShared Tensor.fixLow
  by_cases hc : v.sliceIsCut g.length = true
  · rw [if_pos hc, if_pos hc]
    dsimp only
    cases hf : s.2[v.sliceKey]? with
    | some c =>
      obtain ⟨k1, k2, -⟩ := hM _ c hf
      refine ⟨hM, ?_⟩
      by_cases hsame : v.sameSlice c.1 = true
      · show v.fixLowWith g (if v.sameSlice c.1 = true then c.2 else v.foldedSlice g) :: s.1 = _
        rw [if_pos hsame, k2, Tensor.foldedSlice_same v c.1 g k1 hsame hc]
      · show v.fixLowWith g (if v.sameSlice c.1 = true then c.2 else v.foldedSlice g) :: s.1 = _
        rw [if_neg hsame]
    | none =>
      refine ⟨?_, rfl⟩
      intro key c hcm
      rw [Std.HashMap.getElem?_insertIfNew] at hcm
      split at hcm
      · rename_i hk
        have ek : v.sliceKey = key := by simpa using hk.1
        have ec : (v, v.foldedSlice g) = c := by simpa using hcm
        rw [← ec]
        exact ⟨ek, rfl, v.dense_of_cut _ hc⟩
      · exact hM key c hcm
  · rw [if_neg hc, if_neg hc]
    exact ⟨hM, rfl⟩

/-- The loop of `Form.fixLow` over the tensors, as a value. -/
theorem fixLow_loop_exact (g : List E) (times : E) :
    ∀ (l : List Tensor) (s : List Tensor × Form.FoldedSlices), SlicesOk g s.2 →
      (l.foldl (fun s v => Form.fixLowShared g s (v.scale times)) s).1 =
        (l.map fun v => (v.scale times).fixLow g).reverse ++ s.1
  | [], _, _ => rfl
  | v :: l, s, hM => by
    obtain ⟨hM', e⟩ := fixLowShared_exact g s (v.scale times) hM
    rw [List.foldl_cons, fixLow_loop_exact g times l _ hM', e, List.map_cons, List.reverse_cons,
      List.append_assoc]
    rfl

/-- **`Form.fixLow` and `Form.fixLowPlain` return the same value.** -/
theorem Form.fixLow_eq_plain (f : Form) (g : List E) (times : E) :
    f.fixLow g times = f.fixLowPlain g times := by
  have h0 : SlicesOk g ({} : Form.FoldedSlices) := by
    intro key c hc
    simp at hc
  unfold Form.fixLow Form.fixLowPlain
  rw [fixLow_loop_exact g times f.tensors ([], {}) h0, List.append_nil, List.reverse_reverse]

end OnBytes

#print axioms OnBytes.foldBit_congr
#print axioms OnBytes.Tensor.foldedSlice_same
#print axioms OnBytes.fixLowShared_exact
#print axioms OnBytes.Form.fixLow_eq_plain
