-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkLeavesRead.lean: the program's rewriting of a claim on the leaves of a key tree,
read in the field.

`Lkp.keysOf` (OnBytes/Iop/Lkp.lean) and the sums of OnBytes/Iop/Wf.lean compute on elements of three
machine words. OnBytes/Slice/KeyLeaves.lean has the same functions on lists over the field. This
file compares them: each function of the program, read in the field (readE,
OnBytes/Slice/ProgField.lean), is the function over the field at the arguments read in the field.

Main definitions: `accOf`, `readKeys`.
Main theorems: `read_eqWeight`, `read_eqIndex`, `read_eqTable`, `read_pick`, `read_cubeWeight`,
`read_takeOut`, `read_keysOf`, `read_eqPlaces`, `read_sumSlice`, `read_coveredSum`.

Not claimed. Nothing on the weights on the keys that `Lkp.keysOf` also returns. Nothing on a run on
a view, on soundness or on hiding. readE is not injective, so no statement here leads from the field
back to the program's words.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyLeaves
import OnBytes.Slice.BlkPscRead
import OnBytes.Slice.ProgMle

set_option autoImplicit false

namespace OnBytes.Slice.Leaves
open Prob Cb
open OnBytes.Params (WfRun WfPart WfLookup)

/-! ## The equality vector -/

/-- The loop of the equality vector's entry, from any running value. -/
theorem read_eqWeight : ∀ (z : List E) (j : ℕ) (r : E),
    readE (eqWeight z j r) = readE r * eqW (z.map readE) j
  | [], _, r => (mul_one (readE r)).symm
  | x :: xs, j, r => by
    rw [congrFun (congrFun (eqWeight_cons_fun x xs) j) r, read_eqWeight xs, readE_mul,
      List.map_cons, eqW, mul_assoc]
    congr 2
    by_cases h : j % 2 = 1
    · rw [if_pos (beq_iff_eq.2 h), if_pos h]
    · rw [if_neg fun hb => h (beq_iff_eq.1 hb), if_neg h, readE_sub, readE_one]

/-- The equality vector's entry. -/
theorem read_eqIndex (z : List E) (j : ℕ) : readE (eqIndex z j) = eqW (z.map readE) j := by
  unfold eqIndex
  rw [read_eqWeight, readE_one, one_mul]

/-- The difference of two lists, entry by entry. -/
theorem map_zipWith_sub : ∀ a b : List E,
    (List.zipWith subE a b).map readE = List.zipWith (· - ·) (a.map readE) (b.map readE)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by
    simp only [List.zipWith_cons_cons, List.map_cons, readE_sub, map_zipWith_sub a b]

/-- The loop of the written-out table of corners, from any table. -/
theorem read_eqTableLoop : ∀ (z : List E) (out : Array E),
    (z.foldl (fun (out : Array E) x =>
      let hi := out.map fun w => mulE w x
      (Array.zipWith subE out hi) ++ hi) out).toList.map readE =
    (z.map readE).foldl (fun out x =>
      let hi := out.map fun w => w * x
      List.zipWith (· - ·) out hi ++ hi) (out.toList.map readE)
  | [], _ => rfl
  | x :: xs, out => by
    rw [List.foldl_cons, read_eqTableLoop xs, List.map_cons, List.foldl_cons]
    congr 1
    simp only [Array.toList_append, Array.toList_zipWith, Array.toList_map, List.map_append,
      map_zipWith_sub, List.map_map]
    have e : (readE ∘ fun w => mulE w x) = (fun w => w * readE x) ∘ readE := by
      funext w
      exact readE_mul w x
    rw [e]

/-- The written-out table of corners. -/
theorem read_eqTable (z : List E) : (eqTable z).toList.map readE = eqTableF (z.map readE) := by
  unfold eqTable eqTableF
  rw [read_eqTableLoop]
  simp [readE_one]

/-- The equality vector of a point's place coordinates, written out. -/
theorem read_eqPlaces (m : Wf.Matrix) (point : List E) :
    (Wf.eqPlaces m point).toList.map readE = eqPlacesF m.kCol (point.map readE) := by
  unfold Wf.eqPlaces eqPlacesF
  rw [read_eqTable, List.map_drop]

/-! ## A cube's weight -/

/-- x or 1 - x. -/
theorem read_pick (b : Bool) (x : E) : readE (Lkp.pick b x) = pickF b (readE x) := by
  unfold Lkp.pick pickF
  cases b
  · simp [readE_sub, readE_one]
  · simp

/-- The loop of a cube's weight, from any running value. -/
theorem read_cubeLoop (c : Lkp.Cube) : ∀ (l : List (ℕ × E)) (w : E),
    readE (l.foldl (fun w p =>
      if c.mask.testBit p.1 then mulE w (Lkp.pick (c.value.testBit p.1) p.2) else w) w) =
    (l.map fun p => (p.1, readE p.2)).foldl (fun w p =>
      if c.mask.testBit p.1 then w * pickF (c.value.testBit p.1) p.2 else w) (readE w)
  | [], _ => rfl
  | p :: l, w => by
    rw [List.foldl_cons, read_cubeLoop c l, List.map_cons, List.foldl_cons]
    congr 1
    by_cases h : c.mask.testBit p.1 = true
    · simp only [h, if_true, readE_mul, read_pick]
    · simp only [h, Bool.false_eq_true, if_false]

/-- A cube's weight. -/
theorem read_cubeWeight (c : Lkp.Cube) (z : List E) :
    readE (Lkp.cubeWeight c z) = cubeWeightF c (z.map readE) := by
  unfold Lkp.cubeWeight cubeWeightF
  rw [read_cubeLoop, readE_one, List.length_map, zip_read_right]

/-! ## The claim on the keys -/

/-- What the making of a claim on the keys carries along, read; its weights are left out. -/
def accOf (a : Lkp.KeyAcc) : KeyAccF := ⟨readE a.target, a.real.map readE⟩

/-- One cube is taken out of a claim on the keys. -/
theorem read_takeOut (S : Lkp.Public) (θ : E) (point : List E) (a : Lkp.KeyAcc) (cube : Lkp.Cube)
    (row : ℕ) (block : Option ℕ) :
    accOf (Lkp.takeOut S θ point a cube row block) =
      takeOutF (fun t => readE (Lkp.rowAt S θ t)) (point.map readE) (accOf a) cube row block := by
  unfold Lkp.takeOut takeOutF accOf
  cases block with
  | none => simp only [readE_sub, readE_mul, read_cubeWeight]
  | some b =>
    simp only [readE_sub, readE_mul, read_cubeWeight, List.map_set, KeyAccF.mk.injEq, true_and]
    congr 2
    by_cases h : b < a.real.length
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact h),
        List.getElem_map]
    · rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by rw [List.length_map]; omega), readE_zero]

/-- A claim on one part of the keys, read; its weights are left out. -/
def readKeys (k : Lkp.Keys) : KeysF := ⟨k.point.map readE, readForm k.masks, readE k.target⟩

/-- A mask form times -1. -/
theorem read_scaleNeg (m : MaskForm) :
    readForm (Psc.scaleForm (negE oneE) m) = PscF.scaleForm (-1) (readForm m) := by
  unfold readForm Psc.scaleForm PscF.scaleForm
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  show (t.1, readE (mulE (negE oneE) t.2)) = (t.1, -1 * readE t.2)
  rw [readE_mul, readE_neg, readE_one]

/-- The program's rewriting of a claim on the leaves, read. The rows of the table and numbers as
elements are the program's, read. -/
theorem read_keysOf (S : Lkp.Public) (θ α : E) (part : ℕ) (c : PointClaim) :
    readKeys (Lkp.keysOf S θ α part c) =
      keysOfF S (fun t => readE (Lkp.rowAt S θ t)) (fun n => readE (Lkp.natE n)) (readE θ)
        (readE α) part (readPC c) := by
  unfold Lkp.keysOf keysOfF readKeys
  simp only [KeysF.mk.injEq]
  refine ⟨rfl, read_scaleNeg c.masks, ?_⟩
  -- the state before the loops
  have h0 : accOf
      { target := subE α c.value
        weights := Form.ofTensor (Tensor.eq c.point)
        real := S.keys.map fun b =>
          if b.function.isNone then zeroE else Lkp.cubeWeight (Lkp.cubeOfBlock S b) c.point } =
      { target := readE α - (readPC c).value
        real := S.keys.map fun b =>
          if b.function.isNone then 0
          else cubeWeightF (Lkp.cubeOfBlock S b) (readPC c).point } := by
    unfold accOf
    simp only [readE_sub, List.map_map, KeyAccF.mk.injEq]
    refine ⟨rfl, List.map_congr_left fun b _ => ?_⟩
    show readE (if b.function.isNone then zeroE else _) = _
    by_cases hb : b.function.isNone = true
    · simp only [hb, if_true, readE_zero]
    · simp only [hb, Bool.false_eq_true, if_false]
      exact read_cubeWeight _ _
  rw [← h0]
  have hlen : (readPC c).point.length = c.point.length := List.length_map _
  rw [hlen]
  -- the two loops
  rw [List.foldl_hom accOf (g₁ := fun a b =>
      Lkp.takeOut S θ c.point a (Lkp.cubeOfBlock S b) b.paddingRow none)
    (H := fun a b => (read_takeOut S θ c.point a _ _ none).symm)]
  rw [List.foldl_hom accOf (g₁ := fun a p =>
      (Lkp.cubesOf p c.point.length).foldl (fun a x => Lkp.takeOut S θ c.point a x p.row
        (some (S.keys.findIdx fun k => k.holds S.g p.first))) a)
    (H := fun a p => by
      rw [List.foldl_hom accOf (g₁ := fun a x => Lkp.takeOut S θ c.point a x p.row
          (some (S.keys.findIdx fun k => k.holds S.g p.first)))
        (H := fun a x => (read_takeOut S θ c.point a _ _ _).symm)])]
  -- the last loop
  generalize (List.foldl (fun a p =>
      (Lkp.cubesOf p c.point.length).foldl (fun a x => Lkp.takeOut S θ c.point a x p.row
        (some (S.keys.findIdx fun k => k.holds S.g p.first))) a) _ _) = a2
  show _ = List.foldl _ (readE a2.target) (S.keys.zip (a2.real.map readE))
  rw [zip_read_right, List.foldl_map]
  refine (List.foldl_hom readE (H := fun t q => ?_)).symm
  cases hq : q.1.function with
  | none => rfl
  | some n =>
    simp only []
    by_cases hn : (n == 0) = true
    · simp only [hn, if_true]
    · simp only [hn, Bool.false_eq_true, if_false, readE_sub, readE_mul]

/-! ## The two sums -/

/-- A running sum, from any value. -/
theorem read_foldl_add : ∀ (l : List E) (r : E),
    readE (l.foldl addE r) = readE r + (l.map readE).sum
  | [], r => by simp
  | x :: l, r => by
    rw [List.foldl_cons, read_foldl_add l, readE_add, List.map_cons, List.sum_cons, add_assoc]

/-- The sum of a stretch of a written-out vector. -/
theorem read_sumSlice (values : Array E) (first count : ℕ) :
    readE (Wf.sumSlice values first count) = sumSliceF (values.toList.map readE) first count := by
  unfold Wf.sumSlice sumSliceF
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, read_foldl_add, readE_zero, zero_add,
    Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left, List.map_take,
    List.map_drop]

/-- The sum of a written-out vector over the covered places. -/
theorem read_coveredSum (p : WfPart) (e : Array E) :
    readE (Wf.coveredSum p e) = coveredSumF p.runs (e.toList.map readE) := by
  unfold Wf.coveredSum coveredSumF
  rw [← readE_zero]
  refine (List.foldl_hom readE (H := fun s r => ?_)).symm
  rw [readE_add, read_sumSlice]

end OnBytes.Slice.Leaves
