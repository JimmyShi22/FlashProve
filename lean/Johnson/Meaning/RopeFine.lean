-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopeFine.lean: the test rowOK of Johnson/Meaning/RopeData.lean in finer pieces: 128
tokens a piece in the place of a pair's 1024. Definitions, and that eight pieces make a row.

Why. By measurement the memory of such an evaluation in Lean's kernel grows with the number of
steps: a pair's 1024 tokens take 3.5 GB of the process's own memory, 128 tokens below 1 GB.
  turnAt r m c s: the rotation after m more tokens. turnAt_add: it composes.
  tokList_add: the list of m + n tokens is the list of m tokens, then that of n tokens from the
    rotation after m. tokList_blocks: so the list of k n tokens is k lists of n tokens.
  range_blocks: the like for a list made over List.range.
  partOf, dataPart, partOK i q: the recursion's words, the stored words, and the test, for the 128
    tokens from 128 q on of pair i.
  rowOK_of_parts: if partOK i q holds for q = 0, ..., 7, rowOK i holds.
Nothing is evaluated here.
-/
import Johnson.Meaning.RopeData

set_option autoImplicit false

namespace Meaning.Rope

open OnBytes.Model.Layer (fxOne roundD cosSin turn)
open Inst.Model (dec)

/-- The rotation after m more tokens. -/
def turnAt (r : Int × Int) : Nat → Int → Int → Int × Int
  | 0, c, s => (c, s)
  | m + 1, c, s => turnAt r m (turn c s r).1 (turn c s r).2

theorem turnAt_add (r : Int × Int) : ∀ (m n : Nat) (c s : Int),
    turnAt r (m + n) c s = turnAt r n (turnAt r m c s).1 (turnAt r m c s).2
  | 0, n, c, s => by rw [Nat.zero_add]; rfl
  | m + 1, n, c, s => by
    have e : m + 1 + n = (m + n) + 1 := by omega
    rw [e]
    exact turnAt_add r m n (turn c s r).1 (turn c s r).2

/-- The list of m + n tokens. -/
theorem tokList_add (cs : Nat) (p : Nat × Nat) (pf : Nat) (r : Int × Int) :
    ∀ (m n t : Nat) (c s : Int),
      tokList cs p pf r (m + n) t c s =
        tokList cs p pf r m t c s ++
          tokList cs p pf r n (t + m) (turnAt r m c s).1 (turnAt r m c s).2
  | 0, n, t, c, s => by rw [Nat.zero_add]; rfl
  | m + 1, n, t, c, s => by
    have e : m + 1 + n = (m + n) + 1 := by omega
    have e2 : t + (m + 1) = t + 1 + m := by omega
    rw [e, e2]
    show _ :: tokList cs p pf r (m + n) (t + 1) (turn c s r).1 (turn c s r).2 =
      (_ :: tokList cs p pf r m (t + 1) (turn c s r).1 (turn c s r).2) ++ _
    rw [tokList_add cs p pf r m n (t + 1) (turn c s r).1 (turn c s r).2]
    rfl

/-- The list of k n tokens is k lists of n tokens. -/
theorem tokList_blocks (cs : Nat) (p : Nat × Nat) (pf : Nat) (r : Int × Int) (n : Nat) :
    ∀ (k t : Nat) (c s : Int),
      tokList cs p pf r (k * n) t c s =
        (List.range k).flatMap fun q =>
          tokList cs p pf r n (t + q * n) (turnAt r (q * n) c s).1 (turnAt r (q * n) c s).2
  | 0, t, c, s => by rw [Nat.zero_mul]; rfl
  | k + 1, t, c, s => by
    have e : (k + 1) * n = n + k * n := by rw [Nat.succ_mul]; omega
    rw [e, tokList_add, tokList_blocks cs p pf r n k (t + n), List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    congr 1
    · rw [Nat.zero_mul, Nat.add_zero]
      rfl
    · refine List.flatMap_congr fun q _ => ?_
      have e3 : (q + 1) * n = n + q * n := by rw [Nat.succ_mul]; omega
      have e4 : t + n + q * n = t + (q + 1) * n := by omega
      show tokList cs p pf r n (t + n + q * n) _ _ = tokList cs p pf r n (t + (q + 1) * n) _ _
      rw [e4, e3, turnAt_add]

/-- A list made over the numbers below k n is k lists made over the numbers below n. -/
theorem range_blocks {α : Type} (g : Nat → α) (n : Nat) : ∀ k : Nat,
    (List.range (k * n)).map g =
      (List.range k).flatMap fun q => (List.range n).map fun t => g (q * n + t)
  | 0 => by rw [Nat.zero_mul]; rfl
  | k + 1 => by
    have e : (k + 1) * n = k * n + n := Nat.succ_mul k n
    rw [e, List.range_add, List.map_append, range_blocks g n k, List.range_succ,
      List.flatMap_append, List.map_map]
    simp [Function.comp_def]

/-- The recursion's words for the n tokens from t0 on, from the pair's power x. -/
def partOf (cs n t0 x : Nat) : List (Nat × Nat) :=
  tokList cs (roundD x fxOne) ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2)
    (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) n t0
    (turnAt (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) t0 fxOne 0).1
    (turnAt (cosSin ((roundD x fxOne).1 * fxOne / (roundD x fxOne).2 : Nat)) t0 fxOne 0).2

/-- The library's stored words of pair i for the n tokens from t0 on. -/
def dataPart (i t0 n : Nat) : List (Nat × Nat) :=
  (List.range n).map fun t =>
    (dec Inst.Model.Data.cos 14 (64 * (t0 + t) + i), dec Inst.Model.Data.sin 14 (64 * (t0 + t) + i))

/-- The test on the 128 tokens from 128 q on of pair i. -/
def partOK (i q : Nat) : Bool :=
  decide (partOf 12 128 (q * 128) (xAt (uOf 500000 64) i fxOne) = dataPart i (q * 128) 128) &&
    (dataPart i (q * 128) 128).all fun w => decide (w.1 ≤ 8192) && decide (w.2 ≤ 8192)

/-- A row is its eight parts. -/
theorem rowOf_parts (cs x : Nat) :
    rowOf cs 1024 x = (List.range 8).flatMap fun q => partOf cs 128 (q * 128) x := by
  unfold rowOf
  rw [show (1024 : Nat) = 8 * 128 from rfl, tokList_blocks]
  refine List.flatMap_congr fun q _ => ?_
  unfold partOf
  rw [Nat.zero_add]

theorem dataRow_parts (i : Nat) :
    dataRow i = (List.range 8).flatMap fun q => dataPart i (q * 128) 128 := by
  unfold dataRow
  rw [show (1024 : Nat) = 8 * 128 from rfl, range_blocks]
  rfl

/-- Eight pieces make a row. -/
theorem rowOK_of_parts {i : Nat} (h : ∀ q, q < 8 → partOK i q = true) : rowOK i = true := by
  have h1 : ∀ q, q < 8 →
      partOf 12 128 (q * 128) (xAt (uOf 500000 64) i fxOne) = dataPart i (q * 128) 128 := by
    intro q hq
    have y := h q hq
    unfold partOK at y
    rw [Bool.and_eq_true] at y
    exact of_decide_eq_true y.1
  have h2 : ∀ q, q < 8 → ((dataPart i (q * 128) 128).all fun w =>
      decide (w.1 ≤ 8192) && decide (w.2 ≤ 8192)) = true := by
    intro q hq
    have y := h q hq
    unfold partOK at y
    rw [Bool.and_eq_true] at y
    exact y.2
  unfold rowOK
  rw [Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    rw [rowOf_parts, dataRow_parts]
    exact List.flatMap_congr fun q hq => h1 q (List.mem_range.mp hq)
  · rw [dataRow_parts, List.all_flatMap, List.all_eq_true]
    exact fun q hq => h2 q (List.mem_range.mp hq)

#print axioms tokList_blocks
#print axioms range_blocks
#print axioms rowOK_of_parts

end Meaning.Rope
