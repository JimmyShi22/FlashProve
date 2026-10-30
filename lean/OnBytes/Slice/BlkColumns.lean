-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkColumns.lean: the program and the format cut a leaf's column at the same words.

A leaf of a tree holds a column of words: the main symbols of the tree's oracle messages, part by
part, and after them their mask symbols. The program (the Lean verifier in OnBytes/) cuts the
symbols of one oracle message out of the column (OnBytes/Iop/Ground.lean: `Blk.columnOf`). The
format (the verifier of the library's folder Fmt/) puts the whole column on the rows of a stage
(Fmt/M1Types.lean: `stageCol`) or of the first group (Fmt/M2Types.lean: `groupCol`). This file says
of each of the three at which word every symbol begins. So a symbol of the program and an entry of
the format's column are equal as soon as their words' numbers are.

Main definitions: `sym3` (the symbol over the extension field that begins at a given word).
Main theorems.
 `columnOf_size`, `columnOf_main`, `columnOf_mask`   the program's cut.
 `takeE_inv`, `cutCol_inv`, `stageCol_inv`           the format's cut of a later stage's column.
 `cutParts_inv`, `groupCol_inv`, `groupCol_zero`     the format's cut of the first tree's column,
      for two members of equally many main rows over the extension field, no mask rows of their
      own, and one fresh mask row.
 `stage_main`, `stage_mask`, `stage_fresh`, `group_main0`, `group_main1`, `group_fresh`
      the joints: a symbol of the program is the entry of the format's column.
Not claimed. Nothing on main rows over the base field. Nothing on how the program folds the symbols
of a column.
-/
import OnBytes.Slice.ProgCodes
import Fmt.M2Types

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## Three words of a column -/

/-- The symbol over the extension field that begins at word i of a column; words that the column
lacks count as 0. -/
def sym3 (w : List UInt64) (i : ℕ) : Fmt.M1.E := (w.getD i 0, w.getD (i + 1) 0, w.getD (i + 2) 0)

/-- Three words in front move every symbol by three. -/
theorem sym3_cons3 (a b c : UInt64) (w : List UInt64) (k : ℕ) :
    sym3 (a :: b :: c :: w) (k + 3) = sym3 w k := rfl

/-- A symbol of a column without its first m words. -/
theorem sym3_drop (w : List UInt64) (m k : ℕ) : sym3 (w.drop m) k = sym3 w (m + k) := by
  unfold sym3
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

/-- The symbols that the format takes off a list of words, and what it leaves. -/
theorem takeE_inv : ∀ (n : ℕ) (w : List UInt64) (l : List Fmt.M1.E) (w' : List UInt64),
    Fmt.M1.takeE n w = some (l, w') →
    l.length = n ∧ w' = w.drop (3 * n) ∧ ∀ i, i < n → l.getD i Fmt.Fld.zeroE = sym3 w (3 * i)
  | 0, w, l, w', h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, [], l, w', h => by cases h
  | n + 1, [_], l, w', h => by cases h
  | n + 1, [_, _], l, w', h => by cases h
  | n + 1, a :: b :: c :: w, l, w', h => by
    obtain ⟨⟨l0, w0⟩, h0, h1⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    obtain ⟨k1, k2, k3⟩ := takeE_inv n w l0 w0 h0
    refine ⟨congrArg (· + 1) k1, ?_, fun i hi => ?_⟩
    · rw [k2, show 3 * (n + 1) = 3 * n + 3 by ring]
      rfl
    · cases i with
      | zero => rfl
      | succ i =>
        rw [show 3 * (i + 1) = 3 * i + 3 by ring, sym3_cons3]
        exact k3 i (Nat.lt_of_succ_lt_succ hi)

/-! ## The program's cut -/

/-- An entry of an array of words is the entry of its list. -/
private theorem word_toList (w : Array F) (k : ℕ) : w.getD k 0 = w.toList.getD k 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- Three words as an element of the program are read as the format's symbol. -/
theorem readE_sym3 (w : Array F) (k : ℕ) :
    readE (E.mk3 (w.getD k 0) (w.getD (k + 1) 0) (w.getD (k + 2) 0)) = toE (sym3 w.toList k) := by
  rw [readE_mk3, word_toList, word_toList, word_toList]
  rfl

/-- The numbers of symbols that the program cuts out of a column. -/
theorem columnOf_size (x : Oracle) (m z : ℕ) (w : Array F) :
    (Blk.columnOf x m z w).main.size = x.shape.mainRows ∧
      (Blk.columnOf x m z w).mask.size = x.shape.maskRows := by
  unfold Blk.columnOf
  simp

/-- A main symbol that the program cuts out of a column, for main rows over the extension
field. -/
theorem columnOf_main (x : Oracle) (m z : ℕ) (w : Array F) (b : ℕ) (hb : b < x.shape.mainRows)
    (h3 : x.shape.mainDeg = 3) :
    readV (Blk.columnOf x m z w).main b = toE (sym3 w.toList (m + 3 * b)) := by
  have e : (Blk.columnOf x m z w).main.getD b zeroE =
      E.mk3 (w.getD (m + 3 * b) 0) (w.getD (m + 3 * b + 1) 0) (w.getD (m + 3 * b + 2) 0) := by
    unfold Blk.columnOf
    simp [Array.getD_eq_getD_getElem?, E.mk3, hb, h3]
  unfold readV
  rw [e, readE_sym3]

/-- A mask symbol that the program cuts out of a column. -/
theorem columnOf_mask (x : Oracle) (m z : ℕ) (w : Array F) (b : ℕ) (hb : b < x.shape.maskRows) :
    readV (Blk.columnOf x m z w).mask b = toE (sym3 w.toList (z + 3 * b)) := by
  have e : (Blk.columnOf x m z w).mask.getD b zeroE =
      E.mk3 (w.getD (z + 3 * b) 0) (w.getD (z + 3 * b + 1) 0) (w.getD (z + 3 * b + 2) 0) := by
    unfold Blk.columnOf
    simp [Array.getD_eq_getD_getElem?, E.mk3, hb]
  unfold readV
  rw [e, readE_sym3]

/-! ## The format's cut of a later stage's column -/

/-- The symbols of a column without symbols over the base field. -/
theorem cutCol_inv (mE nz : ℕ) (w : List UInt64) (me zs : List Fmt.M1.E)
    (h : Fmt.M1.cutCol 0 mE nz w = some (me, zs)) :
    me.length = mE ∧ zs.length = nz ∧
      (∀ i, i < mE → me.getD i Fmt.Fld.zeroE = sym3 w (3 * i)) ∧
      ∀ j, j < nz → zs.getD j Fmt.Fld.zeroE = sym3 w (3 * (mE + j)) := by
  unfold Fmt.M1.cutCol at h
  split at h
  · cases hq : Fmt.M1.takeE mE (w.drop 0) with
    | none =>
      rw [hq] at h
      cases h
    | some q =>
      obtain ⟨me', w'⟩ := q
      rw [hq] at h
      obtain ⟨⟨zs', w''⟩, h0, h1⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨e1, e2⟩ := Prod.mk.inj h1
      have e1' : me' = me := e1
      have e2' : zs' = zs := e2
      subst e1' e2'
      obtain ⟨a1, a2, a3⟩ := takeE_inv _ _ _ _ hq
      obtain ⟨b1, _, b3⟩ := takeE_inv _ _ _ _ h0
      refine ⟨a1, b1, a3, fun j hj => ?_⟩
      rw [b3 j hj, a2, List.drop_drop, sym3_drop]
      congr 1
      ring
  · cases h

/-- An entry of a list after its first n. -/
theorem lst_drop (n : ℕ) (l : List Fmt.M1.E) (t : ℕ) : lst (l.drop n) t = lst l (n + t) := by
  unfold lst
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The format's column of a later stage's tree, word by word. mE main rows over the extension
field were sent; after them come 2^h old mask symbols and 2^h fresh ones. -/
theorem stageCol_inv (st : Fmt.M1.Stage) (mE : ℕ) (w : List UInt64) (col : Fmt.M1.Col)
    (h : Fmt.M1.stageCol st 0 mE w = some col) :
    (∀ i, i < mE → i < 2 ^ st.k → vec col.main i = toE (sym3 w (3 * i))) ∧
      (∀ i, mE ≤ i → vec col.main i = 0) ∧
      (∀ j, j < 2 ^ st.h → vec col.mask j = toE (sym3 w (3 * (mE + j)))) ∧
      ∀ j, j < 2 ^ st.h → vec col.fresh j = toE (sym3 w (3 * (mE + 2 ^ st.h + j))) := by
  obtain ⟨⟨me, zs⟩, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨a1, a2, a3, a4⟩ := cutCol_inv _ _ _ _ _ h0
  have hmain : ∀ i, vec (Array.ofFn (n := 2 ^ st.k) fun i => me.getD i.val Fmt.Fld.zeroE) i =
      if i < 2 ^ st.k then lst me i else 0 := by
    intro i
    unfold vec Fmt.M1.ent
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    split
    · rfl
    · exact toE_zeroE
  refine ⟨fun i hi hk => ?_, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · show vec (Array.ofFn (n := 2 ^ st.k) fun i => me.getD i.val Fmt.Fld.zeroE) i = _
    rw [hmain, if_pos hk]
    unfold lst
    rw [a3 i hi]
  · show vec (Array.ofFn (n := 2 ^ st.k) fun i => me.getD i.val Fmt.Fld.zeroE) i = _
    rw [hmain]
    split
    · exact lst_of_le me i (by rw [a1]; exact hi)
    · rfl
  · show vec (zs.take (2 ^ st.h)).toArray j = _
    rw [vec_toArray, lst_take _ _ _ hj]
    unfold lst
    rw [a4 j (by omega)]
  · show vec (zs.drop (2 ^ st.h)).toArray j = _
    rw [vec_toArray, lst_drop]
    unfold lst
    rw [a4 _ (by omega), Nat.add_assoc]

/-! ## The format's cut of the first tree's column -/

/-- Symbols that are all over the extension field are taken three words each. -/
theorem takeParts_true : ∀ (n : ℕ) (w : List UInt64),
    Fmt.M2.takeParts (List.replicate n true) w = Fmt.M1.takeE n w
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | _ + 1, [_] => rfl
  | _ + 1, [_, _] => rfl
  | n + 1, a :: b :: c :: w => by
    show (Fmt.M2.takeParts (List.replicate n true) w).map _ = (Fmt.M1.takeE n w).map _
    rw [takeParts_true n w]

/-- An entry of a table into which symbols were put at their rows. -/
theorem ent_putRows (n : ℕ) (xs : List (Option ℕ × List Fmt.M1.E)) (i : ℕ) (hi : i < n) :
    Fmt.M1.ent (Fmt.M2.putRows n xs) i =
      (xs.findSome? fun x => x.1.bind fun f =>
        if f ≤ i && i < f + x.2.length then x.2[i - f]? else none).getD Fmt.Fld.zeroE := by
  unfold Fmt.M2.putRows Fmt.M1.ent
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hi]
  rfl

/-- A table into which nothing was put holds zeros. -/
theorem vec_putRows_nil (n : ℕ) (xs : List (Option ℕ × List Fmt.M1.E)) (h : ∀ x ∈ xs, x.2 = [])
    (j : ℕ) : vec (Fmt.M2.putRows n xs) j = 0 := by
  by_cases hj : j < n
  · unfold vec
    rw [ent_putRows _ _ _ hj, List.findSome?_eq_none_iff.2 fun x hx => by
      rw [h x hx]
      cases x.1 <;> simp]
    exact toE_zeroE
  · refine vec_of_le _ _ ?_
    unfold Fmt.M2.putRows
    rw [Array.size_ofFn]
    omega

/-- The symbols of a column whose main symbols are all over the extension field. -/
theorem cutParts_inv (n nz : ℕ) (w : List UInt64) (ms zs : List Fmt.M1.E)
    (h : Fmt.M2.cutParts (List.replicate n true) nz w = some (ms, zs)) :
    ms.length = n ∧ zs.length = nz ∧
      (∀ i, i < n → ms.getD i Fmt.Fld.zeroE = sym3 w (3 * i)) ∧
      ∀ j, j < nz → zs.getD j Fmt.Fld.zeroE = sym3 w (3 * (n + j)) := by
  unfold Fmt.M2.cutParts at h
  rw [takeParts_true] at h
  cases hq : Fmt.M1.takeE n w with
  | none =>
    simp only [hq] at h
    cases h
  | some q =>
    obtain ⟨ms', w'⟩ := q
    simp only [hq] at h
    cases hz : Fmt.M1.takeE nz w' with
    | none =>
      simp only [hz] at h
      cases h
    | some q' =>
      obtain ⟨zs', w''⟩ := q'
      simp only [hz] at h
      cases w'' with
      | cons u v => cases h
      | nil =>
        obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj h)
        subst e1 e2
        obtain ⟨a1, a2, a3⟩ := takeE_inv _ _ _ _ hq
        obtain ⟨b1, _, b3⟩ := takeE_inv _ _ _ _ hz
        refine ⟨a1, b1, a3, fun j hj => ?_⟩
        rw [b3 j hj, a2, sym3_drop]
        congr 1
        ring

/-- The format's column of the first tree, word by word, for a group of two members of R main
rows each over the extension field, without mask rows, and one fresh mask row. The second member's
block begins at row f1. -/
theorem groupCol_inv (m : Fmt.M2.Mem) (hE : m.overE = true) (hm : m.masks = 0) (f1 : ℕ)
    (hst : (Fmt.M2.starts [m, m]).1 = [some 0, some f1]) (hf : m.rows ≤ f1)
    (hk : f1 + m.rows ≤ 2 ^ Fmt.M2.kOf [m, m]) (w : List UInt64) (kc : Fmt.M2.KCol)
    (h : Fmt.M2.groupCol [m, m] 1 w = some kc) :
    (∀ i, i < m.rows → vec kc.col.main i = toE (sym3 w (3 * i))) ∧
      (∀ i, i < m.rows → vec kc.col.main (f1 + i) = toE (sym3 w (3 * (m.rows + i)))) ∧
      (∀ j, vec kc.col.mask j = 0) ∧
      vec kc.col.fresh 0 = toE (sym3 w (3 * (m.rows + m.rows))) := by
  obtain ⟨⟨ms, zs⟩, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  clear h
  have hdeg : Fmt.M2.degsOf [m, m] = List.replicate (m.rows + m.rows) true := by
    show List.replicate m.rows m.overE ++ (List.replicate m.rows m.overE ++ []) = _
    rw [hE, List.append_nil, List.replicate_append_replicate]
  have hsum : ([m, m].map (·.masks)).sum = 0 := by simp [hm]
  rw [hdeg, hsum] at h0
  obtain ⟨a1, a2, a3, a4⟩ := cutParts_inv _ _ _ _ _ h0
  clear h0
  have l1 : (ms.take m.rows).length = m.rows := by
    rw [List.length_take, a1]
    omega
  have l2 : ((ms.drop m.rows).take m.rows).length = m.rows := by
    rw [List.length_take, List.length_drop, a1]
    omega
  have hz : (List.zip [some 0, some f1] (Fmt.M2.splitBy ([m, m].map (·.rows)) ms)) =
      [(some 0, ms.take m.rows), (some f1, (ms.drop m.rows).take m.rows)] := rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun j => ?_, ?_⟩
  · show toE (Fmt.M1.ent (Fmt.M2.putRows (2 ^ Fmt.M2.kOf [m, m])
      ((Fmt.M2.starts [m, m]).1.zip (Fmt.M2.splitBy ([m, m].map (·.rows)) ms))) i) = _
    rw [hst, hz, ent_putRows _ _ i (by omega), ← a3 i (by omega)]
    have hb : i < ms.length := by omega
    simp [l1, hi, hb]
  · show toE (Fmt.M1.ent (Fmt.M2.putRows (2 ^ Fmt.M2.kOf [m, m])
      ((Fmt.M2.starts [m, m]).1.zip (Fmt.M2.splitBy ([m, m].map (·.rows)) ms))) (f1 + i)) = _
    rw [hst, hz, ent_putRows _ _ (f1 + i) (by omega), ← a3 (m.rows + i) (by omega)]
    have hn : ¬ f1 + i < m.rows := by omega
    have hb : m.rows + i < ms.length := by omega
    simp [l1, l2, hi, hn, hb]
  · refine vec_putRows_nil _ _ (fun x hx => ?_) j
    have h2 := (List.of_mem_zip hx).2
    have hs : Fmt.M2.splitBy ([m, m].map (·.masks)) (zs.take ([m, m].map (·.masks)).sum) =
        [[], []] := by
      show [List.take m.masks _, List.take m.masks _] = _
      rw [hm]
      rfl
    rw [hs] at h2
    simpa using h2
  · show vec (zs.drop ([m, m].map (·.masks)).sum).toArray 0 = _
    rw [hsum, vec_toArray, List.drop_zero]
    unfold lst
    rw [a4 0 (by omega), Nat.add_zero]

/-- The rows of the first tree's main table that belong to neither member hold zeros. -/
theorem groupCol_zero (m : Fmt.M2.Mem) (hE : m.overE = true) (hm : m.masks = 0) (f1 : ℕ)
    (hst : (Fmt.M2.starts [m, m]).1 = [some 0, some f1]) (w : List UInt64) (kc : Fmt.M2.KCol)
    (h : Fmt.M2.groupCol [m, m] 1 w = some kc) (b : ℕ) (h1 : m.rows ≤ b)
    (h2 : b < f1 ∨ f1 + m.rows ≤ b) : vec kc.col.main b = 0 := by
  obtain ⟨⟨ms, zs⟩, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  clear h
  have hdeg : Fmt.M2.degsOf [m, m] = List.replicate (m.rows + m.rows) true := by
    show List.replicate m.rows m.overE ++ (List.replicate m.rows m.overE ++ []) = _
    rw [hE, List.append_nil, List.replicate_append_replicate]
  have hsum : ([m, m].map (·.masks)).sum = 0 := by simp [hm]
  rw [hdeg, hsum] at h0
  obtain ⟨a1, _, _, _⟩ := cutParts_inv _ _ _ _ _ h0
  clear h0
  have l1 : (ms.take m.rows).length = m.rows := by
    rw [List.length_take, a1]
    omega
  have l2 : ((ms.drop m.rows).take m.rows).length = m.rows := by
    rw [List.length_take, List.length_drop, a1]
    omega
  have hz : (List.zip [some 0, some f1] (Fmt.M2.splitBy ([m, m].map (·.rows)) ms)) =
      [(some 0, ms.take m.rows), (some f1, (ms.drop m.rows).take m.rows)] := rfl
  show vec (Fmt.M2.putRows (2 ^ Fmt.M2.kOf [m, m])
    ((Fmt.M2.starts [m, m]).1.zip (Fmt.M2.splitBy ([m, m].map (·.rows)) ms))) b = 0
  rw [hst, hz]
  by_cases hb : b < 2 ^ Fmt.M2.kOf [m, m]
  · unfold vec
    rw [ent_putRows _ _ b hb]
    have n1 : ¬ b < m.rows := by omega
    have n2 : ¬ (f1 ≤ b ∧ b < f1 + m.rows) := by omega
    have e : ([(some 0, ms.take m.rows), (some f1, (ms.drop m.rows).take m.rows)].findSome?
        fun x : Option ℕ × List Fmt.M1.E => x.1.bind fun f =>
          if f ≤ b && b < f + x.2.length then x.2[b - f]? else none) = none := by
      simp [l1, l2, n1]
      intro q1 q2
      exact absurd ⟨q1, q2⟩ n2
    rw [e]
    exact toE_zeroE
  · refine vec_of_le _ _ ?_
    unfold Fmt.M2.putRows
    rw [Array.size_ofFn]
    omega

/-! ## The joints -/

section
variable (x : Oracle) (m z : ℕ) (w : Array F)

/-- A main symbol of the program is an entry of a later stage's column. Its oracle message's main
symbols begin at symbol number `first`. -/
theorem stage_main (st : Fmt.M1.Stage) (mE : ℕ) (col : Fmt.M1.Col)
    (h : Fmt.M1.stageCol st 0 mE w.toList = some col) (first b : ℕ) (hb : b < x.shape.mainRows)
    (h3 : x.shape.mainDeg = 3) (hm : m = 3 * first) (h1 : first + b < mE)
    (h2 : first + b < 2 ^ st.k) :
    readV (Blk.columnOf x m z w).main b = vec col.main (first + b) := by
  rw [columnOf_main x m z w b hb h3, (stageCol_inv st mE _ col h).1 _ h1 h2, hm, Nat.mul_add]

/-- A mask symbol of the program is an entry of a later stage's old mask rows. -/
theorem stage_mask (st : Fmt.M1.Stage) (mE : ℕ) (col : Fmt.M1.Col)
    (h : Fmt.M1.stageCol st 0 mE w.toList = some col) (first b : ℕ) (hb : b < x.shape.maskRows)
    (hz : z = 3 * (mE + first)) (h1 : first + b < 2 ^ st.h) :
    readV (Blk.columnOf x m z w).mask b = vec col.mask (first + b) := by
  rw [columnOf_mask x m z w b hb, (stageCol_inv st mE _ col h).2.2.1 _ h1, hz, ← Nat.mul_add,
    Nat.add_assoc]

/-- A mask symbol of the program is an entry of a later stage's fresh mask rows. -/
theorem stage_fresh (st : Fmt.M1.Stage) (mE : ℕ) (col : Fmt.M1.Col)
    (h : Fmt.M1.stageCol st 0 mE w.toList = some col) (first b : ℕ) (hb : b < x.shape.maskRows)
    (hz : z = 3 * (mE + 2 ^ st.h + first)) (h1 : first + b < 2 ^ st.h) :
    readV (Blk.columnOf x m z w).mask b = vec col.fresh (first + b) := by
  rw [columnOf_mask x m z w b hb, (stageCol_inv st mE _ col h).2.2.2 _ h1, hz, ← Nat.mul_add,
    Nat.add_assoc]

variable (mem : Fmt.M2.Mem) (hE : mem.overE = true) (hm0 : mem.masks = 0) (f1 : ℕ)
  (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1]) (hf : mem.rows ≤ f1)
  (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem]) (kc : Fmt.M2.KCol)
  (h : Fmt.M2.groupCol [mem, mem] 1 w.toList = some kc)
include hE hm0 hst hf hk h

/-- A main symbol of the first member is an entry of the first tree's column. -/
theorem group_main0 (b : ℕ) (hb : b < x.shape.mainRows) (h3 : x.shape.mainDeg = 3) (hm : m = 0)
    (h1 : b < mem.rows) : readV (Blk.columnOf x m z w).main b = vec kc.col.main b := by
  rw [columnOf_main x m z w b hb h3, (groupCol_inv mem hE hm0 f1 hst hf hk _ kc h).1 _ h1, hm,
    Nat.zero_add]

/-- A main symbol of the second member is an entry of the first tree's column, in the block that
begins at row f1. -/
theorem group_main1 (b : ℕ) (hb : b < x.shape.mainRows) (h3 : x.shape.mainDeg = 3)
    (hm : m = 3 * mem.rows) (h1 : b < mem.rows) :
    readV (Blk.columnOf x m z w).main b = vec kc.col.main (f1 + b) := by
  rw [columnOf_main x m z w b hb h3, (groupCol_inv mem hE hm0 f1 hst hf hk _ kc h).2.1 _ h1, hm,
    Nat.mul_add]

/-- The mask symbol of the oracle message that holds the fresh mask is the first tree's fresh
entry. -/
theorem group_fresh (hb : 0 < x.shape.maskRows) (hz : z = 3 * (mem.rows + mem.rows)) :
    readV (Blk.columnOf x m z w).mask 0 = vec kc.col.fresh 0 := by
  rw [columnOf_mask x m z w 0 hb, (groupCol_inv mem hE hm0 f1 hst hf hk _ kc h).2.2.2, hz,
    Nat.mul_zero, Nat.add_zero]

end

end OnBytes.Slice

#print axioms OnBytes.Slice.columnOf_main
#print axioms OnBytes.Slice.columnOf_mask
#print axioms OnBytes.Slice.stageCol_inv
#print axioms OnBytes.Slice.groupCol_inv
#print axioms OnBytes.Slice.groupCol_zero
#print axioms OnBytes.Slice.stage_main
#print axioms OnBytes.Slice.stage_mask
#print axioms OnBytes.Slice.stage_fresh
#print axioms OnBytes.Slice.group_main0
#print axioms OnBytes.Slice.group_main1
#print axioms OnBytes.Slice.group_fresh
#print axioms OnBytes.Slice.sym3_cons3
#print axioms OnBytes.Slice.sym3_drop
#print axioms OnBytes.Slice.takeE_inv
#print axioms OnBytes.Slice.word_toList
#print axioms OnBytes.Slice.readE_sym3
#print axioms OnBytes.Slice.columnOf_size
#print axioms OnBytes.Slice.cutCol_inv
#print axioms OnBytes.Slice.lst_drop
#print axioms OnBytes.Slice.takeParts_true
#print axioms OnBytes.Slice.ent_putRows
#print axioms OnBytes.Slice.vec_putRows_nil
#print axioms OnBytes.Slice.cutParts_inv
