-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BatCol.lean: the format's way from a leaf's column to the rows of the link's group
meets the tie that OnBytes/Slice/BlockBat.lean asks.

The link's group has two members, each of R rows over the extension field and without mask rows. A
leaf's column also holds one fresh mask symbol. The format (the verifier of the library's folder
Fmt/) cuts the column into symbols of three words and puts them at the group's rows
(Fmt/M2Types.lean: groupCol). The first member's symbols go to the rows from 0 on, the second's to
the rows from 2^aR on. A row that no member has holds 0. This file shows that the column so made
meets the record ColTie: each row holds the symbol of the written oracle that the record names.

Main theorem: colTie_of_groupCol.
Not claimed. Nothing is said of a column that the format refuses: the hypothesis asks that groupCol
gives a column at every position. Nothing on the mask symbols of a column: ColTie asks for the main
rows alone.
-/
import OnBytes.Slice.BlockBat

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- Symbols over the extension field off a list of words: three words each. -/
private theorem takeParts_true : ∀ (n : ℕ) (w : List UInt64) (ms : List Fmt.M1.E)
    (w' : List UInt64), Fmt.M2.takeParts (List.replicate n true) w = some (ms, w') →
    ms.length = n ∧ ∀ i, i < n → ms.getD i Fmt.Fld.zeroE =
      (w.getD (3 * i) 0, w.getD (3 * i + 1) 0, w.getD (3 * i + 2) 0)
  | 0, w, ms, w', h => by
    simp only [List.replicate_zero, Fmt.M2.takeParts, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, [], ms, w', h => by simp [List.replicate_succ, Fmt.M2.takeParts] at h
  | n + 1, [_], ms, w', h => by simp [List.replicate_succ, Fmt.M2.takeParts] at h
  | n + 1, [_, _], ms, w', h => by simp [List.replicate_succ, Fmt.M2.takeParts] at h
  | n + 1, a :: b :: c :: w0, ms, w', h => by
    simp only [List.replicate_succ, Fmt.M2.takeParts] at h
    cases h2 : Fmt.M2.takeParts (List.replicate n true) w0 with
    | none => simp [h2] at h
    | some y =>
      obtain ⟨m1, w1⟩ := y
      simp only [h2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hl, hv⟩ := takeParts_true n w0 m1 w1 h2
      refine ⟨by simp [hl], fun i hi => ?_⟩
      cases i with
      | zero => rfl
      | succ i =>
        rw [List.getD_cons_succ, hv i (by omega)]
        simp only [show 3 * (i + 1) = 3 * i + 1 + 1 + 1 by omega, List.getD_cons_succ]

/-- A word of the written oracle's column is an entry of the column as a list. -/
private theorem wordAt_eq (d : PQ.RD) (o : (wRound d).Orc) (x j : ℕ) :
    wordAt d o x j = (colW d o x).getD j 0 := by
  unfold wordAt colW
  by_cases hx : x < PQ.posN d.tree
  · rw [dif_pos hx, dif_pos hx, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hj : j < PQ.colW d.tree
    · rw [dif_pos hj, dif_pos hj]
      rfl
    · rw [dif_neg hj, dif_neg hj]
      rfl
  · rw [dif_neg hx, dif_neg hx]
    rfl

/-- The main rows of the column that the format puts on the link's group: the symbols of the first
member from row 0 on, those of the second from row 2^aR on. -/
private theorem groupCol_main (P : Fmt.M3.Par) (hR : 0 < P.R) (w : List UInt64) (c : Fmt.M1.Col)
    (h : (Fmt.M2.groupCol P.mems 1 w).map (·.col) = some c) :
    ∃ ms : List Fmt.M1.E, ms.length = P.R + P.R ∧
      (∀ i, i < P.R + P.R → ms.getD i Fmt.Fld.zeroE =
        (w.getD (3 * i) 0, w.getD (3 * i + 1) 0, w.getD (3 * i + 2) 0)) ∧
      c.main = Fmt.M2.putRows (2 ^ (P.aR + 1))
        [(some 0, ms.take P.R), (some (2 ^ P.aR), (ms.drop P.R).take P.R)] := by
  have hdeg : Fmt.M2.degsOf P.mems = List.replicate (P.R + P.R) true := by
    show List.replicate P.R true ++ (List.replicate P.R true ++ []) = _
    rw [List.append_nil, List.replicate_append_replicate]
  unfold Fmt.M2.groupCol at h
  cases hc : Fmt.M2.cutParts (Fmt.M2.degsOf P.mems) ((P.mems.map (·.masks)).sum + 1) w with
  | none => simp [hc] at h
  | some y =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    unfold Fmt.M2.cutParts at hc
    rw [hdeg] at hc
    split at hc
    · cases hc
    · next ms w' ht =>
      split at hc
      · next zs hz =>
        cases hc
        obtain ⟨hl, hv⟩ := takeParts_true _ _ _ _ ht
        refine ⟨ms, hl, hv, ?_⟩
        show Fmt.M2.putRows (2 ^ Fmt.M2.kOf P.mems)
          ((Fmt.M2.starts P.mems).1.zip (Fmt.M2.splitBy (P.mems.map (·.rows)) ms)) = _
        rw [kOf_mems P hR, starts_mems P hR]
        rfl
      · cases hc

/-- An entry of symbols that are put at two blocks of rows, the first from row 0 on. Where both
blocks have a row, the first block's symbol is taken. -/
private theorem vec_putRows_two (n f1 : ℕ) (A B : List Fmt.M1.E) (e : ℕ) (he : e < n) :
    vec (Fmt.M2.putRows n [(some 0, A), (some f1, B)]) e =
      if e < A.length then toE (A.getD e Fmt.Fld.zeroE)
      else if f1 ≤ e ∧ e < f1 + B.length then toE (B.getD (e - f1) Fmt.Fld.zeroE) else 0 := by
  unfold Fmt.M2.putRows
  rw [vec_ofFn, dif_pos he]
  by_cases h1 : e < A.length
  · simp [List.findSome?, h1, List.getD_eq_getElem?_getD]
  · by_cases h2 : f1 ≤ e ∧ e < f1 + B.length
    · simp [List.findSome?, h1, h2.1, h2.2, List.getD_eq_getElem?_getD]
      cases B[e - f1]? <;> rfl
    · rw [if_neg h1, if_neg h2]
      have h3 : ¬ (f1 ≤ e ∧ e < f1 + B.length) := h2
      simp [List.findSome?, h1, h3, toE_zeroE]

/-- The format's own way from a leaf's column to the group's rows meets the tie, if it gives a
column at every position. -/
theorem colTie_of_groupCol (S : Sz) (d2 : PQ.RD) (o : (wRound d2).Orc) (col : ℕ → Fmt.M1.Col)
    (h : ∀ x : Fin (2 ^ S.P.C.a),
      (Fmt.M2.groupCol S.P.mems 1 (colW d2 o x.val)).map (·.col) = some (col x.val)) :
    ColTie S d2 o col := by
  have hle : S.P.R ≤ 2 ^ S.P.aR := le_two_pow_clog S.P.R
  have key : ∀ (x : Fin (2 ^ S.P.C.a)) (a : Bool) (i : ℕ), i < 2 ^ S.P.aR →
      vec (col x.val).main (S.blk a + i) =
        if i < S.P.R then symAt d2 o x.val ((if a then S.P.R else 0) + i) else 0 := by
    intro x a i hi
    obtain ⟨ms, hl, hv, hm⟩ := groupCol_main S.P S.hR _ _ (h x)
    have hA : (ms.take S.P.R).length = S.P.R := by
      rw [List.length_take, hl]
      omega
    have hB : ((ms.drop S.P.R).take S.P.R).length = S.P.R := by
      rw [List.length_take, List.length_drop, hl]
      omega
    have hsym : ∀ k, k < S.P.R + S.P.R →
        toE (ms.getD k Fmt.Fld.zeroE) = symAt d2 o x.val k := by
      intro k hk
      rw [hv k hk]
      unfold symAt
      rw [wordAt_eq, wordAt_eq, wordAt_eq]
    have he : S.blk a + i < 2 ^ (S.P.aR + 1) := by
      rw [pow_succ]
      unfold Sz.blk
      split <;> omega
    rw [hm, vec_putRows_two _ _ _ _ _ he, hA, hB]
    cases a
    · have e0 : S.blk false + i = i := by
        unfold Sz.blk
        simp
      rw [e0]
      by_cases hi' : i < S.P.R
      · rw [if_pos hi', if_pos hi', List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi',
          ← List.getD_eq_getElem?_getD, hsym i (by omega)]
        simp
      · rw [if_neg hi', if_neg hi', if_neg (by omega)]
    · have e1 : S.blk true + i = 2 ^ S.P.aR + i := by
        unfold Sz.blk
        simp
      rw [e1, if_neg (by omega)]
      by_cases hi' : i < S.P.R
      · rw [if_pos ⟨by omega, by omega⟩, if_pos hi', Nat.add_sub_cancel_left,
          List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi', List.getElem?_drop,
          ← List.getD_eq_getElem?_getD, hsym (S.P.R + i) (by omega)]
        simp
      · rw [if_neg (by omega), if_neg hi']
  refine ⟨fun x a i hi => ?_, fun x a i h1 h2 => ?_⟩
  · rw [key x a i (lt_of_lt_of_le hi hle), if_pos hi]
  · rw [key x a i h2, if_neg (by omega)]

end OnBytes.Slice

#print axioms OnBytes.Slice.colTie_of_groupCol
