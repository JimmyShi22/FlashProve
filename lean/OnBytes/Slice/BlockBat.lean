-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlockBat.lean: the round of the written link in which all rows become one, for the
format's own functions.

To take a round off is to show that the prover has lost before the round from what is known after
it. OnBytes/Slice/BatSem.lean takes that round off for rows that are given in the field. This file
lays a row of the format's on the group's tables (`rowStm`) and shows that the row that the format
computes from rows under the powers of an element (`Fmt.M2.sumM`) is their sum (`stm_sum`). No round
is taken off here. That the rows which the format's verifier forms (Fmt/M3Link.lean: `rowsLit`) are
the rows of BatSem.lean, and that `batchLit` gives their sum, is not shown here.











What is asked.
 `BatOK`      the field modulo 2^64 - 2^32 + 1; the layout "rows high"; a row's length is a power of
              two; and what BatSem.lean asks of the radius and of the main code.
 `BatDraws`   what each of the six rounds sends and draws.
 `ViewTie`    a stored column that the view shows is the column that the stored string holds.
 `ColTie`     the columns on the stage's rows are those of the tree that the prover sent.





Main definitions: `BatOK`, `BatDraws`, `ViewTie`, `ColTie`, `rowStm`.
Main theorems: `vecIn_atJ`, `stm_sum`.
Not claimed. That the hypotheses hold at given sizes and rounds. Nothing on the rounds that follow.
-/
import OnBytes.Slice.BatSem
import OnBytes.Slice.SimLink
import OnBytes.Slice.SimSample

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## What is asked -/

/-- What is asked of the sizes, the radius e and the number d. -/
structure BatOK (S : Sz) (e d : ℕ) : Prop extends SemOK S e d where
  fld : S.P.fld = .two
  high : S.P.high = true
  pow : S.P.C.l = 2 ^ S.P.aP

/-- What the six rounds send and draw. -/
structure BatDraws (S : Sz) (d1 d2 d3 d4 d5 dA : PQ.RD) : Prop where
  r1 : SendsDraws d1 0 S.P.v 0 0
  r2 : SendsDraws d2 0 (S.P.aR + S.P.aP + 1) 0 0
  nz : IsNZ (Fmt.dsOf d2.entry d2.kind) (S.P.aR + S.P.aP)
  r3 : SendsDraws d3 2 0 0 0
  r4 : SendsDraws d4 0 0 (S.P.nu0 + S.P.nuj) S.P.T.a
  r5 : SendsDraws d5 0 S.P.aPhi 0 0
  rA : SendsDraws dA 0 1 0 0

/-- What the view shows of a stored table at a position is the column that the string holds. -/
def ViewTie (S : Sz) (V : Fmt.M3.View) (y : S.lk.E0.Str) : Prop :=
  ∀ (x : S.Pos) (c : List UInt64),
    (Fmt.M3.storedAt V 0 x.val = some c → c = (y.1 x).2) ∧
    (Fmt.M3.storedAt V 1 x.val = some c → c = (y.2 x).2)

/-- The columns on the group's rows are those of the written oracle: row i of member a's block holds
the member's symbol number i, and 0 if the member has no such row. -/
structure ColTie (S : Sz) (d2 : PQ.RD) (o : (wRound d2).Orc) (col : ℕ → Fmt.M1.Col) : Prop where
  sent : ∀ (x : Fin (2 ^ S.P.C.a)) (a : Bool) (i : ℕ), i < S.P.R →
    vec (col x.val).main (S.blk a + i) = symAt d2 o x.val ((if a then S.P.R else 0) + i)
  free : ∀ (x : Fin (2 ^ S.P.C.a)) (a : Bool) (i : ℕ), S.P.R ≤ i → i < 2 ^ S.P.aR →
    vec (col x.val).main (S.blk a + i) = 0

/-- The number of the vertex of row i of member a's block. -/
theorem rowNo_memRow (S : Sz) (t : ℕ) (a : Bool) (i : ℕ) (hi : i < 2 ^ S.P.aR) :
    Sz.rowNo (memRow S t a i) = S.blk a + i := by
  have hb : S.blk a ≤ 2 ^ S.P.aR := by
    unfold Sz.blk
    split <;> omega
  have hlt : S.blk a + i < 2 ^ ((S.sg t).h + (S.sg t).g) := by
    show S.blk a + i < 2 ^ (0 + (S.P.aR + 1))
    rw [Nat.zero_add, Nat.pow_succ]
    omega
  exact (rowNo_testBit ((S.sg t).h + (S.sg t).g) (S.blk a + i)).trans (Nat.mod_eq_of_lt hlt)

/-- The columns as a word meet the tie of the words. -/
theorem wordTie_of_col (S : Sz) (t : ℕ) (d2 : PQ.RD) (o : (wRound d2).Orc)
    (col : ℕ → Fmt.M1.Col) (h : ColTie S d2 o col) : WordTie S t d2 o (wordIn (S.sg t) col) := by
  have hR : S.P.R ≤ 2 ^ S.P.aR := le_two_pow_clog S.P.R
  refine ⟨fun x a i hi => ?_, fun x a i h1 h2 => ?_⟩
  · show vec (col x.val).main (Sz.rowNo (memRow S t a i)) = _
    rw [rowNo_memRow S t a i (lt_of_lt_of_le hi hR)]
    exact h.sent x a i hi
  · show vec (col x.val).main (Sz.rowNo (memRow S t a i)) = _
    rw [rowNo_memRow S t a i h2]
    exact h.free x a i h1 h2

/-! ## The written rows on the group's tables -/

/-- Row number b of a list of rows, laid on the group's tables, as a statement. -/
def rowStm (S : Sz) (t : ℕ) (rows : List Fmt.M2.MRow) (b : ℕ) : GE × ((S.sg t).cIn.J → GE) :=
  stmIn (S.sg t) (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l (rows.getD b noM)).toG

/-- A laid row's coefficient at an entry of a member is the coefficient of the member's form
at the entry's index in the member's own table. -/
theorem vecIn_atJ (S : Sz) (t : ℕ) (R : Fmt.M2.MRow) (a : Bool) (j : S.MJ) :
    vecIn (S.sg t) (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l R).toG (atJ S t a j) =
      vec (R.main.getD (if a then 1 else 0) #[]) (S.idxJ j) := by
  rcases j with ⟨i, p⟩ | ⟨e, _⟩
  · have hi : i.val < 2 ^ S.P.aR := lt_of_lt_of_le i.isLt (le_two_pow_clog S.P.R)
    have hn : S.blk a + i.val < 2 ^ (S.P.aR + 1) := by
      rw [Nat.pow_succ]
      unfold Sz.blk
      split <;> omega
    have hmod : (S.blk a + i.val + 2 ^ (S.P.aR + 1) * p.val) % 2 ^ (S.P.aR + 1) =
        S.blk a + i.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hn]
    have hdiv : (S.blk a + i.val + 2 ^ (S.P.aR + 1) * p.val) / 2 ^ (S.P.aR + 1) = p.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hn, Nat.zero_add]
    have hlt : S.blk a + i.val + 2 ^ (S.P.aR + 1) * p.val < 2 ^ (S.P.aR + 1) * S.P.C.l := by
      have h1 : 2 ^ (S.P.aR + 1) * (p.val + 1) ≤ 2 ^ (S.P.aR + 1) * S.P.C.l :=
        Nat.mul_le_mul_left _ p.isLt
      rw [Nat.mul_add_one] at h1
      omega
    show vec (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l R).c
        (Sz.rowNo (memRow S t a i.val) + 2 ^ (0 + (S.P.aR + 1)) * p.val) =
      vec (R.main.getD (if a then 1 else 0) #[]) (i.val + 2 ^ S.P.aR * p.val)
    rw [rowNo_memRow S t a i.val hi, Nat.zero_add, vec_toK_c S.P S.hR, if_pos hlt, hmod, hdiv]
    cases a with
    | false =>
      have hb : S.blk false = 0 := rfl
      rw [hb, Nat.zero_add, if_pos hi]
      rfl
    | true =>
      have hb : S.blk true = 2 ^ S.P.aR := rfl
      rw [hb, if_neg (by omega), Nat.add_sub_cancel_left]
      rfl
  · exact e.elim

/-- An entry of the main part of the laid sum of rows is the sum of the laid rows' entries under the
powers. -/
private theorem vec_toK_c_sum (P : Fmt.M3.Par) (hR : 0 < P.R) (l lz : ℕ) (x : Fmt.M1.E)
    (rows : List Fmt.M2.MRow) (i : ℕ) :
    vec (Fmt.M2.toK P.mems l lz (Fmt.M2.sumM .two x rows)).c i =
      ∑ k ∈ Finset.range rows.length,
        vec (Fmt.M2.toK P.mems l lz (rows.getD k noM)).c i * toE x ^ k := by
  simp only [vec_toK_c P hR]
  by_cases h : i < 2 ^ (P.aR + 1) * l
  · simp only [if_pos h]
    by_cases h1 : i % 2 ^ (P.aR + 1) < 2 ^ P.aR
    · simp only [if_pos h1]
      rw [vec_sumM_main]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · simp only [if_neg h1]
      rw [vec_sumM_main]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · simp only [if_neg h, zero_mul, Finset.sum_const_zero]

/-- The row that the format computes is the combination of the rows under the powers. -/
theorem stm_sum (S : Sz) (t : ℕ) (hf : S.P.fld = .two) (rows : List Fmt.M2.MRow)
    (hn : rows.length = S.nRows) (theta : Fmt.M1.E) :
    stmIn (S.sg t) (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l (Fmt.M2.sumM S.P.fld theta rows)).toG =
      sumStm S t (fun b => (rowStm S t rows b).1) (fun b => (rowStm S t rows b).2) (toE theta) := by
  rw [hf]
  refine Prod.ext ?_ ?_
  · -- the target
    show toE (Fmt.M2.sumM .two theta rows).t =
      ∑ b : Fin S.nRows, toE theta ^ b.val * toE (rows.getD b.val noM).t
    rw [toE_sumM_t, hn, Finset.sum_range]
  · -- the coefficients, one by one
    funext j
    rcases j with x | x
    · show vec (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l (Fmt.M2.sumM .two theta rows)).c _ =
        ∑ b : Fin S.nRows,
          vec (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l (rows.getD b.val noM)).c _ * toE theta ^ b.val
      rw [vec_toK_c_sum S.P S.hR, hn, Finset.sum_range]
    · show vec (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l (Fmt.M2.sumM .two theta rows)).d _ =
        ∑ b : Fin S.nRows,
          vec (Fmt.M2.toK S.P.mems S.P.C.l S.P.Z.l (rows.getD b.val noM)).d _ * toE theta ^ b.val
      simp only [vec_toK_d, zero_mul, Finset.sum_const_zero]

/-! ## Reading the earlier rounds -/

/-- An entry of a list that is read in the field entry by entry. -/
private theorem getD_map_toE (l : List Fmt.M1.E) (i : ℕ) : (l.map toE).getD i 0 = lst l i := by
  unfold lst
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact toE_zeroE.symm
  | some a => rfl

/-- The drawn elements as the library's point are the list that the decision reads. -/
theorem gVec_rv (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) (n : ℕ) :
    gVec n _ (valsOf d c) = fun i => lst (rvOf d m c).els i.val := by
  funext i
  show (elemsV _ (valsOf d c)).getD i.val 0 = _
  rw [← rvOf_els d m c, getD_map_toE]

/-- The draws with their tables, one by one. -/
theorem drawsOf_getD (P : Fmt.M3.Par) (xs : List ℕ) (n : ℕ) (hn : n < xs.length) :
    (Fmt.M3.drawsOf P xs).getD n (0, 0) = (if n < P.nu0 then 0 else 1, xs.getD n 0) := by
  unfold Fmt.M3.drawsOf
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  by_cases h : n < P.nu0
  · rw [List.getElem?_append_left (by rw [List.length_map, List.length_take]; omega),
      List.getElem?_map, List.getElem?_take_of_lt h, List.getElem?_eq_getElem hn, if_pos h]
    rfl
  · have hl : ((xs.take P.nu0).map fun x => (0, x)).length = P.nu0 := by
      rw [List.length_map, List.length_take]
      omega
    rw [List.getElem?_append_right (by rw [hl]; omega), hl, List.getElem?_map, List.getElem?_drop,
      show P.nu0 + (n - P.nu0) = n by omega, List.getElem?_eq_getElem hn, if_neg h]
    rfl

/-- There are as many draws with tables as drawn positions. -/
theorem drawsOf_length (P : Fmt.M3.Par) (xs : List ℕ) :
    (Fmt.M3.drawsOf P xs).length = xs.length := by
  unfold Fmt.M3.drawsOf
  rw [List.length_append, List.length_map, List.length_map, List.length_take, List.length_drop]
  omega

/-- Membership in a union, whatever the test of equality with which the union is formed. -/
private theorem mem_union_any {α : Type} (inst : DecidableEq α) {s t : Finset α} {a : α} :
    a ∈ @Union.union _ (@Finset.instUnion α inst) s t ↔ a ∈ s ∨ a ∈ t := Finset.mem_union

/-- Membership in an image, whatever the test of equality with which the image is formed. -/
private theorem mem_image_any {α β : Type} (inst : DecidableEq β) {f : α → β} {s : Finset α}
    {b : β} : b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

section Lit
variable (S : Sz) (t e d : ℕ) (d1 d2 d3 d4 d5 dA : PQ.RD)

end Lit



end OnBytes.Slice

#print axioms OnBytes.Slice.wordTie_of_col
#print axioms OnBytes.Slice.vecIn_atJ
#print axioms OnBytes.Slice.stm_sum
