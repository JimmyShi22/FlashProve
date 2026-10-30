-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatApply.lean: the batched row APPLIED TO TABLES: what the row that
`Bat.combine` (OnBytes/Iop/Bat.lean) returns says of the group's two tables and of the kept members'
own tables, against what each row says of the oracle messages' own tables. Definitions, statements
and proofs.

BatVector.lean, beside this file, reads the batched row's coefficients at every index. Here they are
multiplied with the tables' entries and added up.
  `shiftIn_lt`, `unshift_lt`, `sum_inBlock`: a sum over the indices of a group's table that lie in
    one block is the sum over the indices of the member's own table.
  `foldedWeight`, `maskedWeight`: 1 if an oracle message is a member whose main rows are folded; a
    member with mask rows; else 0. `sum_mainWeight`, `sum_maskWeight`: one message's share.
  `rowMain_apply`, `rowMask_apply`: one row applied to the group's main table, its mask table.
  `sum_hornerSum`, `hornerSum_add`, `hornerSum_sub`: sums under powers are linear.
  `combine_main_apply`, `combine_mask_apply`, `combine_kept_apply`: the batched row applied.
  `rowSumIn ρ S L N tab r`: what a row says of the tables tab, seen through the group.
  `groupSum ρ S L N tab TM TZ G`: what a row on a group says of the group's tables TM, TZ and of the
    kept members' own main tables.
  `combine_defect`: `groupSum` of the batched row minus its target is the sum, under the powers of
    the drawn element, of `rowSumIn` of each row minus that row's target.
  `NamesMembers`, `rowSumIn_eq`: for a row that names the group's members alone, `rowSumIn` is the
    row's coefficients applied to the two tables of each oracle message below N.

Limits. Those of BatVector.lean. TM and TZ are letters with one premise each: at an index at which
an oracle message has a weight they hold that message's entry. So where two members' blocks
overlapped, only tables in which the two members' entries agree there would do. What they hold
elsewhere is free: there the batched row's coefficient reads as 0. `NamesMembers` is shown of no row
that a verifier makes. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.BatVector

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes
open Model

variable {K : Type} [CommRing K]

/-- An index with bits put in is below 2^(a + c + p) if the index is below 2^(a + p). -/
theorem shiftIn_lt (a c v p e : ℕ) (he : e < 2 ^ (a + p)) : shiftIn a c v e < 2 ^ (a + c + p) := by
  rw [shiftIn_form]
  have h1 : e % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : v % 2 ^ c < 2 ^ c := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : e / 2 ^ a < 2 ^ p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm p a]
    exact he
  have h4 : v % 2 ^ c + e / 2 ^ a * 2 ^ c < 2 ^ c * 2 ^ p := by
    calc v % 2 ^ c + e / 2 ^ a * 2 ^ c < 2 ^ c + e / 2 ^ a * 2 ^ c := by omega
      _ = (e / 2 ^ a + 1) * 2 ^ c := by ring
      _ ≤ 2 ^ p * 2 ^ c := Nat.mul_le_mul_right _ h3
      _ = 2 ^ c * 2 ^ p := Nat.mul_comm _ _
  calc e % 2 ^ a + 2 ^ a * (v % 2 ^ c + e / 2 ^ a * 2 ^ c)
      < 2 ^ a + 2 ^ a * (v % 2 ^ c + e / 2 ^ a * 2 ^ c) := by omega
    _ = 2 ^ a * (v % 2 ^ c + e / 2 ^ a * 2 ^ c + 1) := by ring
    _ ≤ 2 ^ a * (2 ^ c * 2 ^ p) := Nat.mul_le_mul_left _ h4
    _ = 2 ^ (a + c + p) := by rw [Nat.pow_add, Nat.pow_add]; ring

/-- An index without its bits a, .., a + c - 1 is below 2^(a + p) if the index is below
2^(a + c + p). -/
theorem unshift_lt (a c p J : ℕ) (hJ : J < 2 ^ (a + c + p)) : unshift a c J < 2 ^ (a + p) := by
  unfold unshift
  have h1 : J % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : J / 2 ^ (a + c) < 2 ^ p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm p (a + c)]
    exact hJ
  calc J % 2 ^ a + 2 ^ a * (J / 2 ^ (a + c)) < 2 ^ a + 2 ^ a * (J / 2 ^ (a + c)) := by omega
    _ = 2 ^ a * (J / 2 ^ (a + c) + 1) := by ring
    _ ≤ 2 ^ a * 2 ^ p := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (a + p) := by rw [Nat.pow_add]

/-- **A sum over a block.** Over the indices J below 2^(a + c + p) whose bits a, .., a + c - 1 are
those of v, a function of J without these bits sums as the function over all indices below
2^(a + p). -/
theorem sum_inBlock (a c v p : ℕ) (F : ℕ → K) :
    ∑ J ∈ Finset.range (2 ^ (a + c + p)),
        (if J / 2 ^ a % 2 ^ c = v % 2 ^ c then F (unshift a c J) else 0) =
      ∑ e ∈ Finset.range (2 ^ (a + p)), F e := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun e _ => shiftIn a c v e) ?_ ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨shiftIn_lt a c v p e (Finset.mem_range.1 he), ((shiftIn_eq_iff a c v e _).1 rfl).1⟩
  · intro e _ e' _ h
    have h' : shiftIn a c v e = shiftIn a c v e' := h
    rw [← unshift_shiftIn a c v e, h', unshift_shiftIn]
  · intro J hJ
    rw [Finset.mem_filter, Finset.mem_range] at hJ
    exact ⟨unshift a c J, Finset.mem_range.2 (unshift_lt a c p J hJ.1),
      (shiftIn_eq_iff a c v _ J).2 ⟨hJ.2, rfl⟩⟩
  · intro e _
    rw [unshift_shiftIn]

variable (ρ : Reading K)

/-- 1 if o is a member whose main rows are folded (it is not kept and has a block); else 0. -/
def foldedWeight (L : GroupLayout) (o : ℕ) : K :=
  match L.find o with
  | none => 0
  | some i => if L.kept.getD i false then 0 else
    match L.mainFirst.getD i none with
    | none => 0
    | some _ => 1

/-- **One oracle message's share of a sum over the group's main table.** p: the table's number of
place bits. Over the indices J of the group's main table, the message's weight at J times a function
of the entry of the message's own table that belongs to J sums as that function over the message's
own table, if the message is a member whose rows are folded, and as 0 if it is not. -/
theorem sum_mainWeight (S : Statement) (L : GroupLayout) (hL : MainBlocksOk S L) (o p : ℕ)
    (F : ℕ → K) :
    ∑ J ∈ Finset.range (2 ^ (L.k + p)), mainWeight (K := K) S L o J * F (mainBack S L o J) =
      foldedWeight (K := K) L o * ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + p)), F e := by
  unfold mainWeight foldedWeight mainBack
  cases hf : L.find o with
  | none => simp
  | some i =>
    dsimp only
    by_cases hk : L.kept.getD i false = true
    · simp [hk]
    · simp only [hk, Bool.false_eq_true, if_false]
      cases hm : L.mainFirst.getD i none with
      | none => simp
      | some first =>
        dsimp only
        have hb := hL o i first hf hm
        have e : L.k + p = S.rowBits o .main + (L.k - S.rowBits o .main) + p := by
          rw [Nat.add_sub_cancel' hb.le]
        rw [one_mul, e, ← sum_inBlock (S.rowBits o .main) (L.k - S.rowBits o .main)
          (first / 2 ^ S.rowBits o .main) p F]
        refine Finset.sum_congr rfl fun J _ => ?_
        split <;> simp

/-- **A row applied to the group's main table.** T: the group's main table: at every index at which
an oracle message has a weight it holds the entry of that message's own main table (tab) that
belongs to the index. What the row weighs on the group's table, applied to T, is the row's own
coefficients applied to the main tables of the members whose rows are folded. -/
theorem rowMain_apply (S : Statement) (L : GroupLayout) (hL : MainBlocksOk S L) (N p : ℕ) (r : Row)
    (tab : ℕ → ℕ → K) (T : ℕ → K)
    (hT : ∀ o J, mainWeight (K := K) S L o J ≠ 0 → T J = tab o (mainBack S L o J)) :
    ∑ J ∈ Finset.range (2 ^ (L.k + p)), rowMain ρ S L N r J * T J =
      ∑ o ∈ Finset.range N, foldedWeight (K := K) L o *
        ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + p)),
          ρ.val (r.coefficient o .main e) * tab o e := by
  unfold rowMain
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← sum_mainWeight S L hL o p fun e => ρ.val (r.coefficient o .main e) * tab o e]
  refine Finset.sum_congr rfl fun J _ => ?_
  by_cases hw : mainWeight (K := K) S L o J = 0
  · rw [hw]
    ring
  · rw [hT o J hw]
    ring

/-! ## The mask table -/

/-- 1 if o is a member with a block of mask rows; else 0. -/
def maskedWeight (L : GroupLayout) (o : ℕ) : K :=
  match L.find o with
  | none => 0
  | some i =>
    match L.maskFirst.getD i none with
    | none => 0
    | some _ => 1

/-- One oracle message's share of a sum over the group's mask table. -/
theorem sum_maskWeight (S : Statement) (L : GroupLayout) (hL : MaskBlocksOk S L) (o p : ℕ)
    (F : ℕ → K) :
    ∑ J ∈ Finset.range (2 ^ (L.h + p)), maskWeight (K := K) S L o J * F (maskBack S L o J) =
      maskedWeight (K := K) L o * ∑ e ∈ Finset.range (2 ^ (S.rowBits o .mask + p)), F e := by
  unfold maskWeight maskedWeight maskBack
  cases hf : L.find o with
  | none => simp
  | some i =>
    dsimp only
    cases hm : L.maskFirst.getD i none with
    | none => simp
    | some first =>
      dsimp only
      have hb := hL o i first hf hm
      have e : L.h + p = S.rowBits o .mask + (L.h - S.rowBits o .mask) + p := by
        rw [Nat.add_sub_cancel' hb.le]
      rw [one_mul, e, ← sum_inBlock (S.rowBits o .mask) (L.h - S.rowBits o .mask)
        (first / 2 ^ S.rowBits o .mask) p F]
      refine Finset.sum_congr rfl fun J _ => ?_
      split <;> simp

/-- A row applied to the group's mask table. -/
theorem rowMask_apply (S : Statement) (L : GroupLayout) (hL : MaskBlocksOk S L) (N p : ℕ) (r : Row)
    (tab : ℕ → ℕ → K) (T : ℕ → K)
    (hT : ∀ o J, maskWeight (K := K) S L o J ≠ 0 → T J = tab o (maskBack S L o J)) :
    ∑ J ∈ Finset.range (2 ^ (L.h + p)), rowMask ρ S L N r J * T J =
      ∑ o ∈ Finset.range N, maskedWeight (K := K) L o *
        ∑ e ∈ Finset.range (2 ^ (S.rowBits o .mask + p)),
          ρ.val (r.coefficient o .mask e) * tab o e := by
  unfold rowMask
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← sum_maskWeight S L hL o p fun e => ρ.val (r.coefficient o .mask e) * tab o e]
  refine Finset.sum_congr rfl fun J _ => ?_
  by_cases hw : maskWeight (K := K) S L o J = 0
  · rw [hw]
    ring
  · rw [hT o J hw]
    ring

/-! ## The batched row applied -/

/-- A sum under powers, applied place by place, is the sum under powers of what is applied. -/
theorem sum_hornerSum {α : Type} (s : Finset ℕ) (y : K) (f : α → ℕ → K) (T : ℕ → K) :
    ∀ l : List α, ∑ J ∈ s, hornerSum y (l.map fun r => f r J) * T J =
      hornerSum y (l.map fun r => ∑ J ∈ s, f r J * T J)
  | [] => by simp [hornerSum]
  | r :: l => by
    simp only [List.map_cons, hornerSum, add_mul, Finset.sum_add_distrib, mul_assoc,
      ← Finset.mul_sum, sum_hornerSum s y f T l]

/-- **The batched row applied to the group's main table** is the sum, under the powers of x, of the
rows' own coefficients applied to the main tables of the members whose rows are folded. -/
theorem combine_main_apply (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MainBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r) (N p : ℕ) (hN : input.layout.top ≤ N)
    (tab : ℕ → ℕ → K) (T : ℕ → K)
    (hT : ∀ o J, mainWeight (K := K) S input.layout o J ≠ 0 →
      T J = tab o (mainBack S input.layout o J)) :
    ∑ J ∈ Finset.range (2 ^ (input.layout.k + p)), ρ.val (out.c.entry J) * T J =
      hornerSum (ρ.val x) (input.rows.toList.map fun r =>
        ∑ o ∈ Finset.range N, foldedWeight (K := K) input.layout o *
          ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + p)),
            ρ.val (r.coefficient o .main e) * tab o e) := by
  have e1 : ∀ J, ρ.val (out.c.entry J) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      rowMain ρ S input.layout N r J) := fun J =>
    combine_main_all ρ S g input x out h hL hr N J fun o ho =>
      mainWeight_top S input.layout o J (hN.trans ho)
  simp only [e1]
  rw [sum_hornerSum]
  refine congrArg _ (List.map_congr_left fun r _ => ?_)
  exact rowMain_apply ρ S input.layout hL N p r tab T hT

/-- **The batched row applied to the group's mask table.** -/
theorem combine_mask_apply (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (N : ℕ)
    (hN : input.layout.top ≤ N) (tab : ℕ → ℕ → K) (T : ℕ → K)
    (hT : ∀ o J, maskWeight (K := K) S input.layout o J ≠ 0 →
      T J = tab o (maskBack S input.layout o J)) :
    ∑ J ∈ Finset.range (2 ^ (input.layout.h + input.layout.logEllZk)),
        ρ.val (out.d.getD J zeroE) * T J =
      hornerSum (ρ.val x) (input.rows.toList.map fun r =>
        ∑ o ∈ Finset.range N, maskedWeight (K := K) input.layout o *
          ∑ e ∈ Finset.range (2 ^ (S.rowBits o .mask + input.layout.logEllZk)),
            ρ.val (r.coefficient o .mask e) * tab o e) := by
  have e1 : ∀ J ∈ Finset.range (2 ^ (input.layout.h + input.layout.logEllZk)),
      ρ.val (out.d.getD J zeroE) * T J = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
        rowMask ρ S input.layout N r J) * T J := fun J hJ => by
    rw [combine_mask_all ρ S g input x out h hL hr N J (Finset.mem_range.1 hJ) fun o ho =>
      maskWeight_top S input.layout o J (hN.trans ho)]
  rw [Finset.sum_congr rfl e1, sum_hornerSum]
  refine congrArg _ (List.map_congr_left fun r _ => ?_)
  exact rowMask_apply ρ S input.layout hL N _ r tab T hT

/-- **The batched row's forms on the kept members, applied to these members' own main tables.**
sz o: the number of entries of the main table of the message o. -/
theorem combine_kept_apply (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r) (N : ℕ)
    (sz : ℕ → ℕ) (tab : ℕ → ℕ → K) :
    ∑ o ∈ Finset.range N, ∑ e ∈ Finset.range (sz o),
        keptSum ρ o e out.kept.toList * tab o e =
      hornerSum (ρ.val x) (input.rows.toList.map fun r =>
        ∑ o ∈ Finset.range N, keptWeight (K := K) input.layout o *
          ∑ e ∈ Finset.range (sz o), ρ.val (r.coefficient o .main e) * tab o e) := by
  have e1 : ∀ o, ∑ e ∈ Finset.range (sz o), keptSum ρ o e out.kept.toList * tab o e =
      hornerSum (ρ.val x) (input.rows.toList.map fun r =>
        keptWeight (K := K) input.layout o *
          ∑ e ∈ Finset.range (sz o), ρ.val (r.coefficient o .main e) * tab o e) * 1 := fun o => by
    simp only [combine_kept_all ρ S g input x out h hr o]
    rw [sum_hornerSum, mul_one]
    refine congrArg _ (List.map_congr_left fun r _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp only [e1]
  rw [sum_hornerSum (Finset.range N) (ρ.val x) (fun (r : Row) o =>
    keptWeight (K := K) input.layout o *
      ∑ e ∈ Finset.range (sz o), ρ.val (r.coefficient o .main e) * tab o e) (fun _ => 1)]
  simp only [mul_one]

/-- Sums under powers add. -/
theorem hornerSum_add {α : Type} (y : K) (f f' : α → K) : ∀ l : List α,
    hornerSum y (l.map f) + hornerSum y (l.map f') = hornerSum y (l.map fun r => f r + f' r)
  | [] => by simp [hornerSum]
  | r :: l => by
    simp only [List.map_cons, hornerSum, ← hornerSum_add y f f' l]
    ring

theorem hornerSum_sub {α : Type} (y : K) (f f' : α → K) : ∀ l : List α,
    hornerSum y (l.map f) - hornerSum y (l.map f') = hornerSum y (l.map fun r => f r - f' r)
  | [] => by simp [hornerSum]
  | r :: l => by
    simp only [List.map_cons, hornerSum, ← hornerSum_sub y f f' l]
    ring

/-- What a row says of the tables, seen through the group: its coefficients applied to the main
tables of the members that are folded or kept and to the mask tables of the members with mask rows.
tab o part e: entry e of the table `part` of the oracle message o. -/
def rowSumIn (S : Statement) (L : GroupLayout) (N : ℕ) (tab : ℕ → Part → ℕ → K) (r : Row) : K :=
  (∑ o ∈ Finset.range N, foldedWeight (K := K) L o *
      ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + L.logEll)),
        ρ.val (r.coefficient o .main e) * tab o .main e) +
  (∑ o ∈ Finset.range N, maskedWeight (K := K) L o *
      ∑ e ∈ Finset.range (2 ^ (S.rowBits o .mask + L.logEllZk)),
        ρ.val (r.coefficient o .mask e) * tab o .mask e) +
  ∑ o ∈ Finset.range N, keptWeight (K := K) L o *
      ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
        ρ.val (r.coefficient o .main e) * tab o .main e

/-- What a row on a group says of the group's two tables TM, TZ and of the kept members' own main
tables. -/
def groupSum (S : Statement) (L : GroupLayout) (N : ℕ) (tab : ℕ → Part → ℕ → K) (TM TZ : ℕ → K)
    (G : GroupRow) : K :=
  (∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)), ρ.val (G.c.entry J) * TM J) +
  (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)), ρ.val (G.d.getD J zeroE) * TZ J) +
  ∑ o ∈ Finset.range N, ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
    keptSum ρ o e G.kept.toList * tab o .main e

/-- **THE BATCHED ROW's DEFECT IS THE SUM OF THE ROWS' DEFECTS UNDER THE POWERS OF x.** TM, TZ: the
group's two tables: at every index at which an oracle message has a weight they hold the entry of
that message's own table that belongs to the index. -/
theorem combine_defect (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hM : MainBlocksOk S input.layout)
    (hZ : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (N : ℕ)
    (hN : input.layout.top ≤ N) (tab : ℕ → Part → ℕ → K) (TM TZ : ℕ → K)
    (hTM : ∀ o J, mainWeight (K := K) S input.layout o J ≠ 0 →
      TM J = tab o .main (mainBack S input.layout o J))
    (hTZ : ∀ o J, maskWeight (K := K) S input.layout o J ≠ 0 →
      TZ J = tab o .mask (maskBack S input.layout o J)) :
    groupSum ρ S input.layout N tab TM TZ out - ρ.val out.target =
      hornerSum (ρ.val x) (input.rows.toList.map fun r =>
        rowSumIn ρ S input.layout N tab r - ρ.val r.target) := by
  have hr1 : ∀ r ∈ input.rows.toList, RowFits S r := fun r hm => (hr r hm).1
  unfold groupSum
  rw [combine_main_apply ρ S g input x out h hM hr1 N input.layout.logEll hN
      (fun o => tab o .main) TM hTM,
    combine_mask_apply ρ S g input x out h hZ hr N hN (fun o => tab o .mask) TZ hTZ,
    combine_kept_apply ρ S g input x out h hr1 N
      (fun o => 2 ^ (S.rowBits o .main + S.placeBits o .main)) (fun o => tab o .main),
    combine_target ρ S g input x out h hr1, hornerSum_add, hornerSum_add, hornerSum_sub]
  rfl

/-- The row names the group's members alone, and their tables have the group's numbers of places:
for each oracle message below N: on its main table: it is a member whose rows are folded, with as
many place bits as the group's main table; or a kept member; or the row has no coefficient there; on
its mask table: it is a member with mask rows, with as many place bits as the group's mask table; or
the row has no coefficient there. -/
structure NamesMembers (S : Statement) (L : GroupLayout) (N : ℕ) (r : Row) : Prop where
  main : ∀ o < N,
    (foldedWeight (K := K) L o = 1 ∧ keptWeight (K := K) L o = 0 ∧
      S.placeBits o .main = L.logEll) ∨
    (foldedWeight (K := K) L o = 0 ∧ keptWeight (K := K) L o = 1) ∨
    (foldedWeight (K := K) L o = 0 ∧ keptWeight (K := K) L o = 0 ∧
      ∀ e, ρ.val (r.coefficient o .main e) = 0)
  mask : ∀ o < N,
    (maskedWeight (K := K) L o = 1 ∧ S.placeBits o .mask = L.logEllZk) ∨
    (maskedWeight (K := K) L o = 0 ∧ ∀ e, ρ.val (r.coefficient o .mask e) = 0)

/-- **Seen through the group a row says what it says of the messages' own tables**: the row's
coefficients applied to the two tables of each oracle message below N. -/
theorem rowSumIn_eq (S : Statement) (L : GroupLayout) (N : ℕ) (tab : ℕ → Part → ℕ → K) (r : Row)
    (h : NamesMembers ρ S L N r) :
    rowSumIn ρ S L N tab r =
      ∑ o ∈ Finset.range N,
        ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
            ρ.val (r.coefficient o .main J) * tab o .main J) +
          ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
            ρ.val (r.coefficient o .mask j) * tab o .mask j) := by
  unfold rowSumIn
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o ho => ?_
  have ho' := Finset.mem_range.1 ho
  have e1 : foldedWeight (K := K) L o *
        ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + L.logEll)),
          ρ.val (r.coefficient o .main e) * tab o .main e +
      keptWeight (K := K) L o *
        ∑ e ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
          ρ.val (r.coefficient o .main e) * tab o .main e =
      ∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
        ρ.val (r.coefficient o .main J) * tab o .main J := by
    rcases h.main o ho' with ⟨a, b, c⟩ | ⟨a, b⟩ | ⟨a, b, c⟩
    · rw [a, b, c]
      ring
    · rw [a, b]
      ring
    · rw [a, b]
      simp [c]
  have e2 : maskedWeight (K := K) L o *
        ∑ e ∈ Finset.range (2 ^ (S.rowBits o .mask + L.logEllZk)),
          ρ.val (r.coefficient o .mask e) * tab o .mask e =
      ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
        ρ.val (r.coefficient o .mask j) * tab o .mask j := by
    rcases h.mask o ho' with ⟨a, c⟩ | ⟨a, c⟩
    · rw [a, c, one_mul]
    · rw [a]
      simp [c]
  linear_combination e1 + e2

end OnBytes

#print axioms OnBytes.rowSumIn_eq
#print axioms OnBytes.combine_defect
#print axioms OnBytes.combine_kept_apply
#print axioms OnBytes.combine_main_apply
#print axioms OnBytes.combine_mask_apply
#print axioms OnBytes.sum_inBlock
#print axioms OnBytes.sum_mainWeight
#print axioms OnBytes.rowMain_apply
