-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatVector.lean: what the batching of the rows on a group
(`Bat.combine`, OnBytes/Iop/Bat.lean) returns, read AT EVERY INDEX of the group's two tables and on
every oracle message's own main table, for a group of any number of members, kept or not.
Definitions, statements and proofs.

OnBytes/Iop/RowLaws.lean and MaskLaws.lean read the batched row at an index whose row lies in the
block of one member and of no other (`combine_main_member`, `combine_mask_member`), or in no
member's block (`combine_main_none`, `combine_mask_none`), and on a member that is kept
(`combine_kept`). Here nothing is asked on whose block an index lies in.
  `rowMain ρ S L N r J`, `rowMask ρ S L N r J`: what the row r weighs at the index J of the group's
    main table, of its mask table: over the oracle messages with a number below N, the message's
    weight at J (`mainWeight`, `maskWeight`: 1 or 0) times the row's coefficient
    (`Row.coefficient`) on the entry of the message's own table that belongs to J.
  `Row.mainSum_eq`, `Row.maskSum_eq`: what x times a row adds at J (`Row.mainSum`, `Row.maskSum`) is
    x times that, if no message from N on has a weight at J.
  `combine_main_all`, `combine_mask_all`: the batched row's coefficient at J reads as the sum of x^i
    times what row number i (from 0) weighs at J.
  `combine_kept_all`: the batched row's forms on the message o, at an entry, read as the sum of x^i
    times row number i's coefficient there if o is a kept member, and as 0 if it is not.
  `GroupLayout.top`: a number above every member's. `combine_main_sum`, `combine_mask_sum`: the same
    two laws without the number N, by what 1 times each row adds at J.
With `combine_target` these say the whole of the batched row from the rows, one by one.

Limits. Those of the two files named: every law has the form "if the call returns a row"; the
conditions on the layout and on the rows (MainBlocksOk, MaskBlocksOk, RowFits, MaskFits) are asked
and shown of nothing that a verifier makes. An index whose row lies in two members' blocks gets both
members' weights. Every equation is between values under a reading, which need not be one to one.
Nothing on soundness.

-/
import OnBytes.Iop.RowLaws
import OnBytes.Iop.MaskLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes
open Model

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A sum over the numbers below N of a weight times a list's summands on that number is the list's
sum of each summand under the weight of its own number, if the weight is 0 from N on. -/
theorem sum_range_pick {α : Type} (N : ℕ) (w : ℕ → K) (hN : ∀ o, N ≤ o → w o = 0) (orc : α → ℕ)
    (p : α → Prop) [DecidablePred p] (f : α → ℕ → K) : ∀ l : List α,
    ∑ o ∈ Finset.range N, w o * (l.map fun t => if orc t = o ∧ p t then f t o else 0).sum =
      (l.map fun t => if p t then w (orc t) * f t (orc t) else 0).sum
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib,
      sum_range_pick N w hN orc p f l]
    congr 1
    by_cases hp : p t
    · simp only [hp, and_true, if_true, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      by_cases hm : orc t ∈ Finset.range N
      · rw [if_pos hm]
      · rw [if_neg hm, hN _ (by simpa using hm), zero_mul]
    · simp [hp]

/-- What a row weighs at the index J of a group's main table: over the oracle messages with a number
below N, the weight of the message at J times the row's coefficient on the entry of the message's
main table that belongs to J. -/
def rowMain (S : Statement) (L : GroupLayout) (N : ℕ) (r : Row) (J : ℕ) : K :=
  ∑ o ∈ Finset.range N,
    mainWeight (K := K) S L o J * ρ.val (r.coefficient o .main (mainBack S L o J))

/-- What x times a row adds at J is x times what the row weighs there. -/
theorem Row.mainSum_eq (S : Statement) (L : GroupLayout) (N : ℕ) (x : E) (row : Row) (J : ℕ)
    (hN : ∀ o, N ≤ o → mainWeight (K := K) S L o J = 0) :
    row.mainSum ρ S L x J = rowMain ρ S L N row J * ρ.val x := by
  unfold Row.mainSum rowMain
  simp only [Row.coefficient_val, mul_add, Finset.sum_add_distrib]
  rw [sum_range_pick N _ hN (fun t : Term => t.oracle) (fun t => t.part = .main)
      (fun t o => ρ.val (t.v.entry (mainBack S L o J))),
    sum_range_pick N _ hN (fun u : Single => u.oracle) (fun u => u.part = .main)
      (fun u o => if u.index = mainBack S L o J then ρ.val u.coeff else 0),
    sum_range_pick N _ hN (fun w : Run => w.oracle) (fun w => w.part = .main)
      (fun w o => w.val ρ (mainBack S L o J)),
    sum_range_pick N _ hN (fun f : MainForm => f.oracle) (fun _ => True)
      (fun f o => ρ.val (f.c.entry (mainBack S L o J)))]
  simp only [add_mul, ← List.sum_map_mul_right, ite_mul, zero_mul, if_true]

/-- What a row weighs there is additive: a row plus x times another. -/
theorem rowMain_addScaled (S : Statement) (L : GroupLayout) (N : ℕ) (r other : Row) (x : E)
    (J : ℕ) : rowMain ρ S L N (r.addScaled other x) J =
      rowMain ρ S L N r J + rowMain ρ S L N other J * ρ.val x := by
  unfold rowMain
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Row.coefficient_addScaled]
  ring

/-- A row weighs what its structured parts and its written-out parts weigh together. -/
theorem rowMain_split (S : Statement) (L : GroupLayout) (N : ℕ) (r : Row) (J : ℕ) :
    rowMain ρ S L N r J = rowMain ρ S L N { r with units := #[], runs := #[] } J +
      rowMain ρ S L N { units := r.units, runs := r.runs } J := by
  unfold rowMain
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Row.coefficient_split ρ r]
  ring

/-- **The batched row's form on the main table, at EVERY index**: if Bat.combine returns a row, the
layout meets MainBlocksOk and every row meets RowFits: the batched row's coefficient at J reads as
the sum of x^i times what row number i (from 0) weighs at J. N: a number from which on no oracle
message has a weight at J. Nothing is asked on whose block the row of J lies in. -/
theorem combine_main_all (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MainBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r) (N J : Nat)
    (hN : ∀ o, N ≤ o → mainWeight (K := K) S input.layout o J = 0) :
    ρ.val (out.c.entry J) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      rowMain ρ S input.layout N r J) :=
  combine_read ρ S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True) (fun a => ρ.val (a.c.entry J))
    (fun r => rowMain ρ S input.layout N r J)
    (fun row y acc acc' hf _ ha => by
      refine ⟨trivial, ?_⟩
      dsimp only
      rw [addToGroupRow_main ρ S _ hL row hf y acc acc' ha J, Row.mainSum_eq ρ S _ N y row J hN])
    (fun r other y => rowMain_addScaled ρ S _ N r other y J)
    (fun r => rowMain_split ρ S _ N r J)
    trivial (Form.entry_empty ρ J) (by simp [rowMain, Row.coefficient_val])

/-! ## The mask table -/

/-- What a row weighs at the index J of a group's mask table. -/
def rowMask (S : Statement) (L : GroupLayout) (N : ℕ) (r : Row) (J : ℕ) : K :=
  ∑ o ∈ Finset.range N,
    maskWeight (K := K) S L o J * ρ.val (r.coefficient o .mask (maskBack S L o J))

/-- What x times a row adds at J is x times what the row weighs there. -/
theorem Row.maskSum_eq (S : Statement) (L : GroupLayout) (N : ℕ) (x : E) (row : Row) (J : ℕ)
    (hN : ∀ o, N ≤ o → maskWeight (K := K) S L o J = 0) :
    row.maskSum ρ S L x J = rowMask ρ S L N row J * ρ.val x := by
  unfold Row.maskSum rowMask
  simp only [Row.coefficient_val, mul_add, Finset.sum_add_distrib]
  rw [sum_range_pick N _ hN (fun t : Term => t.oracle) (fun t => t.part = .mask)
      (fun t o => ρ.val (t.v.entry (maskBack S L o J))),
    sum_range_pick N _ hN (fun u : Single => u.oracle) (fun u => u.part = .mask)
      (fun u o => if u.index = maskBack S L o J then ρ.val u.coeff else 0),
    sum_range_pick N _ hN (fun w : Run => w.oracle) (fun w => w.part = .mask)
      (fun w o => w.val ρ (maskBack S L o J))]
  simp [add_mul, ← List.sum_map_mul_right, ite_mul, zero_mul]

theorem rowMask_addScaled (S : Statement) (L : GroupLayout) (N : ℕ) (r other : Row) (x : E)
    (J : ℕ) : rowMask ρ S L N (r.addScaled other x) J =
      rowMask ρ S L N r J + rowMask ρ S L N other J * ρ.val x := by
  unfold rowMask
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Row.coefficient_addScaled]
  ring

theorem rowMask_split (S : Statement) (L : GroupLayout) (N : ℕ) (r : Row) (J : ℕ) :
    rowMask ρ S L N r J = rowMask ρ S L N { r with units := #[], runs := #[] } J +
      rowMask ρ S L N { units := r.units, runs := r.runs } J := by
  unfold rowMask
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Row.coefficient_split ρ r]
  ring

/-- **The batched row's vector on the mask table, at every index** below the table's length. -/
theorem combine_mask_all (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (N J : Nat)
    (hJ : J < 2 ^ (input.layout.h + input.layout.logEllZk))
    (hN : ∀ o, N ≤ o → maskWeight (K := K) S input.layout o J = 0) :
    ρ.val (out.d.getD J zeroE) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      rowMask ρ S input.layout N r J) :=
  combine_read ρ S g input x out h (fun r => RowFits S r ∧ MaskFits S input.layout r)
    (fun _ a => a.1) (fun _ a => ⟨a.1.structured, a.2⟩)
    (fun _ a => ⟨a.fits, by intro t ht; simp [a.terms] at ht⟩) hr
    (MaskReady input.layout) (fun a => ρ.val (a.d.getD J zeroE))
    (fun r => rowMask ρ S input.layout N r J)
    (fun row y acc acc' hf hp ha => by
      obtain ⟨p, e⟩ := addToGroupRow_mask ρ S _ hL row hf.1 hf.2 y acc acc' hp ha J hJ
      refine ⟨p, ?_⟩
      dsimp only
      rw [e, Row.maskSum_eq ρ S _ N y row J hN])
    (fun r other y => rowMask_addScaled ρ S _ N r other y J)
    (fun r => rowMask_split ρ S _ N r J)
    (Or.inl rfl) (by simp [Array.getD, ρ.zero]) (by simp [rowMask, Row.coefficient_val])

/-! ## The kept members -/

/-- **The batched row's forms on an oracle message's own main table, at every message and entry**:
the sum of x^i times the coefficient of row number i on that entry if the message is a kept member;
0 if it is not. -/
theorem combine_kept_all (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hr : ∀ r ∈ input.rows.toList, RowFits S r)
    (o idx : Nat) :
    keptSum ρ o idx out.kept.toList = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      keptWeight (K := K) input.layout o * ρ.val (r.coefficient o .main idx)) :=
  combine_read ρ S g input x out h (RowFits S) (fun _ a => a)
    (fun _ a => a.structured) (fun _ a => a.fits) hr (fun _ => True)
    (fun a => keptSum ρ o idx a.kept.toList)
    (fun r => keptWeight (K := K) input.layout o * ρ.val (r.coefficient o .main idx))
    (fun row y acc acc' hf _ ha => by
      refine ⟨trivial, ?_⟩
      dsimp only
      rw [addToGroupRow_kept ρ S _ row hf y acc acc' ha o idx])
    (fun r other y => by
      dsimp only
      rw [Row.coefficient_addScaled]
      ring)
    (fun r => by
      dsimp only
      rw [Row.coefficient_split ρ r]
      ring)
    trivial (by simp [keptSum]) (by simp [Row.coefficient_val])

/-! ## Without the number N -/

theorem le_foldrMax_of_mem : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0
  | b :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldrMax_of_mem l a h).trans (le_max_right _ _)

/-- A number above every member's. -/
def GroupLayout.top (L : GroupLayout) : ℕ := L.members.toList.foldr max 0 + 1

/-- From that number on nothing is a member. -/
theorem GroupLayout.find_top (L : GroupLayout) (o : ℕ) (h : L.top ≤ o) : L.find o = none := by
  unfold GroupLayout.find
  rw [Array.idxOf?_eq_none_iff]
  intro hm
  have := le_foldrMax_of_mem L.members.toList o (Array.mem_toList_iff.2 hm)
  unfold GroupLayout.top at h
  omega

theorem mainWeight_top (S : Statement) (L : GroupLayout) (o J : ℕ) (h : L.top ≤ o) :
    mainWeight (K := K) S L o J = 0 := by
  unfold mainWeight
  rw [L.find_top o h]

theorem maskWeight_top (S : Statement) (L : GroupLayout) (o J : ℕ) (h : L.top ≤ o) :
    maskWeight (K := K) S L o J = 0 := by
  unfold maskWeight
  rw [L.find_top o h]

/-- **The batched row's form on the main table, at every index, by the rows laid alone**: the sum of
x^i times what 1 times row number i adds at J (`Row.mainSum`). For a group of any number of
members, kept or not. -/
theorem combine_main_sum (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MainBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r) (J : Nat) :
    ρ.val (out.c.entry J) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      r.mainSum ρ S input.layout oneE J) := by
  have hN := fun o ho => mainWeight_top (K := K) S input.layout o J ho
  rw [combine_main_all ρ S g input x out h hL hr input.layout.top J hN]
  refine congrArg _ (List.map_congr_left fun r _ => ?_)
  rw [Row.mainSum_eq ρ S _ input.layout.top oneE r J hN, ρ.one, mul_one]

/-- The same on the mask table. -/
theorem combine_mask_sum (S : Statement) (g : Nat) (input : RunInput) (x : E) (out : GroupRow)
    (h : Bat.combine S g input x = some out) (hL : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (J : Nat)
    (hJ : J < 2 ^ (input.layout.h + input.layout.logEllZk)) :
    ρ.val (out.d.getD J zeroE) = hornerSum (ρ.val x) (input.rows.toList.map fun r =>
      r.maskSum ρ S input.layout oneE J) := by
  have hN := fun o ho => maskWeight_top (K := K) S input.layout o J ho
  rw [combine_mask_all ρ S g input x out h hL hr input.layout.top J hJ hN]
  refine congrArg _ (List.map_congr_left fun r _ => ?_)
  rw [Row.maskSum_eq ρ S _ input.layout.top oneE r J hN, ρ.one, mul_one]

end OnBytes

#print axioms OnBytes.combine_main_sum
#print axioms OnBytes.combine_mask_sum
#print axioms OnBytes.combine_main_all
#print axioms OnBytes.combine_mask_all
#print axioms OnBytes.combine_kept_all
