-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/RowHoldsSays.lean: Theorems; one definition of Prop.
"A ROW HOLDS": TWO TEXTS OF ONE NOTION, IN TWO FILES, SHOWN TO BE ONE. RowHolds
(Johnson/Desc/Key/KeyWords.lean: the program's machine sums over 2 ^ tableBits entries of BOTH parts
of EVERY message of the statement, "is" being the letter same) and Means.Says
(Johnson/Desc/Means/Says.lean: sums in a commutative ring over Means.tableSize entries: 2 ^
tableBits where the statement HAS that table, 0 where it has not). They part at a table that is not
there.
  OffTables ρ St r            the row reads as 0 on every table that the statement has not.
  table_read                  one table: the machine sum reads as the ring's sum over the table.
  rowHolds_iff_says           **UNDER OffTables THE TWO TEXTS ARE ONE**: RowHolds at same := "ρ a = ρ b" ↔ Means.Says at the words "ρ of val": any row, any statement, any val.
  has_of_placeOk              a summand that fits its place (Blk.placeOk) is on a table that the statement has.
  offTables_of_rowIn          **A ROW THAT HAS PASSED THE ADDING's TESTS (Means.RowIn, at any group) MEETS OffTables.**
  rowHolds_iff_says_of_rowIn  the two joined.
This is the one text of the lemma.
AT SILLY MEMBERS. The row without a summand meets OffTables at every statement; both texts then say "0 reads as the target". A row with a term on a message's mask table, at a statement in which that message has no mask rows, does not meet OffTables (unless the term reads 0): there RowHolds counts the entry at index 0 and Says counts nothing: the iff is not claimed, and RowIn refuses such a row.
What is not claimed: that a row meets RowIn; that either text is what a protocol means. Nothing on soundness, on an honest prover or on hiding.
Axioms: rowHolds_iff_says · offTables_of_rowIn · rowHolds_iff_says_of_rowIn each on
propext · Classical.choice · Quot.sound.
-/
import Johnson.Desc.Key.KeySumRead
import Johnson.Desc.Means.Says
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

/-- The row reads as 0 on every table that the statement has not. -/
def OffTables (St : Statement) (r : OnBytes.Row) : Prop :=
  ∀ o pt i, St.has o pt = false → ρ.val (r.coefficient o pt i) = 0

/-- One table: the machine sum over 2 ^ tableBits entries reads as the ring's sum over the table. -/
theorem table_read (St : Statement) (val : Nat → Part → Nat → E) (r : OnBytes.Row)
    (hoff : OffTables ρ St r) (o : Nat) (pt : Part) :
    ρ.val (sumE (2 ^ St.tableBits o pt) fun i => mulE (r.coefficient o pt i) (val o pt i)) =
      Means.onTable ρ St r (fun o pt i => ρ.val (val o pt i)) o pt := by
  rw [sumE_read ρ.val ρ.zero ρ.add]
  unfold Means.onTable Means.tableSize
  cases hh : St.has o pt with
  | true =>
    rw [if_pos rfl]
    exact Finset.sum_congr rfl fun i _ => ρ.mul _ _
  | false =>
    rw [if_neg (by simp), Finset.range_zero, Finset.sum_empty]
    exact Finset.sum_eq_zero fun i _ => by rw [ρ.mul, hoff o pt i hh, zero_mul]

/-- **Under OffTables the two texts of "a row holds" are one.** -/
theorem rowHolds_iff_says (St : Statement) (val : Nat → Part → Nat → E) (r : OnBytes.Row)
    (hoff : OffTables ρ St r) :
    RowHolds (fun a b => ρ.val a = ρ.val b) St val r ↔
      Means.Says ρ St r fun o pt i => ρ.val (val o pt i) := by
  unfold RowHolds Means.Says Means.value
  beta_reduce
  rw [sumE_read ρ.val ρ.zero ρ.add]
  have e : ∀ o ∈ Finset.range St.oracles.size,
      ρ.val (addE (sumE (2 ^ St.tableBits o .main) fun i =>
          mulE (r.coefficient o .main i) (val o .main i))
        (sumE (2 ^ St.tableBits o .mask) fun i =>
          mulE (r.coefficient o .mask i) (val o .mask i))) =
      Means.onTable ρ St r (fun o pt i => ρ.val (val o pt i)) o .main +
        Means.onTable ρ St r (fun o pt i => ρ.val (val o pt i)) o .mask := fun o _ => by
    rw [ρ.add, table_read ρ St val r hoff o .main, table_read ρ St val r hoff o .mask]
  rw [Finset.sum_congr rfl e]

/-- A summand that fits its place is on a table that the statement has. -/
theorem has_of_placeOk (S : Statement) (G : OnBytes.Group) (o : Nat) (pt : Part) (vars index : Nat)
    (h : Blk.placeOk S G o pt vars index = true) : S.has o pt = true := by
  simp only [Blk.placeOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem sum_map_zero_of {α : Type} (l : List α) (f : α → K) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), add_zero]

/-- **A row that has passed the adding's tests reads as 0 on every table that is not there.** -/
theorem offTables_of_rowIn (S : Statement) (G : OnBytes.Group) (row : OnBytes.Row)
    (h : Means.RowIn S G row) : OffTables ρ S row := by
  intro o pt i hh
  have no : ∀ o' pt', S.has o' pt' = true → ¬ (o' = o ∧ pt' = pt) := by
    rintro o' pt' h1 ⟨rfl, rfl⟩
    rw [hh] at h1
    cases h1
  rw [Row.coefficient_val, sum_map_zero_of, sum_map_zero_of, sum_map_zero_of, sum_map_zero_of]
  · simp
  · intro f hf
    refine if_neg fun e => ?_
    exact no f.oracle .main (has_of_placeOk _ _ _ _ _ _ (h.forms f hf).1) ⟨e.1, e.2.symm⟩
  · intro w hw
    exact if_neg (no w.oracle w.part (has_of_placeOk _ _ _ _ _ _ (h.runs w hw).2.2))
  · intro u hu
    exact if_neg (no u.oracle u.part (has_of_placeOk _ _ _ _ _ _ (h.units u hu)))
  · intro t ht
    exact if_neg (no t.oracle t.part (has_of_placeOk _ _ _ _ _ _ (h.terms t ht)))

/-- The two joined. -/
theorem rowHolds_iff_says_of_rowIn (S : Statement) (G : OnBytes.Group) (val : Nat → Part → Nat → E)
    (row : OnBytes.Row) (h : Means.RowIn S G row) :
    RowHolds (fun a b => ρ.val a = ρ.val b) S val row ↔
      Means.Says ρ S row fun o pt i => ρ.val (val o pt i) :=
  rowHolds_iff_says ρ S val row (offTables_of_rowIn ρ S G row h)

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.rowHolds_iff_says
#print axioms VerifiableInference.Desc.Key.offTables_of_rowIn
#print axioms VerifiableInference.Desc.Key.rowHolds_iff_says_of_rowIn
