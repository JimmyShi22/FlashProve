-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2/RowsCanMeans.lean: the kind «the code switch»: WHAT A YES OF [G33]'s TEST
MEANS. NO BLOCK IMPORTS THIS FILE.
K2/RowsCan.lean's rowsCan is a yes-or-no test with code: eight clauses, some of them on what a
prover sent (the symbols read, the old claim, the old sample rows) and on what was drawn (the
positions).
Here the eight facts stand as one proposition, RowsCan, written with «for all», «is a member of»,
«=» and «<», without a loop or an index; and rowsCan_iff_facts proves that the test says yes just
where they hold.
One default value is left, in the field samples: «S.oracles.getD o default»: a kept member that the
statement lacks counts as a message without sample rows, as in the maker's own text
(OnBytes/Iop/Cs.lean: switchOldSamples).
  ReadsMainOf o row     every term, single entry and run of the row is on the main table of the
  message o, and every whole form is on o
  readsMainOf_iff       the test readsMainOf says yes just there
  RowsCan …             the eight facts, each a named field
  rowsCan_iff_facts     rowsCan … = true ⇔ RowsCan …
(The name rowsCan_iff is taken: K2/RowsMadeAgree.lean's theorem of that name says that the test says
yes just where the program's maker switchRows returns rows.)
No soundness is claimed: this says what one test checks, not that the check suffices for anything.
-/
import Johnson.Top.H0.Tw.K2.RowsCan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

/-! ### four small tools on arrays -/

theorem memL {α : Type} {a : Array α} {x : α} : x ∈ a.toList ↔ x ∈ a := by simp

theorem arrAll {α : Type} (a : Array α) (p : α → Bool) : a.all p = true ↔ ∀ x ∈ a, p x = true := by
  rw [← Array.all_toList, List.all_eq_true]
  exact ⟨fun h x hx => h x (memL.2 hx), fun h x hx => h x (memL.1 hx)⟩

theorem getDAt (a : Array Nat) {i : Nat} (hi : i < a.size) : a.getD i noId = a[i] := by simp [hi]

/-- A test asked at every index of an array of numbers is asked of every member. -/
theorem rangeAll (a : Array Nat) (p : Nat → Bool) :
    ((List.range a.size).all fun i => p (a.getD i noId)) = true ↔ ∀ o ∈ a, p o = true := by
  rw [List.all_eq_true]
  constructor
  · intro h o ho
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ho
    have := h i (List.mem_range.2 hi)
    rwa [getDAt a hi] at this
  · intro h i hi
    have hi' := List.mem_range.1 hi
    rw [getDAt a hi']
    exact h _ (Array.getElem_mem hi')

/-- «Some index holds v» is «v is a member». -/
theorem rangeAny (a : Array Nat) (v : Nat) :
    ((List.range a.size).any fun i => a.getD i noId == v) = true ↔ v ∈ a := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨i, hi, he⟩
    have hi' := List.mem_range.1 hi
    rw [getDAt a hi'] at he
    rw [← beq_iff_eq.1 he]
    exact Array.getElem_mem hi'
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
    exact ⟨i, List.mem_range.2 hi, by rw [getDAt a hi]; exact beq_self_eq_true _⟩

/-- «It has an index in the list» is «it is a member». -/
theorem idxSome (a : Array Nat) (x : Nat) : (a.idxOf? x).isSome = true ↔ x ∈ a := by simp

/-! ### the proposition -/

/-- The row reads the main table of the message o and nothing else. -/
def ReadsMainOf (o : Nat) (row : Row) : Prop :=
  (∀ t ∈ row.terms, t.oracle = o ∧ t.part = Part.main) ∧
    (∀ u ∈ row.units, u.oracle = o ∧ u.part = Part.main) ∧
    (∀ r ∈ row.runs, r.oracle = o ∧ r.part = Part.main) ∧
    ∀ f ∈ row.forms, f.oracle = o

theorem readsMainOf_iff {o : Nat} {row : Row} : readsMainOf o row = true ↔ ReadsMainOf o row := by
  unfold readsMainOf ReadsMainOf
  simp only [Bool.and_eq_true, arrAll, beq_iff_eq, and_assoc]

/-- **What [G33] checks: the eight facts.** S: the statement as it stands behind the joins · old:
the old complex of single rows with its one linear claim · T: the switch's target · anew: the new
messages that take the kept members' rows ·
pos: the positions drawn · y: the symbols read at them.
switchKept old, which stands in three fields, is the program's plain reading of the old complex's
layout (OnBytes/Iop/Cs.lean:118): the members that the layout marks as kept, in the order of
sending; it tests nothing and cannot fail. -/
structure RowsCan (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos :
    Positions) (y : Array E) : Prop where
  /-- there is one symbol for each row of the old complex at each position of the list -/
  symbols : y.size = pos.all.size * old.rows
  /-- the old main code is in the statement's list -/
  oldCode : old.code < S.codes.base.size
  /-- the old mask code is in the statement's list -/
  oldMask : old.maskCode < S.codes.mask.size
  /-- g's main code is in the statement's list -/
  newCode : T.shape.code < S.codes.base.size
  /-- there is one new message for each kept member -/
  messages : anew.size = (switchKept old).size
  /-- the old claim reads kept members of the old group alone -/
  claim : ∀ f ∈ old.kept, f.oracle ∈ switchKept old
  /-- each kept member's old sample rows read that member's main table and nothing else -/
  samples : ∀ o ∈ switchKept old, ∀ row ∈ (S.oracles.getD o default).sampleRows, ReadsMainOf o row
  /-- each draw is among the positions of the list by which the trees are opened -/
  draws : ∀ x ∈ pos.draws, x ∈ pos.all

/-- **The test says yes just where the eight facts hold.** -/
theorem rowsCan_iff_facts {S : Statement} {old : SingleRows} {T : SwitchTarget} {anew : Array Nat}
    {pos : Positions} {y : Array E} :
    rowsCan S old T anew pos y = true ↔ RowsCan S old T anew pos y := by
  simp only [rowsCan, rowsCanL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨beq_iff_eq.1 h1, h2, h3, h4, beq_iff_eq.1 h5, ?_, ?_, ?_⟩
    · intro f hf
      exact (rangeAny _ _).1 ((List.all_eq_true.1 h6) f (memL.2 hf))
    · intro o ho row hr
      have := (rangeAll (switchKept old) fun o =>
          (S.oracles.getD o default).sampleRows.toList.all (readsMainOf o)).1 h7 o ho
      exact readsMainOf_iff.1 ((List.all_eq_true.1 this) row (memL.2 hr))
    · intro x hx
      exact (idxSome _ _).1 ((List.all_eq_true.1 h8) x (memL.2 hx))
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨beq_iff_eq.2 h1, h2, h3, h4, beq_iff_eq.2 h5, ?_, ?_, ?_⟩
    · exact List.all_eq_true.2 fun f hf => (rangeAny _ _).2 (h6 f (memL.1 hf))
    · exact (rangeAll (switchKept old) fun o =>
        (S.oracles.getD o default).sampleRows.toList.all (readsMainOf o)).2 fun o ho =>
        List.all_eq_true.2 fun row hr => readsMainOf_iff.2 (h7 o ho row (memL.1 hr))
    · exact List.all_eq_true.2 fun x hx => (idxSome _ _).2 (h8 x (memL.1 hx))

end Tw.K2

#print axioms Tw.K2.readsMainOf_iff
#print axioms Tw.K2.rowsCan_iff_facts
