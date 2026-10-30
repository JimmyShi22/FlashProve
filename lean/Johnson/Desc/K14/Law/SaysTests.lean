--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SaysTests.lean: "a row says its claim of the words" as a test with code.

  onTableE, valueE   a row applied to words given as the program's elements; val_valueE: read, it is
                     Means.value (Johnson/Desc/Means/Says.lean).
  allSayB            every row of a list says its claim; allSay_of_B: a yes gives AllSay.
  holdsAt_of_B       so HoldsAt (Johnson/Desc/K14/Law/GoodFold.lean) at a record, of the rows that
                     the record holds on a group: the state reached is the record itself.
  holdsAt_back       from a later record back, along steps onward.

Cost. valueE sums over every entry of every table of the statement: at a table of a million entries
a row takes the evaluator half a minute.

What is not claimed. The converse. That one record is onward of another: a premise of holdsAt_back.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.WalkTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- A row applied to one table of the words: computed. -/
def onTableE (S : Statement) (r : Row) (mE : Words E) (o : Nat) (part : Part) : E :=
  sumE (Means.tableSize S o part) fun i => mulE (r.coefficient o part i) (mE o part i)

/-- A row applied to the words: computed. -/
def valueE (S : Statement) (r : Row) (mE : Words E) : E :=
  sumE S.oracles.size fun o => addE (onTableE S r mE o .main) (onTableE S r mE o .mask)

theorem val_valueE (S : Statement) (r : Row) (mE : Words E) :
    ρ.val (valueE S r mE) = Means.value ρ S r (wordsOf ρ mE) := by
  unfold valueE Means.value Means.onTable onTableE
  simp only [val_sumE, ρ.add, ρ.mul]
  rfl

/-- Every row of a list says its claim of the words: computed. -/
def allSayB (S : Statement) (l : List Row) (mE : Words E) : Bool :=
  l.all fun r => decide (valueE S r mE = r.target)

theorem allSay_of_B (S : Statement) (l : List Row) (mE : Words E) (h : allSayB S l mE = true) :
    Means.AllSay ρ S l (wordsOf ρ mE) := by
  intro r hr
  simp only [allSayB, List.all_eq_true, decide_eq_true_eq] at h
  unfold Means.Says
  rw [← val_valueE, h r hr]

/-- **All constraints that the record holds on a group hold of the words**: so HoldsAt there. -/
theorem holdsAt_of_B (d : St) (g : Nat) (mE : Words E)
    (h : allSayB d.st (rowsOn d g) mE = true) : HoldsAt ρ d g (wordsOf ρ mE) :=
  ⟨d, Reaches.refl d g, allSay_of_B ρ _ _ _ h⟩

/-- From a later record back, along steps onward. -/
theorem holdsAt_back (a b : St) (g : Nat) (mE : Words E) (o : Onward a b)
    (h : allSayB b.st (rowsOn b g) mE = true) : HoldsAt ρ a g (wordsOf ρ mE) :=
  HoldsAt.back ρ o (holdsAt_of_B ρ b g mE h)

end Desc.K14.Law
