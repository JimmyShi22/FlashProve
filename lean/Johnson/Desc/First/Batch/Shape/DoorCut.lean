-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorCut.lean: THE ONE EQUATION (K9.equation and K9.door,
Johnson/Desc/First/Batch/Text.lean), CUT: when these two texts return, as one test on numbers and
marks, one named test on values, and the returns of the four texts that they call. General laws;
nothing is evaluated.

  `need_ok`, `there_ok`, `ans_bind`: when a test, a value that must be there, and two texts in a row
    return.
  `eqB L F`: nine of K9.equation's ten named tests: those that read numbers and marks alone: the
    door is walked once · the draw has run · all claims are added · all weights are taken · the
    arrays are named · the arrays are there · the slots' five sizes · the owed claims are added ·
    the slots in use are filled.
  `outsideV L F`: the tenth: A TEST ON VALUES: no array beyond the list bears a weight.
  **`equation_iff`**: K9.equation L F₀ = .ok (q, F) just if F is F₀ with the door shut, eqB and
    outsideV accept, allTerms and slotsIn return, and q is made of what they return.
  `doorB owed laid L F`: the three tests of K9.door on numbers and marks: the rows are counted · the
    link is the walk's · the moments have passed.
  **`door_iff`**: K9.door returns o just if the number of indices is laid, K9.equation returns,
    doorB accepts, asRow returns, the row fits (Ground.addRowP), and o is made of what they return.

Limits. THE FOUR TEXTS THAT ARE CALLED (allTerms, slotsIn, asRow, Ground.addRowP) ARE NOT CUT HERE:
each holds tests on numbers and tests on values. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Text

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc

theorem need_ok (n : String) (b : Bool) (u : Unit) : need n b = .ok u ↔ b = true := by
  cases b
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem there_ok {α : Type} (n : String) (x : Option α) (a : α) :
    there n x = .ok a ↔ x = some a := by
  cases x with
  | none => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | some b =>
    exact ⟨fun h => congrArg some (Except.ok.inj h), fun h => congrArg _ (Option.some.inj h)⟩

theorem ans_bind {α β : Type} (x : Ans α) (k : α → Ans β) (r : β) :
    (x >>= k) = .ok r ↔ ∃ a, x = .ok a ∧ k a = .ok r := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | ok a =>
    exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, e, h⟩ => by obtain rfl := Except.ok.inj e; exact h⟩

/-- The tests of the one equation on numbers and marks. -/
def eqB (L : LinkCtx) (F : Fork) : Bool :=
  (L.list.link && !L.list.walked && !L.done) && L.handed &&
    (F.planClaimsF != 0 && F.nClaim == F.planClaimsF) &&
    (F.kapMapF.size == F.planClaimsF && F.kapMapF.all id) &&
    (L.arrayOf.size == L.list.nt.size) && decide (L.list.nt.size ≤ F.trees.size) &&
    (decide (L.list.used ≤ F.ns) && F.gotF.size == F.ns && F.LS.size == F.ns &&
      F.vp.size == F.ns && F.mf.size == F.ns) &&
    F.owed.all (·.added) && F.gotF.all id 0 L.list.used

/-- **A test on values**: no array beyond the list bears a weight. -/
def outsideV (L : LinkCtx) (F : Fork) : Bool :=
  (F.trees.extract L.list.nt.size F.trees.size).all fun X => X.rows.all fun r => r.L.all isZeroE

theorem equation_iff (L : LinkCtx) (F₀ F : Fork) (q : Equation) :
    equation L F₀ = .ok (q, F) ↔
      F = { F₀ with doorShutF := true } ∧ eqB L F₀ = true ∧ outsideV L F₀ = true ∧
        ∃ terms mc, allTerms L { F₀ with doorShutF := true } = .ok terms ∧
          slotsIn { F₀ with doorShutF := true } = .ok mc ∧
          q = { terms := terms, onMasks := mc.1, constant := mc.2 } := by
  unfold equation
  simp only [ans_bind, need_ok, exists_const]
  unfold eqB outsideV
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, terms, ht, h8, h9, h10, mc, hm, e⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact ⟨rfl, ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h5, terms, mc, ht, hm, rfl⟩
  · rintro ⟨rfl, ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h5, terms, mc, ht, hm, rfl⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, terms, ht, h8, h9, h10, mc, hm, rfl⟩

/-- The tests of the door on numbers and marks. n: the number of indices that is laid. -/
def doorB (owed : RowsOwed) (n : Nat) (L : LinkCtx) (F : Fork) : Bool :=
  (owed == some (F.nClaim + n)) && (L.link == L.check.link) &&
    (L.check.inLink && L.check.moments == L.check.momentsDue)

theorem door_iff {X : Type} (owed : RowsOwed) (laid : Option Nat) (L : LinkCtx) (F : Fork)
    (d : St X) (o : Out X) :
    door owed laid L F d = .ok o ↔
      ∃ n q F' y d', laid = some n ∧ equation L F = .ok (q, F') ∧ doorB owed n L F' = true ∧
        asRow L.check.rows L.check.frame q d = .ok y ∧
        Ground.addRowP y.2 L.check.group y.1 = some d' ∧
        o = { owed := none, L := L, F := F', d := d' } := by
  unfold door
  simp only [ans_bind, need_ok, there_ok, exists_const]
  unfold doorB
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨n, hn, ⟨q, F'⟩, hq, h1, h2, h3, y, hy, d', hd, e⟩
    exact ⟨n, q, F', y, d', hn, hq, ⟨⟨h1, h2⟩, h3⟩, hy, hd, (Except.ok.inj e).symm⟩
  · rintro ⟨n, q, F', y, d', hn, hq, ⟨⟨h1, h2⟩, h3⟩, hy, hd, rfl⟩
    exact ⟨n, hn, (q, F'), hq, h1, h2, h3, y, hy, d', hd, rfl⟩

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.equation_iff
#print axioms VerifiableInference.Desc.K9.Shape.door_iff
