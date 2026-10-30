-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Last/TwoTestsAtEnd.lean: TWO TESTS ON A REACHED STATE OF THE FIRST CHAIN, FROM TWO FIELDS OF
`First.FoldFacts` (Johnson/Desc/First/FoldFacts.lean). Three theorems.

Why. `ToldDesc.ownSitsB_last_bools` (Johnson/ToldDescR/OwnSitsBools.lean) asks, in its premise hTwo, four
things of every state reached at border 357. Two are counts. The other two are the tests
`K12.Door.seatsCarriedB L s.book` (the book's places are the listed seats, as far as the book goes) and
`K12.Door.msgShapesB M s.st` (the statement's oracle messages have the listed shapes, as far as they
go). These two are what `FoldFacts`' fields seatsCarried and msgShapes say, by the definitions of
`atFirstSeats` and `atFirstShapes`, at L := d.L and M := d.M.

  `two_tests_of_facts`: at every border k, for any family Rc of pairs (public part, state) each of
    whose members is read off a member of the facts' own family (hR).
  `two_tests_at_reach`: the case in which the facts are stated of the family itself.
  `two_tests_at_rchAt`: the case in which the facts are stated of statements that carry something
    beside the pair (the oracles' strings), read by `Prod.fst`; one such thing y₀ must be at hand.

Limits. The states are those without a failure mark: the two fields say nothing of a marked state. It
pays neither of hTwo's two counts. `FoldFacts` stays a premise: nothing here shows that it holds.
That d.L and d.M are the lists at which the tests on the plan (`ToldDesc.PlanSits`) accept is not
said here. No soundness follows from it. Nothing on hiding.

-/
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (FoldData FoldFacts ModelPart)
open VerifiableInference.Desc.K12.Door (seatsCarriedB msgShapesB)

variable {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × First.S} {d : FoldData}
  {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}

/-- **The two tests at a reached state without a mark, from the facts along the fold.** -/
theorem two_tests_of_facts (FF : FoldFacts Rch at_ d reqW links ps)
    {Rc : ℕ → P × First.S → Prop}
    (hR : ∀ k z s, Rc k (z, s) → ∃ a, Rch k a ∧ at_ a = (z, s)) :
    ∀ k z s, Rc k (z, s) → s.failed = none →
      seatsCarriedB d.L s.book = true ∧ msgShapesB d.M s.st = true := by
  intro k z s h hm
  obtain ⟨a, ha, e⟩ := hR k z s h
  have hm' : (at_ a).2.failed = none := by rw [e]; exact hm
  have h1 := FF.seatsCarried k a ha hm'
  have h2 := FF.msgShapes k a ha hm'
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- The facts stated of the family of pairs itself. -/
theorem two_tests_at_reach {Rc : ℕ → P × First.S → Prop}
    (FF : FoldFacts Rc (fun q => q) d reqW links ps) :
    ∀ k z s, Rc k (z, s) → s.failed = none →
      seatsCarriedB d.L s.book = true ∧ msgShapesB d.M s.st = true :=
  two_tests_of_facts FF fun _ z s h => ⟨(z, s), h, rfl⟩

/-- The facts stated of statements that carry something beside the pair. -/
theorem two_tests_at_rchAt {Str : Type} (y₀ : Str) {Rc : ℕ → P × First.S → Prop}
    (FF : FoldFacts (fun k (a : (P × First.S) × Str) => Rc k a.1) Prod.fst d reqW links ps) :
    ∀ k z s, Rc k (z, s) → s.failed = none →
      seatsCarriedB d.L s.book = true ∧ msgShapesB d.M s.st = true :=
  two_tests_of_facts FF fun _ z s h => ⟨((z, s), y₀), h, rfl⟩

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.two_tests_of_facts
#print axioms VerifiableInference.Desc.Last.two_tests_at_reach
#print axioms VerifiableInference.Desc.Last.two_tests_at_rchAt
