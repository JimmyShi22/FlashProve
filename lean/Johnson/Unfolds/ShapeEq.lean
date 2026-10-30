-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/ShapeEq.lean: the two twins of Johnson/Unfolds/ForestTwins.lean are their routines
where the struck tests pass. Statements with their proofs; nothing is evaluated.
  `asks_ok`: the loop of tests returns where callAsk returns at every call.
  `shape_eq`: callAsk returns at every call of the array: then Forest.shape calls lid =
    Forest.shapeNoAsk calls lid (an equation of the two routines: refusals too).
  `ask_eq`: the call's written table, if there is one, has 2 ^ k words, and each of its words is
    below the prime: then Forest.callAsk c = Forest.callAskNoTab c.

Limits. Nothing on soundness.
-/
import Johnson.Unfolds.ForestTwins

set_option autoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Model

theorem asks_ok : ∀ (l : List Call), (∀ c ∈ l, Forest.callAsk c = .ok ()) →
    (forIn l PUnit.unit fun c _ => (do
      Forest.callAsk c
      pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit))) = .ok PUnit.unit
  | [], _ => rfl
  | a :: l, h => by
    rw [List.forIn_cons, h a (List.mem_cons_self ..)]
    exact asks_ok l fun c hc => h c (List.mem_cons_of_mem _ hc)

/-- **Where the tests on the calls return, the forest's numbers are made without them.** -/
theorem shape_eq (calls : Array Call) (lid : Nat)
    (h : ∀ c ∈ calls.toList, Forest.callAsk c = .ok ()) :
    Forest.shape calls lid = Forest.shapeNoAsk calls lid := by
  unfold Forest.shape Forest.shapeNoAsk
  rw [← Array.forIn_toList, asks_ok _ h]
  rfl

/-- **Where the written table is whole and below the prime, the test on a call is its test on the
numbers.** -/
theorem ask_eq (c : Call) (hs : ∀ t, c.tau = some t → t.size = 2 ^ c.k)
    (ho : ∀ x ∈ (c.tau.getD #[]).toList, okF x = true) :
    Forest.callAsk c = Forest.callAskNoTab c := by
  have e1 : (c.tau.any fun t => t.size != 2 ^ c.k) = false := by
    cases ht : c.tau with
    | none => rfl
    | some t => simp [hs t ht]
  have e2 : ((c.tau.getD #[]).any fun x => !okF x) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    rw [Array.any_eq_true'] at hh
    obtain ⟨x, hx, hn⟩ := hh
    rw [ho x (Array.mem_toList_iff.mpr hx)] at hn
    exact absurd hn (by decide)
  unfold Forest.callAsk Forest.callAskNoTab
  simp only [e1, e2, Bool.or_false]
  rfl

end Johnson.Unfolds

#print axioms Johnson.Unfolds.asks_ok
#print axioms Johnson.Unfolds.shape_eq
#print axioms Johnson.Unfolds.ask_eq
