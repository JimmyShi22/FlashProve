-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/Order.lean: THE ORDER OF A SEGMENT'S RUNS: what
Johnson/Desc/Block.lean's own test on the order (`orderOk`, `orderAfterOk`) catches. Theorems. It
imports Block.lean alone: nothing here speaks of a driver.

Why. A hearing block states runs of claims, and runs behind the batching, each under a name. A
segment's order lists which run of which block is taken when. Block.lean holds the order against the
blocks' own statements (`namesOk`): no name twice; every stated run stands in the order just once;
AND THE ORDER NAMES NO OTHER. The last clause is read out here.

What is said.
  `namesOk_covers`, `orderOk_covers`, `orderAfterOk_covers`: **where Block's test says yes, every
    run that the order names is stated by the block that it names.**
  `orderOk_rings_on_less`, `orderAfterOk_rings_on_less`: **one run that the order names and that the
    block of its number does not state (or no block has that number): the test says no.**
    `laid_refuses_less`, `laid_refuses_less_after`: and then the first block of the segment's flat
    list fails its test on the plan.
So a segment that is handed the protocol's own order is refused as soon as one listed run is stated
by no block. A driver that first cuts the order down to what its blocks state silences this clause;
one that lays the order uncut does not.

Not here. The other half of `namesOk` (a stated run that the order does not name). What a driver
lays: Johnson/Desc/First/Driver/.

Limits. On names and numbers of runs alone: nothing on what a run does. «Refused» is of the tests on
the plan: nothing on a run of the verifier. Nothing on soundness.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Shape

variable {S Cl : Type}

/-- Where the test says yes, the order names no run that is not there. -/
theorem namesOk_covers {all order : List (Nat × String)} (h : namesOk all order = true) :
    ∀ o ∈ order, o ∈ all := by
  unfold namesOk at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact fun o ho => List.contains_iff_mem.1 (h.2 o ho)

/-- A run stands in the list of all runs just if the block of that number states it. -/
theorem mem_runs_iff {α : Type} (f : Block S Cl → List (String × α)) (bs : List (Block S Cl))
    (o : Nat × String) :
    (o ∈ bs.zipIdx.flatMap fun b => (f b.1).map fun c => (b.2, c.1)) ↔
      ∃ b, bs[o.1]? = some b ∧ o.2 ∈ (f b).map (·.1) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨⟨b, i⟩, hb, ho⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    exact ⟨b, List.mem_zipIdx_iff_getElem?.1 hb, List.mem_map.2 ⟨c, hc, rfl⟩⟩
  · rintro ⟨b, hb, ho⟩
    obtain ⟨c, hc, e⟩ := List.mem_map.1 ho
    exact ⟨(b, o.1), List.mem_zipIdx_iff_getElem?.2 hb, List.mem_map.2 ⟨c, hc, by rw [e]⟩⟩

/-- **WHERE `orderOk` SAYS YES, EVERY RUN THAT THE ORDER NAMES IS STATED BY ITS BLOCK.** -/
theorem orderOk_covers {bs : List (Block S Cl)} {order : List (Nat × String)}
    (h : orderOk bs order = true) :
    ∀ o ∈ order, ∃ b, bs[o.1]? = some b ∧ o.2 ∈ b.claims.map (·.1) :=
  fun o ho => (mem_runs_iff (·.claims) bs o).1 (namesOk_covers h o ho)

theorem orderAfterOk_covers {bs : List (Block S Cl)} {order : List (Nat × String)}
    (h : orderAfterOk bs order = true) :
    ∀ o ∈ order, ∃ b, bs[o.1]? = some b ∧ o.2 ∈ b.after.map (·.1) :=
  fun o ho => (mem_runs_iff (·.after) bs o).1 (namesOk_covers h o ho)

/-- **IT RINGS ON LESS**: one run that the order names and its block does not state: no. -/
theorem orderOk_rings_on_less {bs : List (Block S Cl)} {order : List (Nat × String)}
    {o : Nat × String} (ho : o ∈ order)
    (hn : ∀ b, bs[o.1]? = some b → o.2 ∉ b.claims.map (·.1)) : orderOk bs order = false := by
  cases h : orderOk bs order with
  | false => rfl
  | true =>
    obtain ⟨b, hb, hm⟩ := orderOk_covers h o ho
    exact absurd hm (hn b hb)

theorem orderAfterOk_rings_on_less {bs : List (Block S Cl)} {order : List (Nat × String)}
    {o : Nat × String} (ho : o ∈ order)
    (hn : ∀ b, bs[o.1]? = some b → o.2 ∉ b.after.map (·.1)) : orderAfterOk bs order = false := by
  cases h : orderAfterOk bs order with
  | false => rfl
  | true =>
    obtain ⟨b, hb, hm⟩ := orderAfterOk_covers h o ho
    exact absurd hm (hn b hb)

/-- So a segment whose order names a run that no block states fails the test on the plan that the
first block of its flat list holds. -/
theorem laid_refuses_less (L : Link S Cl) {o : Nat × String} (ho : o ∈ L.order)
    (hn : ∀ b, L.hear[o.1]? = some b → o.2 ∉ b.claims.map (·.1)) :
    (L.blocksInOrder.head?.map (·.planOk)) = some false := by
  have h := orderOk_rings_on_less ho hn
  simp [Link.blocksInOrder, h]

/-- The like of a run behind the batching. -/
theorem laid_refuses_less_after (L : Link S Cl) {o : Nat × String} (ho : o ∈ L.orderAfter)
    (hn : ∀ b, L.hear[o.1]? = some b → o.2 ∉ b.after.map (·.1)) :
    (L.blocksInOrder.head?.map (·.planOk)) = some false := by
  have h := orderAfterOk_rings_on_less ho hn
  simp [Link.blocksInOrder, h]

end VerifiableInference.Desc.Shape

#print axioms VerifiableInference.Desc.Shape.namesOk_covers
#print axioms VerifiableInference.Desc.Shape.mem_runs_iff
#print axioms VerifiableInference.Desc.Shape.orderOk_covers
#print axioms VerifiableInference.Desc.Shape.orderAfterOk_covers
#print axioms VerifiableInference.Desc.Shape.orderOk_rings_on_less
#print axioms VerifiableInference.Desc.Shape.orderAfterOk_rings_on_less
#print axioms VerifiableInference.Desc.Shape.laid_refuses_less
#print axioms VerifiableInference.Desc.Shape.laid_refuses_less_after
