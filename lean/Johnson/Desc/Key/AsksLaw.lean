-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/AsksLaw.lean: what a yes of the door's tests gives (Johnson/Desc/Key/Asks.lean): a
law a test. This file grows with the door.

Main names.
  yes_append: a yes of a longer list is a yes of the shorter.
  bytesFit_iff: `bytesFit m` says yes just where each of the seven strings of parameter bytes is
    shorter than 2 ^ 64 bytes.
  asks_bytes: a yes of the door gives that bound.
  asks_pinned: a yes of the door gives the yes of the written plan's test.
  asks_of: WHILE THE DOOR's LIST HAS TWO TESTS these two give a yes of the door. This one must be
    stated anew whenever a test is appended to the door's list.

Limits. By unfolding. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Maker OnBytes.Model.Verify

/-- **A yes of a longer list is a yes of the shorter.** -/
theorem yes_append (l l' : List (String × Bool)) (h : ∀ t ∈ l ++ l', t.2 = true) :
    ∀ t ∈ l, t.2 = true := fun t ht => h t (List.mem_append_left l' ht)

theorem bytesFit_iff (m : Johnson.G.OfPlan.Made) :
    bytesFit m = true ↔ ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 := by
  unfold bytesFit chainNames
  constructor
  · intro h n
    have h' := List.all_eq_true.1 h n (by cases n <;> simp)
    exact of_decide_eq_true h'
  · intro h
    exact List.all_eq_true.2 fun n _ => decide_eq_true (h n)

/-- **A yes of the door gives the bound on the seven strings.** -/
theorem asks_bytes {X : Public} {lay : ByteArray} {m : Johnson.G.OfPlan.Made} {F : FileDescription Xi}
    {D : WholeD} (h : ∀ t ∈ lawsAsk X lay m F D, t.2 = true) :
    ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64 :=
  (bytesFit_iff m).1 (h ("a string of its parameter bytes has 2 ^ 64 bytes or more", bytesFit m)
    (by unfold lawsAsk; simp))

/-- **A yes of the door gives the yes of the written plan's test.** -/
theorem asks_pinned {X : Public} {lay : ByteArray} {m : Johnson.G.OfPlan.Made} {F : FileDescription Xi}
    {D : WholeD} (h : ∀ t ∈ lawsAsk X lay m F D, t.2 = true) :
    PlanWritten.pinnedKeyAt m F = true :=
  h ("its rounds are not the written ones", PlanWritten.pinnedKeyAt m F)
    (by unfold lawsAsk; simp)

/-- At the door's list of two tests the bound and the written plan's test give its yes. -/
theorem asks_of (X : Public) (lay : ByteArray) (m : Johnson.G.OfPlan.Made) (F : FileDescription Xi)
    (D : WholeD) (h : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (hp : PlanWritten.pinnedKeyAt m F = true) : ∀ t ∈ lawsAsk X lay m F D, t.2 = true := by
  intro t ht
  unfold lawsAsk at ht
  rcases List.mem_cons.1 ht with rfl | ht
  · exact (bytesFit_iff m).2 h
  · obtain rfl : t = _ := List.mem_singleton.1 ht
    exact hp

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.yes_append
#print axioms VerifiableInference.Desc.Key.bytesFit_iff
#print axioms VerifiableInference.Desc.Key.asks_bytes
#print axioms VerifiableInference.Desc.Key.asks_pinned
#print axioms VerifiableInference.Desc.Key.asks_of
