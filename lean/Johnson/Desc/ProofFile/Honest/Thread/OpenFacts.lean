-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/OpenFacts.lean: two facts on the library's table of open items
at the full size (`openSets`, Johnson/Desc/First/Borders.lean, at the written lists `P5J.At.links`
and `P5J.At.ps`). They read no state and no public file. Each is one test with code that the kernel
evaluates, and a lemma that reads the fact off the test. HeadFences.lean takes the two facts as
hypotheses. No definition.

  1  `open_pin_of_row_B`, `open_pin_of_row`   at every border at which the item `row m (sample t)`
     is open, the item `pin m t` is open
  2  `open_pinI_B`, `open_pinI`   the item `pinI` is open at every border from 3 to 358
  3  `open_controls`   both tests can fail: the first rejects if it asks for the pin of the next
     moment; `pinI` is not open at border 2

Limits.
  * Full size only.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (Item openSets start)

/-! ## 1 Where a class of sample rows is open, its pin is open -/

set_option maxRecDepth 1000000 in
/-- By the kernel: one walk over the open sets accepts. -/
theorem open_pin_of_row_B :
    ((openSets P5J.At.links P5J.At.ps (start P5J.At.links)).all fun O =>
      O.all fun i => match i with
        | .row m (.sample t) => O.contains (Item.pin m t)
        | _ => true) = true := by decide +kernel

/-- Where `row m (sample t)` is open, `pin m t` is open. -/
theorem open_pin_of_row {b m t : Nat}
    (h : Item.row m (.sample t) ∈
      ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD []) :
    Item.pin m t ∈ ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD [] := by
  cases hO : (openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]? with
  | none =>
    rw [hO] at h
    cases h
  | some O =>
    rw [hO] at h
    have h1 := List.all_eq_true.1 open_pin_of_row_B O (List.mem_of_getElem? hO)
    have h2 : O.contains (Item.pin m t) = true := List.all_eq_true.1 h1 _ h
    exact List.contains_iff_mem.1 h2

/-! ## 2 `pinI` is open from border 3 on -/

set_option maxRecDepth 1000000 in
/-- By the kernel. -/
theorem open_pinI_B :
    ((List.range 356).all fun j =>
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[j + 3]?).getD []).contains
        Item.pinI) = true := by
  decide +kernel

/-- `pinI` is open at every border from 3 to 358. -/
theorem open_pinI {b : Nat} (h3 : 3 ≤ b) (h : b ≤ 358) :
    Item.pinI ∈ ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD [] := by
  obtain ⟨j, rfl⟩ : ∃ j, b = j + 3 := ⟨b - 3, by omega⟩
  exact List.contains_iff_mem.1
    (List.all_eq_true.1 open_pinI_B j (List.mem_range.2 (by omega)))

/-! ## 3 Both tests can fail -/

set_option maxRecDepth 1000000 in
/-- By the kernel: the first test rejects if it asks for the pin of the next moment, and `pinI` is
not open at border 2. -/
theorem open_controls :
    ((openSets P5J.At.links P5J.At.ps (start P5J.At.links)).all fun O =>
        O.all fun i => match i with
          | .row m (.sample t) => O.contains (Item.pin m (t + 1))
          | _ => true,
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[2]?).getD []).contains Item.pinI) =
      (false, false) := by decide +kernel

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.open_pin_of_row_B
#print axioms ProofFile.Honest.FirstThread.open_pin_of_row
#print axioms ProofFile.Honest.FirstThread.open_pinI_B
#print axioms ProofFile.Honest.FirstThread.open_pinI
#print axioms ProofFile.Honest.FirstThread.open_controls
