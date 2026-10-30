-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameFit.lean: the premise NoneBetween of the frame's ties (FrameTied.lean),
paid from the table of joints' own test on the plan's numbers (Johnson/Desc/First/BookFit.lean:
bookFit): under that test's yes the numbers of trees and of messages are the same at the two borders
of every block that tells no oracle.

  noneBetween_of_fit

Limits: BookFit.lean's: the test holds the numbers against the description's own telling; that it
says yes at a plan is a run's or a computation's to show. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTied
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.Desc.First (Numbers bookFit bookFit_at told_succ_nil)

theorem noneBetween_of_fit {N : Numbers} {ps : List Place} {told : List (List Oracle)}
    (hf : bookFit N ps told = true) {k : Nat} (hk : k < ps.length) (hn : told[k]? = some []) :
    NoneBetween N ps k := by
  have a := bookFit_at N ps told hf k (Nat.le_of_lt hk)
  have b := bookFit_at N ps told hf (k + 1) hk
  have c := told_succ_nil told k hn
  exact ⟨by rw [b.1, a.1, c.1], by rw [b.2, a.2, c.2]⟩

#print axioms noneBetween_of_fit

end Johnson.Desc.First.Walk.Tied
