-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkOutOfRead.lean: a chain that the verifier program's strict reader has read passes
the test that every word of a field's element is below the prime (`okOut`,
OnBytes/Maker/OkOut.lean), at any function for the hash.

Statements and proofs. No premise but the reading. The weight is `readX_below`
(OnBytes/Maker/OkWordsOfRead.lean): round by round, the items' words and the words of every opened
column of a chain that was read are below the prime. Here that is carried to the test.

Main theorems.
  `RoundBelow.okRoundOut`   a round whose words are below the prime passes.
  `okOut_of_readX`          at the strict reader, at any function for the hash.

What is not claimed. Nothing on a value that has passed no reader. Nothing on a reader that is not
the library's. Nothing on soundness.


-/
import OnBytes.Maker.OkOut
import OnBytes.Maker.OkWordsOfRead

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run

theorem RoundBelow.okRoundOut {ro : Fmt.RoundOut} (H : RoundBelow ro) :
    OnBytes.Maker.okRoundOut ro = true := by
  unfold OnBytes.Maker.okRoundOut
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun x hx => (H.1 x hx).okGot, fun y hy => List.all_eq_true.2 fun c hc =>
    List.all_eq_true.2 fun w hw => (H.2 y hy c hc w hw).okF⟩

/-- **A chain that the strict reader has read passes the test on the words**, at any function for
the hash. -/
theorem okOut_of_readX (h : HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    okOut o = true :=
  List.all_eq_true.2 fun ro hro => (readX_below h S seen b i o j e ro hro).okRoundOut

end OnBytes.Maker
