-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendAsksB.lean: A DEFINITION WITH CODE AND A THEOREM. **The four tests that the law of a sending asks at a seat of the key file's first chain (SendAsks: KeySendAtDesc.lean), as ONE Boolean; its yes
gives the structure by theorem.** Cut out of KeySendAsks.lean (not in this library), whose ride imports a yard: this file imports laws alone.
OBJECT. K1's numbers Q at a sending. USER. Johnson/RunOne/KeySendFull.lean calls asksB | asks_of_B; whoever lays the asks into a door of tests on public data; the ride KeySendAsks.lean (not in this library). LETTERS. K · Q · rad.
  asksB         decide (seeds = 1) && decide (every sampled message meets the library's test at its radius) && shareB K && belowB K
  asks_of_B     asksB K Q rad = true → SendAsks K Q rad
Nothing on soundness.

-/
import Johnson.RunOne.KeySendAtDesc

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params Johnson.Pack Johnson.RunOne.KeySendErr
open VerifiableInference.Desc.K1 (Par shapeAt sampledAt)

def asksB (K : Nat) (Q : Par) (rad : Nat → Nat) : Bool :=
  decide (Q.seeds = 1) && decide (∀ k, sampledAt Q k → meetsB Q.codes (shapeAt Q k) (rad k.val) = true) && shareB K Q rad && belowB K Q

theorem asks_of_B {K : Nat} {Q : Par} {rad : Nat → Nat} (h : asksB K Q rad = true) : SendAsks K Q rad := by
  unfold asksB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.asks_of_B
