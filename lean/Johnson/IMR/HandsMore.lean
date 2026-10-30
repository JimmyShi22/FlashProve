-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
HandsMore.lean: A LIGHT FILE: KIND-FREE: IT IMPORTS HandsFence.lean ALONE: e₁ AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: THE SIXTH FIELD «more» SET APART, SO THAT IT CAN BE ASKED UNDER THE FENCE.
WHY. A share that is general in the further test E and takes «more» as a premise (hear_quiet and its like) asks it AT EVERY STATE AT WHICH X ACCEPTS. By the test that the keeper of e₁'s sheet put to every house («which part of the state does the premise's conclusion read that no public item of the promise reads at that border? alter it there») such a premise may be payable by
nobody: what a sub-protocol MAKES may want a fact along the fold. THE CURE, NO PROOF RETYPED: call the share at offNext E k (E, but «true» at border k + 1): there its premise «more» is rfl, and X at border k is X at E: so its five other fields are E's; «more» at E is then asked UNDER THE FENCE.
  offNext E k       E, but «true» at border k + 1.
  xk_offNext        X at border k does not see the turn.
  more_offNext      «more» at offNext E k: nothing to pay.
  handsR_on         HandsR Fk … (offNext E k) … · «more» at E under the fence ⟹ HandsR Fk … E ….
  handsR_on_hands   the like from Hands.
What is not claimed. Hands | HandsR at any sub-protocol. «more» at any. No soundness.
-/
import Johnson.IMR.HandsFence

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open ProofFile (Cl)

/-- E, but «true» at border k + 1. -/
def offNext (E : Nat → S → Bool) (k : Nat) : Nat → S → Bool :=
  fun j t => if j = k + 1 then true else E j t

variable {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart} {ps : List Place}
  {E : Nat → S → Bool} {ft k : Nat} {b : Block S Cl}

theorem xk_offNext (s : S) : XK N links ps (offNext E k) k s = XK N links ps E k s := by
  unfold XK offNext
  rw [if_neg (by omega)]

theorem more_offNext (s' : S) : offNext E k (k + 1) s' = true := by
  unfold offNext
  rw [if_pos rfl]

/-- **«more» under the fence.** -/
theorem handsR_on (H : HandsR Fk N links ps (offNext E k) ft k b)
    (more : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → E (k + 1) s' = true) : HandsR Fk N links ps E ft k b :=
  ⟨H.mark,
    fun s s' f hy h0 h1 hx => H.shape s s' f hy h0 h1 (by rw [xk_offNext]; exact hx),
    fun s s' f hy h0 h1 hx => H.rows s s' f hy h0 h1 (by rw [xk_offNext]; exact hx),
    fun s s' f hy h0 h1 hx => H.members s s' f hy h0 h1 (by rw [xk_offNext]; exact hx),
    fun s s' f hy h0 h1 hx => H.book s s' f hy h0 h1 (by rw [xk_offNext]; exact hx), more⟩

theorem handsR_on_hands (H : Hands N links ps (offNext E k) ft k b)
    (more : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps E k s = true → E (k + 1) s' = true) : HandsR Fk N links ps E ft k b :=
  handsR_on H.fenced more

end IM

#print axioms IM.xk_offNext
#print axioms IM.more_offNext
#print axioms IM.handsR_on
#print axioms IM.handsR_on_hands
