--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/FunPin.lean: THE FUNCTIONAL PIN: the letter Pin of the row of the eight
(Johnson/Desc/K14/Law/Eight.lean: row1to8) as a term in two letters: a decoder D of the chain's own
messages and a decoder DV of the other vector.

D x: what a decoder reads off the statement x, message by message. DV x: the slot's other vector,
read off x. PinF x w: OF EVERY MESSAGE SENT SO FAR AT x (its number is below the statement's number
of messages) the witness's main words are the decoder's; and the witness's other vector is DV x.
Why "sent so far": all eight pieces have the identity as their extractor: so at a sending "the pin
goes back" must hold of one witness: a pin on ALL numbers would ask in front of the sending what the
decoder can read only behind it.
  agree_of_two   two that agree with a third agree.
  PinF           the pin.
NO RULE "the pin goes back at a yes" STANDS HERE. Asked of the decoder at EVERY statement in front
("it reads behind a block what it read in front") it is false at a decoder that reads the trees,
since a piece writes or clears every tree from its own base on. The rule stands under the border's
fence: Johnson/Desc/K14/Law/Fenced.lean, by Johnson/Desc/Sound/Fence.lean.

What is not claimed. That the decoder which is meant is a term. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Eight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame)

variable {W : Type} {F : Frame}

/-- Two that agree with a third agree. -/
theorem agree_of_two {o : Nat} {m a b : Words GE} (h1 : AgreeOn o m a) (h2 : AgreeOn o m b) :
    AgreeOn o a b := fun i => (h2 i).trans (h1 i).symm

variable (rg : W → Words GE) (wv : W → Nat → GE) (D : St × F.E.Str → Words GE)
  (DV : St × F.E.Str → Nat → GE)

/-- **The functional pin**: of every message sent so far the witness's main words are the
decoder's; the other vector is the decoder's. -/
def PinF (x : St × F.E.Str) (w : W) : Prop :=
  (∀ o, o < x.1.st.oracles.size → AgreeOn o (D x) (rg w)) ∧ wv w = DV x

end Desc.K14.Law
