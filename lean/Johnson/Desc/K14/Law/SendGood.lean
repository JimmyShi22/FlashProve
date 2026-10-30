-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SendGood.lean: the shared chain's two sendings ("send o_u", "send o_omega") in
the form of the rule of composition: what the sending kind's general law
(Johnson/Desc/K1/Law/GoodSend3.lean: send_goodIn) asks of a block holds of them, at this chain's own
record.

  sendAt_isSend   a yes of a sending at this chain's state holds a yes of the sending kind's
                  decision, and what this kind notes behind it leaves the statement.
  isSend_of_blocks   so for the second and the fifth of the eight blocks, each at the sending kind's
                  parameters that the block's own text names: that is the one premise of the general
                  law that speaks of the block.

What is not claimed. The general law is not called here: its other premises (the one Boolean on the
plan and the radii, one seed, what the first written round draws, how the words are read off the
oracles, the two premises at a yes on the borders' letters) are whoever's that lays the borders.
No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.AtBlocks
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (IsSend SameMsgs sendPiece send_goodIn Sealed sendOwn)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- **A yes of a sending at this chain's state holds a yes of the sending kind's decision.** -/
theorem sendAt_isSend (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → d'.st = d.st) :
    IsSend Q (fun s : St => s.st) (sendAt P n Q inFront groups behind) := by
  intro d d' r₁ r₂ gs h
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  have e : d'.st = x2.st := hb _ _ _ (named_some h)
  refine ⟨_, _, x2, none, ids, hx, ?_, ?_⟩
  · show SameMsgs x2.st d'.st
    rw [e]
    exact ⟨rfl, fun _ => rfl⟩
  · show d'.st.oracles.size = x2.st.oracles.size
    rw [e]

/-- The second and the fifth block are such sendings. -/
theorem isSend_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ sentU, withU P.S = some sentU ∧
      IsSend (parK1 P 2 "o_u and the first mask" sentU) (fun s : St => s.st) b2 ∧
      IsSend (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (fun s : St => s.st) b5 := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  exact ⟨sentU, hU,
    sendAt_isSend _ _ _ _ _ _ fun d ids d' h => (behindU_inv P.par d d' ids h).1,
    sendAt_isSend _ _ _ _ _ _ fun d ids d' h => (behindOmega_inv P.par d d' ids h).1⟩

end Desc.K14.Law
