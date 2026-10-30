-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeySendsFive.lean: the key file's five of sendsFrom, at the written
values, in the letters of sendsFrom_one (Johnson/G/SendsListed.lean): what wSend and
linSharedSends return at the typed shape, by name, and that the inner routine
Johnson.G.oneOf returns the three written lists keySendsFull.1 | .2.1 | .2.2.
It serves the join over the ledger sendsFrom_of_parts.

WHAT IS SAID.
  wListedOf S · sharedListedOf S a   what wSend S and linSharedSends S a return WHERE THEY RETURN,
                   by formula: their own texts with «getD» in the place of the refusing arm.
  wSend_is · linShared_is   general in S: a return is that value.
  keyW · keyShared   the two values at the typed shape keyFull.once.shape (and the written
                   setting's number of samples).
  ok_of_sendIs     sendIs's yes opened: the made list returned, and it is the written one: by
                   PlanWritten.sameChain_eq.
  keyW_at · keyShared_at   **the two returns, with their values by name.**
  keySendsFive_written   **the five.**
  keySendsFive_at_W      the same five in the ledger's own letters, at W := writtenMade.at
                   Hung.none: the tie is by rfl.
HOW. Calls alone: NOTHING IS ASKED OF THE KERNEL HERE: the three closed facts key0_send |
key1_send | key2_send (IMR/KeySend0 | 1 | 2.lean) stand; IM.oneSend is Johnson.G.oneOf by
IM.oneSend_is_oneOf (rfl).
What is not claimed. Anything on the entry chain's or the proof file's four. That sendsFrom returns
at what the planner makes. No soundness.

-/
import Johnson.IMR.KeySend0
import Johnson.IMR.KeySend1
import Johnson.IMR.KeySend2
import Johnson.IMR.KeySendsKin
import Johnson.Desc.Ok.PlanWritten.SendsTestLaws
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Params
open Johnson.G Johnson.G.MadeFree
open VerifiableInference VerifiableInference.Number.ByRuns
open VerifiableInference.PlanWritten.Joined (writtenMade)
open Lk6.AtPlan (keyFull)

/-- What wSend returns where it returns. -/
def wListedOf (S : LinShape) : Listed := ⟨"W", ((linMessageW S).getD #[]).toList⟩

/-- What linSharedSends returns where it returns. -/
def sharedListedOf (S : LinShape) (answers : Nat) : List Listed :=
  [⟨"the folded row", ((linMessageU S).getD #[]).toList⟩, ⟨"Omega", (linMessageOmega S).toList⟩] ++
    ioppSends "the folded row's test" answers S.choice.masksRide 1 S.testU ++
    (if S.sharedSplitNeeded then ioppSends "Omega's test" answers S.choice.masksRide 1 S.testOmega
     else [])

theorem wSend_is {S : LinShape} {w : Listed} (h : wSend S = .ok w) : w = wListedOf S := by
  unfold wSend at h
  unfold wListedOf
  cases e : linMessageW S with
  | none =>
    rw [e] at h
    cases h
  | some a =>
    rw [e] at h
    exact (Except.ok.inj h).symm

theorem linShared_is {S : LinShape} {a : Nat} {s : List Listed} (h : linSharedSends S a = .ok s) :
    s = sharedListedOf S a := by
  unfold linSharedSends at h
  unfold sharedListedOf
  cases e : linMessageU S with
  | none =>
    rw [e] at h
    cases h
  | some u =>
    rw [e] at h
    exact (Except.ok.inj h).symm

/-- W's sending as listed, at the typed shape. -/
def keyW : Listed := wListedOf keyFull.once.shape

/-- The shared chain's sendings as listed, at the typed shape and the written setting. -/
def keyShared : List Listed := sharedListedOf keyFull.once.shape recordSet.samples

theorem ok_of_sendIs {x : Except String ChainSends} {W : ChainSends} (h : sendIs x W = true) :
    x = .ok W := by
  cases x with
  | error e => cases h
  | ok k => rw [PlanWritten.sameChain_eq (a := k) (b := W) h]

theorem bind_ok_inv {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **wSend's return at the typed shape, by name.** -/
theorem keyW_at : wSend keyFull.once.shape = .ok keyW := by
  obtain ⟨w, hw, -⟩ := bind_ok_inv (ok_of_sendIs key0_send)
  rw [hw, wSend_is hw]
  rfl

/-- **linSharedSends' return at the typed shape and the written setting, by name.** -/
theorem keyShared_at : linSharedSends keyFull.once.shape recordSet.samples = .ok keyShared := by
  obtain ⟨s, hs, -⟩ := bind_ok_inv (ok_of_sendIs key1_send)
  rw [hs, linShared_is hs]
  rfl

/-- **The key file's five, at the written values.** -/
theorem keySendsFive_written :
    wSend keyFull.once.shape = .ok keyW ∧
      linSharedSends keyFull.once.shape recordSet.samples = .ok keyShared ∧
      oneOf "key" 0 keyFull.codes
        ([⟨"the index-mask message", [keyFull.once.input]⟩,
          ⟨"the multiplicities", (Wf.messageOf keyFull.ranges.x).toList⟩] ++
          ioppSends "the ranges' test" recordSet.samples keyFull.ranges.x.choice.masksRide 1
            keyFull.ranges.x.stages ++ [keyW]) keyThree.A.plan = .ok keySendsFull.1 ∧
      oneOf "key" 1 keyFull.codes keyShared keyThree.B.plan = .ok keySendsFull.2.1 ∧
      oneOf "key" 2 keyFull.codes
        (ioppSends "the own test" recordSet.samples keyFull.once.shape.choice.masksRide 1
          keyFull.once.shape.testOwn) keyThree.C.plan = .ok keySendsFull.2.2 := by
  obtain ⟨w, hw, h0⟩ := bind_ok_inv (ok_of_sendIs key0_send)
  obtain ⟨s, hs, h1⟩ := bind_ok_inv (ok_of_sendIs key1_send)
  have h2 := ok_of_sendIs key2_send
  obtain rfl : w = keyW := wSend_is hw
  obtain rfl : s = keyShared := linShared_is hs
  rw [oneSend_is_oneOf] at h0 h1
  unfold keyMade2 at h2
  rw [oneSend_is_oneOf] at h2
  exact ⟨hw, hs, h0, h1, h2⟩

/-- **The same five in the ledger's own letters**, at the written value of what the planner
makes. -/
theorem keySendsFive_at_W :
    wSend (writtenMade.at Hung.none).sized.key.once.shape = .ok keyW ∧
      linSharedSends (writtenMade.at Hung.none).sized.key.once.shape
        (writtenMade.at Hung.none).sized.set.samples = .ok keyShared ∧
      oneOf "key" 0 (writtenMade.at Hung.none).sized.key.codes
        ([⟨"the index-mask message", [(writtenMade.at Hung.none).sized.key.once.input]⟩,
          ⟨"the multiplicities",
            (Wf.messageOf (writtenMade.at Hung.none).sized.key.ranges.x).toList⟩] ++
          ioppSends "the ranges' test" (writtenMade.at Hung.none).sized.set.samples
            (writtenMade.at Hung.none).sized.key.ranges.x.choice.masksRide 1
            (writtenMade.at Hung.none).sized.key.ranges.x.stages ++ [keyW]) keyThree.A.plan =
        .ok keySendsFull.1 ∧
      oneOf "key" 1 (writtenMade.at Hung.none).sized.key.codes keyShared keyThree.B.plan =
        .ok keySendsFull.2.1 ∧
      oneOf "key" 2 (writtenMade.at Hung.none).sized.key.codes
        (ioppSends "the own test" (writtenMade.at Hung.none).sized.set.samples
          (writtenMade.at Hung.none).sized.key.once.shape.choice.masksRide 1
          (writtenMade.at Hung.none).sized.key.once.shape.testOwn) keyThree.C.plan =
        .ok keySendsFull.2.2 :=
  keySendsFive_written

end IM

#print axioms IM.wSend_is
#print axioms IM.linShared_is
#print axioms IM.ok_of_sendIs
#print axioms IM.bind_ok_inv
#print axioms IM.keyW_at
#print axioms IM.keyShared_at
#print axioms IM.keySendsFive_written
#print axioms IM.keySendsFive_at_W
