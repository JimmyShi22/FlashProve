-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HandsOnRec.lean: THE HAND-ON OF «REACHED» OVER A PIECE WHOSE STATE IS
THE VERIFIER's STATE ALONE (the carriage's pieces `atRec`): `piece_step_below` and
`reach_hand_below` (Johnson/Top/H0/Walk/Reach.lean) speak of pieces over the public part and the
state; these two say the like without the public part. Kind-free. Theorems.

What is said.
  `piece_stepYes`: **a piece's yes is an accepting step of the sub-protocol that it holds.**
    `reach_hand_rec`: **where that sub-protocol stands at number k of the list, «reached at k» goes
    on to «reached at k + 1»**, at whatever public part.

Limits. The proof of the first follows that file's own, without the lift. Nothing on soundness.

-/
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (StepYes Reach)

variable {St Cl P W : Type} {C : CK} {Fr : Frame}

/-- **A PIECE's YES IS AN ACCEPTING STEP OF THE SUB-PROTOCOL THAT IT HOLDS.** -/
theorem piece_stepYes (q : Piece C Fr St Cl W) (a b : St × Fr.E.Str) (τ : Iop.Tr (uLT C q.ds))
    (h : q.ior.red.out a τ = some b) : StepYes Fr.ft q.b a.1 b.1 := by
  obtain ⟨_, f1, f3, _⟩ := piece_yes q a b τ h
  obtain ⟨g1, g2, g3⟩ := f1
  refine ⟨q.shownR τ, (sView C q.stage a.2 τ).opened, g1, ?_⟩
  refine (step_ok_iff Fr.ft q.b a.1 b.1 _ _ _).2 ⟨g2, ?_, ?_, ?_⟩
  · rw [List.take_length]
    exact g3
  · rw [← g3, List.length_map]
  · rw [List.take_length]
    exact f3

/-- **THE HAND-ON.** -/
theorem reach_hand_rec {bs : List (Block St Cl)} {start : P → St} {k : ℕ} (z : P)
    (q : Piece C Fr St Cl W) (hB : bs[k]? = some q.b) (a b : St × Fr.E.Str)
    (τ : Iop.Tr (uLT C q.ds)) (h : q.ior.red.out a τ = some b)
    (hr : Reach Fr.ft bs start k (z, a.1)) : Reach Fr.ft bs start (k + 1) (z, b.1) :=
  Reach.succ hr hB (piece_stepYes q a b τ h)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.piece_stepYes
#print axioms VerifiableInference.Desc.LinkJoin.reach_hand_rec
