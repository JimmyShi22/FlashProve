-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FrameAtHead.lean: the chain's front and the sub-protocol without a round
"link l: laid" of the proof file's own first chain, at all 25 links: under the head at which the
library's laws on that chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): one step on the shape of
the chain's state each, with the laws "carries" and "returns". A joining of laws of the library;
nothing is evaluated.

  `laidGS l`: the step at the seat: no mark of failure; then laidG l
    (Johnson/Desc/First/Walk/Shape/FrameChain.lean).
  **`front_at`**: the flat list's member number 0 has no round, and its decision accepts from s to t
    just if t = s: its step on the shape hands the shape on.
  **`laid_at`**: at l < 25 the flat list's member number 14 l + 1 has no round; its decision
    carries laidGS l; and where laidGS l returns at the state's shape the decision accepts. NO TEST
    ON VALUES.

By IM.front_of (Johnson/IMR/FrontSeat.lean) and IM.frame_of (Johnson/IMR/FrameSeat.lean).

Limits. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. Both statements spell the list (F0T
…).first.blocksInOrder: it is cF.blocksInOrder (Numbers.lean's first_is). The front accepts a marked state too.
laid_at's "carries" is under the step's own return. That laidGS returns at a shape that the chain
reaches is not shown. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.Walk.Shape.FrameChain
import Johnson.IMR.FrameSeat
import Johnson.IMR.FrontSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **The step at the seat.** -/
def laidGS (l : Nat) (a : ChainSh) : Except String ChainSh :=
  if a.marked then .error "a mark of failure" else laidG l a

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem front_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[0]? = some b ∧ b.rounds = [] ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t ↔ t = s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, h0, h1, -, -, -, h2⟩ := IM.front_of O
  exact ⟨b, h0, h1, h2⟩

theorem laid_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ b, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[14 * l + 1]? = some b ∧ b.rounds = [] ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t → laidGS l (chainSh s) = .ok u → u = chainSh t) ∧
      ∀ s rs gs u, laidGS l (chainSh s) = .ok u → ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, bL, -, -, -, -, -, -, hlay, hL, -, hb, hr, hd, -⟩ := hall l hl
  refine ⟨bL, hb, hr, fun s rs gs t u hy hg => ?_, fun s rs gs u hg => ?_⟩
  · have hy' : Lk.lay s = .ok t := (hd s rs gs).symm.trans hy
    have hy2 := (hL s t).1 hy'
    rw [hlay] at hy2
    unfold laidGS at hg
    cases hm : (chainSh s).marked with
    | true => rw [hm] at hg; exact nomatch hg
    | false =>
      rw [hm] at hg
      exact laid_carries l s t u hy2.1 hg
  · unfold laidGS at hg
    cases hm : (chainSh s).marked with
    | true => rw [hm] at hg; exact nomatch hg
    | false =>
      rw [hm] at hg
      obtain ⟨t, ht⟩ := laid_returns l s u hg
      obtain ⟨rfl, -⟩ := Johnson.Desc.First.Walk.Props.layFront_iff.1 ht
      have hf : t.failed = none := by
        have : t.failed.isSome = false := hm
        simpa using this
      exact ⟨t, (hd t rs gs).trans ((hL t t).2 ⟨by rw [hlay]; exact ht, hf, by
        unfold ProofFile.sameReply; exact beq_self_eq_true _⟩)⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.front_at
#print axioms Johnson.AtFull.Shape.laid_at
#print axioms Johnson.AtFull.Shape.laidGS
