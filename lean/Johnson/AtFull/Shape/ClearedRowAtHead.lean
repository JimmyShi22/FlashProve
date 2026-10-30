-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ClearedRowAtHead.lean: the member "link l: cleared" of the proof file's own
first chain AT THE THIRTEEN LINKS THAT CAN LEAVE A ROW (the twelve layers' links and the head's):
under the head at which the library's laws on that chain speak (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): one step on the shape of the chain's state, NAMED, its parameters tied to
values, with the laws "carries" and "returns" at the seated member's own decision. A joining of
laws; nothing is evaluated. NO TEST ON VALUES AND NO PREMISE beside the step's own return.

  `clear_lay`: which "cleared" the frame's row has at a layers' link, link 0 among them.
  `clear_head`: the same at the head's link.
  `clearWith_keeps`: the frame's "cleared" leaves no mark of failure and keeps the reply.
  **`cleared_lay_named`** (l < 25, a layers' link): Y := the plan's entry of the link, hp := the
    public record's plan of group Y.g: the step is clearLayG (pubOf Y) Zp.p.X.layers.wsLay
    Zp.first.lin hp.tl.NM.
  **`cleared_head_named`** (l < 25, the head's link): the step is clearHeadG (pubOf Y)
    Zp.p.X.layers.wsLay Zp.first.lin.

Limits. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. That a step returns at a shape that the chain
reaches is not shown. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Walk.Shape.ClearRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.First.Close (tailHead)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame framesOf_arms rowOf pubOf headFrame)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem clear_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    (hs : subAt l = .layers) {fs : List LinkFrame}
    (hfs : framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs) {f : LinkFrame}
    (hf : fs[l]? = some f) :
    ∃ Y hp, Zp.p.built.links[l]? = some Y ∧ Zp.p.X.G[Y.g]? = some hp ∧
      f.clear = clearWith (pubOf Y) (countsLay hp.tl.NM) leftLay (rowOf Zp.p.X Zp.first) := by
  rcases framesOf_arms hfs hf with ⟨Y, hY, hk, -⟩ | ⟨rfl, Y, q, P, hY, -, hG, rfl, -, -, e3⟩ |
    ⟨-, Y, _, _, hY, hk, -⟩ | ⟨-, Y, q, P, hY, -, hG, rfl, -, -, e3⟩
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · exact ⟨Y, q, hY, hG, e3⟩
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · exact ⟨Y, q, hY, hG, e3⟩

theorem clear_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    (hs : subAt l = .head) {fs : List LinkFrame}
    (hfs : framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs) {f : LinkFrame}
    (hf : fs[l]? = some f) :
    ∃ Y, Zp.p.built.links[l]? = some Y ∧
      f.clear = tailHead (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin := by
  rcases framesOf_arms hfs hf with ⟨Y, hY, -, rfl⟩ | ⟨rfl, Y, _, _, hY, hk, -⟩ |
    ⟨-, Y, _, _, hY, hk, -⟩ | ⟨-, Y, _, _, hY, hk, -⟩
  · exact ⟨Y, hY, rfl⟩
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e
  · have e := sub_kind h hl hY
    rw [hk, hs] at e
    exact nomatch e

/-- The frame's "cleared" leaves the mark of failure unset and the reply as it is. -/
theorem clearWith_keeps {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) :
    t.failed = none ∧ ProofFile.sameReply s t = true := by
  obtain ⟨C, F, -, hF, -, k, q, -, hq⟩ := Props.clearWith_iff.1 h
  rcases hq with ⟨-, hl⟩ | ⟨w, y, os, -, -, hl⟩
  · obtain ⟨rfl, hf⟩ := (leave_iff hF t).1 hl
    exact ⟨hf, by unfold ProofFile.sameReply; exact beq_self_eq_true _⟩
  · have hF' : ({ s with out := pendingKept s.out y, st := { s.st with oracles := os } } :
        S).fork? = some F := hF
    obtain ⟨rfl, hf⟩ := (leave_iff hF' t).1 hl
    exact ⟨hf, by unfold ProofFile.sameReply; exact beq_self_eq_true _⟩

theorem cleared_lay_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hs : subAt l = .layers) :
    ∃ (Y : Stages.LinkH) (hp : Layer.HPlan2) (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl),
      Zp.p.built.links[l]? = some Y ∧ Zp.p.X.G[Y.g]? = some hp ∧
      cF.links[l]? = some L ∧ cF.blocksInOrder[14 * l + L.hear.length + 7]? = some b ∧ b.rounds = [] ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        clearLayG (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin hp.tl.NM (chainSh s) = .ok u →
        u = chainSh t) ∧
      ∀ s rs gs u,
        clearLayG (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin hp.tl.NM (chainSh s) = .ok u →
        ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, bC, eL, -, hf, -, -, -, hC, -, -, -, -, -, -, hb, hr, hd⟩ := hall l hl
  obtain ⟨Y, hp, hY, hG, hc⟩ := clear_lay h hl hs hfs hf
  refine ⟨Y, hp, Lk, bC, hY, hG, eL, hb, hr, fun s rs gs t u hy hg => ?_,
    fun s rs gs u hg => ?_⟩
  · have hy2 := ((hC s t).1 ((hd s rs gs).symm.trans hy)).1
    rw [hc] at hy2
    exact clearLay_carries _ _ _ _ s t u hy2 hg
  · obtain ⟨t, ht⟩ := clearLay_returns _ _ _ _ s u hg
    obtain ⟨k1, k2⟩ := clearWith_keeps ht
    exact ⟨t, (hd s rs gs).trans ((hC s t).2 ⟨by rw [hc]; exact ht, k1, k2⟩)⟩

theorem cleared_head_named (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hs : subAt l = .head) :
    ∃ (Y : Stages.LinkH) (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl),
      Zp.p.built.links[l]? = some Y ∧
      cF.links[l]? = some L ∧ cF.blocksInOrder[14 * l + L.hear.length + 7]? = some b ∧ b.rounds = [] ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        clearHeadG (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin (chainSh s) = .ok u →
        u = chainSh t) ∧
      ∀ s rs gs u, clearHeadG (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin (chainSh s) = .ok u →
        ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, bC, eL, -, hf, -, -, -, hC, -, -, -, -, -, -, hb, hr, hd⟩ := hall l hl
  obtain ⟨Y, hY, hc⟩ := clear_head h hl hs hfs hf
  refine ⟨Y, Lk, bC, hY, eL, hb, hr, fun s rs gs t u hy hg => ?_, fun s rs gs u hg => ?_⟩
  · have hy2 := ((hC s t).1 ((hd s rs gs).symm.trans hy)).1
    rw [hc] at hy2
    exact clearHead_carries _ _ _ s t u hy2 hg
  · obtain ⟨t, ht⟩ := clearHead_returns _ _ _ s u hg
    obtain ⟨k1, k2⟩ := clearWith_keeps (X := pubOf Y) ht
    exact ⟨t, (hd s rs gs).trans ((hC s t).2 ⟨by rw [hc]; exact ht, k1, k2⟩)⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.cleared_lay_named
#print axioms Johnson.AtFull.Shape.cleared_head_named
#print axioms Johnson.AtFull.Shape.clear_lay
#print axioms Johnson.AtFull.Shape.clear_head
#print axioms Johnson.AtFull.Shape.clearWith_keeps
