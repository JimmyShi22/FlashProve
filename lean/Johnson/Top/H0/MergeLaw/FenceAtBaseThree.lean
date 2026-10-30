-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FenceAtBaseThree.lean: the fence at the base of the piece at 346
(`fence_at_base`, FenceAtBase.lean) at the three rows of pieces with the cap (`threeCap`,
Johnson/Goal/Skeleton/TheThree.lean). One theorem with its proof: a call.

`fence_at_three`: F: an IOP as written in Lean, whose data D are made and whose test on the plan
accepts. Where the first chain's rows are the written ones and the two tests with code accept at the
written number of trees in front of 346: at the piece q at 346 of the first row of `threeCap`: every
tenant in `sampledIn N open346` has its tree below q.base, and `Fenced q.base ms`.

Paid here: that the pieces hold F's sub-protocols (`threeCap_ofDesc`); that they tile the first
chain, hold its data and begin at tree 0 (`threeCap_fits`); that the sub-protocols are shaped (the
test on the plan).

Limits. Those of FenceAtBase.lean. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.FenceAtBase
import Johnson.Goal.Skeleton.TheThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Maker OnBytes.Flat
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription blocksOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.PlanWritten (cutFirstFull)

/-- **The fence at the piece's base, at 346, at the three rows of pieces with the cap.** -/
theorem fence_at_three {Xi W : Type} {F : FileDescription Xi} {D : WholeD} {b₁ : Block F.S₁ F.Cl}
    {l₁ : List (Block F.S₁ F.Cl)} {b₂ : Block F.S₂ F.Cl} {l₂ : List (Block F.S₂ F.Cl)}
    {b₃ : Block F.S₃ F.Cl} {l₃ : List (Block F.S₃ F.Cl)} {file : String}
    (h : F.data file = .ok D) (hp : F.planOk = true) (q₁ : F.first.blocksInOrder = b₁ :: l₁)
    (q₂ : F.shared.blocksInOrder = b₂ :: l₂) (q₃ : F.second.blocksInOrder = b₃ :: l₃)
    (e₁ : (i : ℕ) → (ds : List RDT) →
      (F.XiPub × F.S₁) × (Sound.frameAt D (allOf D) D.key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₂ : (i : ℕ) → (ds : List RDT) →
      ((F.XiPub × F.S₁) × F.S₂) × (Sound.frameAt D (allOf D) D.key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₃ : (i : ℕ) → (ds : List RDT) →
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (Sound.frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W)
    (d wEnd : W) (hc : PlanWritten.cutOf F.first.blocksInOrder = cutFirstFull) (N : Numbers)
    (ms : List Mem) (hlow : lowAtB N open346 (treesInFront cutFirstFull 346) = true)
    (hf : fencedB (treesInFront cutFirstFull 346) ms = true)
    (q : Piece (ckP .two) (Sound.frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) F.Cl W)
    (hq : ((threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).p₁ ::
      (threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).l₁)[346]? = some q) :
    (∀ y ∈ sampledIn N open346, y.1 < q.base) ∧ Fenced q.base ms := by
  have hFit := threeCap_fits e₁ e₂ e₃ d wEnd h hp q₁ q₂ q₃
  have hb : blocksOk F.first.blocksInOrder = true := by
    cases hb : blocksOk F.first.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at hp
  exact fence_at_base F file D h (threeCap F D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd)
    (threeCap_ofDesc e₁ e₂ e₃ d wEnd h hp q₁ q₂ q₃) hFit.tiled₁ hFit.data₁ hFit.base₁ hb hc N ms
    hlow hf q hq

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.fence_at_three
