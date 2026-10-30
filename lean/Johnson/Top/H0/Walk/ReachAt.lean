-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachAt.lean: "REACHED" (Reach.lean) AT A DESCRIPTION (the IOP as written in
Lean: FileDescription, Johnson/Desc/Block.lean) AND THE PIECES THAT HOLD ITS OWN FIRST CHAIN's BLOCKS (its
sub-protocols): the family of conditions, border by border, in the form in which the table's frame
takes it: true at the start, handed on by every piece's yes, kind-free.

  RchAt F k a       the state in a is handed on by the first k blocks of F's first chain's flat
                    list, EACH BEHIND THE TEST THAT EVERY WORD SHOWN IS BELOW THE PRIME ("below":
                    what a piece holds), from F.start₁ of a's own public part, at the first tree 0.
                    (Stepping by the sub-protocols themselves it would hold of states that no
                    piece's yes makes.)
  rchAt_zero        true at the start
  block_at          every piece of the first row holds a block of the flat list, at its own number
  rchAt_hand        THE HAND-ON: from OfDesc alone (Johnson/Desc/Sound/DescThree.lean: T.ft₁ = 0;
                    AtDriver.lean: OfDesc.pieceAt): at every piece of the row, the last among them
  rchAt_hand_map    the same at the piece with another extractor laid in (Piece.withMap)
  rchAt_raw, rchAt_fold, rchAt_fold_below   what a law that spends it gets: it is reached by the
                    sub-protocols' own steps too; the fold's own yes, at SOME rounds and columns,
                    over the sub-protocols themselves and over the wrapped ones

Limits. As Reach.lean's. No soundness statement.

-/
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.ReExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block FileDescription foldBlocks)
open VerifiableInference.Desc.Sound

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} {F : FileDescription Xi}
  {T : ThreeAt C D all F X₁ X₂ W}

/-- **Reached, at a description's first chain.** Str: whatever stands beside the statement's first
half (the oracles' strings): it is not read. -/
def RchAt {Str : Type} (F : FileDescription Xi) (k : ℕ) (a : (F.XiPub × F.S₁) × Str) : Prop :=
  Reach 0 (F.first.blocksInOrder.map below) F.start₁ k a.1

theorem rchAt_zero {Str : Type} (z : F.XiPub) (y : Str) : RchAt F 0 ((z, F.start₁ z), y) :=
  Reach.zero z

/-- Every piece of the first row holds a block of the flat list, at its own number. -/
theorem block_at (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) : ∃ B, F.first.blocksInOrder[k]? = some B := by
  have hl : (T.p₁ :: T.l₁).length = F.first.blocksInOrder.length := by
    have e := congrArg List.length hT.b₁
    simpa using e
  have hk : k < F.first.blocksInOrder.length := by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.1 hq).1
  exact ⟨_, List.getElem?_eq_getElem hk⟩

/-- **THE HAND-ON.** -/
theorem rchAt_hand (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) {a b} {τ : Iop.Tr (uLT C q.ds)}
    (h : q.ior.red.out a τ = some b) (hr : RchAt F k a) : RchAt F (k + 1) b := by
  obtain ⟨B, hB⟩ := block_at hT hq
  have e : (frameAt D all D.key₁ T.ft₁).ft = 0 := hT.ft₁
  unfold RchAt at hr ⊢
  rw [← e] at hr ⊢
  exact reach_hand_below hB (OfDesc.pieceAt hT hq hB) h hr

/-- The same at the piece with another extractor laid in. -/
theorem rchAt_hand_map (hT : OfDesc F T) {k : ℕ}
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (F.XiPub × F.S₁) F.Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q) (E) {a b} {τ : Iop.Tr (uLT C (q.withMap E).ds)}
    (h : (q.withMap E).ior.red.out a τ = some b) (hr : RchAt F k a) : RchAt F (k + 1) b :=
  rchAt_hand hT hq (τ := τ) h hr

/-- It is reached by the sub-protocols' own steps too. -/
theorem rchAt_raw {Str : Type} {k : ℕ} {a : (F.XiPub × F.S₁) × Str} (h : RchAt F k a) :
    Reach 0 F.first.blocksInOrder F.start₁ k a.1 := reach_raw h

/-- What a law that spends it gets: the fold over the sub-protocols themselves. -/
theorem rchAt_fold {Str : Type} {k : ℕ} {a : (F.XiPub × F.S₁) × Str} (h : RchAt F k a) :
    k ≤ F.first.blocksInOrder.length ∧ ∃ rs cols,
      foldBlocks 0 (F.first.blocksInOrder.take k) (F.start₁ a.1.1) rs cols = .ok (a.1.2, [], []) :=
  Reach.fold (rchAt_raw h)

/-- And the fold over the wrapped ones: every word shown was below the prime. -/
theorem rchAt_fold_below {Str : Type} {k : ℕ} {a : (F.XiPub × F.S₁) × Str} (h : RchAt F k a) :
    ∃ rs cols, foldBlocks 0 ((F.first.blocksInOrder.map below).take k) (F.start₁ a.1.1) rs cols =
      .ok (a.1.2, [], []) :=
  (Reach.fold h).2

end

#print axioms rchAt_hand
#print axioms rchAt_hand_map
#print axioms rchAt_fold
#print axioms rchAt_fold_below

end Johnson.Desc.First.Walk.Tied
