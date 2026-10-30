-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/MsgLots.lean: the proofs of the four statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/MsgLotsStatement.lean, to the letter. Lemmas; none of the
library's goals.

A FURTHER TEXT. THE FIRST EIGHTEEN LINES OF `maskTieOfOwn` ARE THOSE OF `maskTieOfOn`
(MaskBridge.lean of this folder), WRITTEN A FURTHER TIME: the member is the merge's; the ledger's
next free slot in front is 3531; under the step the book lends; the play leaves the input. That
lemma ends in another form of the frame's authors'.

How. `maskLotAt`, `indexLotAt`, `lotsOfLent`: by the lots' texts. `maskTieOfOwn`: at the stand
behind the member's step the library's reader of the segment's mask row meets `ReaderAt` up to 3569
(`readerAtBehind`, MaskBridge.lean; `padAtHead`, `freeAtHead`, PadAtHead.lean): so at entry 3531 + i
it reads entry 3531 + i of row 0 of the mask table of the witness's message (`reader_at`,
Honest/Law/Rule/ReaderAt.lean); the thread's witness is the Script's, whose message is `Q.msg` at
the challenges cut at `Q.fixedMsg` (`Script.wit`, Honest/Thread/First.lean): the left side of
`OwnMsgs`. The run's input is valid (the thread's last clause; `head_valid`,
Honest/Thread/FirstHead.lean). The lot answers there (`maskLotAt`).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLotsStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskBridge
import Johnson.Desc.ProofFile.Honest.K11.Plays.PadAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (zeroE)
open OnBytes.Model (Reading)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Front (nextAtRaw)
open ProofFile.Honest.SumLaw (firstRun endRun)
open ProofFile.Honest.FirstThread (lettersHead thrS_reach_below head_valid)

/-- **Where the first lot answers.** -/
theorem maskLotAt : MaskLotAt := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ k w hd c hc i hi
  show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
    | .error _ => none
    | .ok c =>
      if true = true ∧ 0 = 0 ∧ ν₀ ≤ ν₀ + i ∧ ν₀ + i < ν₀ + (2 * P.lay.lk + 2) then
        some (Reading.gl.val ((firstRun c.2.1).getD (ν₀ + i - ν₀) zeroE))
      else none) = _
  rw [hc]
  show (if true = true ∧ 0 = 0 ∧ ν₀ ≤ ν₀ + i ∧ ν₀ + i < ν₀ + (2 * P.lay.lk + 2) then
      some (Reading.gl.val ((firstRun c.2.1).getD (ν₀ + i - ν₀) zeroE)) else none) = _
  rw [if_pos ⟨rfl, rfl, Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩, Nat.add_sub_cancel_left]

/-- **Where the second lot answers.** -/
theorem indexLotAt : IndexLotAt := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n r p k w hd c hc
  show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
    | .error _ => none
    | .ok c =>
      if true = true ∧ r = r ∧ p = p then some (Reading.gl.val ((endRun c.2.1).headD zeroE))
      else none) = _
  rw [hc]
  show (if true = true ∧ r = r ∧ p = p then
      some (Reading.gl.val ((endRun c.2.1).headD zeroE)) else none) = _
  rw [if_pos ⟨rfl, rfl, rfl⟩]

/-- **Coins to which the book lends alike give one text.** -/
theorem lotsOfLent : LotsOfLent := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ n' r p k k' e
  constructor
  · funext w hd mask row place
    show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
      | .error _ => none
      | .ok c => _) = (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k' with
      | .error _ => none
      | .ok c => _)
    rw [e]
  · funext w hd mask row place
    show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
      | .error _ => none
      | .ok c => _) = (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k' with
      | .error _ => none
      | .ok c => _)
    rw [e]

/-- **The kind's premise on the mask row's message, from `OwnMsgs` at the kind's own lot.** -/
theorem maskTieOfOwn : MaskTieOfOwn := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    claims weights c₀ hB hhalf hOwn blk k s m E ds y cols s' a a9 hT hS hblk ha ha9 ds' i hi
  obtain ⟨Bs', _, name, hB', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  obtain rfl : blk = IM.seatedAs ProofFile.sameReply
      (Johnson.Desc.First.ForkMerge.headClaimMergeKind (_root_.K11.parOf Zp Bs'.G₀)) name IM.k11Place :=
    Option.some.inj (hblk.symm.trans hfl)
  have hb : 346 ≤ cF.blocksInOrder.length := by
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  have hr := reach_raw (thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT)
  have hnext : a.F.next = 3531 :=
    (nextAtRaw Z D r Zp Np cF x Bs' m.st.input.x.pub s a h hB hr ha).1
  obtain ⟨⟨l, hl, hy⟩, _⟩ := hS.1
  obtain ⟨q, c, hlend, _⟩ := stepsOfHalf Bk W₀ Rc ProofFile.Inst Tr X _
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (_root_.K11.parOf Zp Bs'.G₀)
    claims weights name IM.k11Place hhalf k m.st.input l hl
  have hin : y.2.st.input = m.st.input := (play_mid l ds [] m y hy).1
  -- the reader
  have hfree := freeAtHead Z D r Zp Np cF x h Bs' hB
  have hRd := readerAtBehind Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w Bs' 3569 hB (padAtHead Z D r Zp Np cF x h) k s' y.2 E
    ⟨_, s, m, E, ds, y, cols, hT, hS, hblk, rfl⟩ a9 ha9
  have e1 := reader_at hRd (Q.wit k y.2.st.input (y.2.st.heard ++ ds')) (ν := 3531 + i) (by omega)
  -- the lot
  have hV : Vd y.2.st.input := by
    rw [hin]
    exact ((head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m.st.input).1
      hT.1.2.2.2.2.2.2).2
  have e2 := hOwn k y.2.st.input (y.2.st.heard ++ ds') hV (Nat.zero_le _) true 0 (3531 + i) _
    (maskLotAt Bk W₀ Rc ProofFile.Inst Tr X _ IM.k11Place (_root_.K11.parOf Zp Bs'.G₀) claims weights
      (P5J.At.num Zp 24 0) 3531 k y.2.st.input _ _ hlend i hi)
  unfold headMergeCoins
  rw [hlend, hnext]
  exact e1.trans e2

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.maskLotAt
#print axioms ProofFile.Honest.K11.indexLotAt
#print axioms ProofFile.Honest.K11.lotsOfLent
#print axioms ProofFile.Honest.K11.maskTieOfOwn
