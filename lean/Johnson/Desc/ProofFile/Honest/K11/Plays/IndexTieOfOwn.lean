-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexTieOfOwn.lean: the proof of the statement of
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexTieOfOwnStatement.lean, to the letter. A lemma; none of
the library's goals. A joining.

How. The lines of `maskTieOfOwn` (MsgLots.lean of this folder) that find the base, the seated block,
what the row is lent and the valid input stand here again. Then: `keeps_of_stepped` (Riders.lean of
this folder) gives the kind's clause on what the step writes: the state behind is the state in front
but for the count of rows owed and the head's own part. `indexEntry_border`
(Honest/K4/Law/W/IndexFactsThr.lean, another group of authors') is called at border 346 and segment
24, AT THE STATE IN FRONT: the place there by `k11_hp` (Johnson/Desc/Sound/MgAt/K11Places.lean); the
item pinI open there by `pinI_open_at_346` (Johnson/Desc/K11/Front/PinIOpenAt346.lean). Its end is
carried to the state behind by unfolding: the ledger and the reader's mask table read the statement,
the book and the output numbers alone. `indexLotAt` (MsgLots.lean) and the premise give the entry's
value.

Why not at border 347. That the thread stands behind the member is not to be had for nothing: the
frame's lemma for it asks the kind's own debts, this field among them.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexTieOfOwnStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.MsgLots
import Johnson.Desc.ProofFile.Honest.K11.Plays.Riders
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexFactsThr
import Johnson.Desc.K11.Front.PinIOpenAt346

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.Sound.MgAt (k11_hp mergeAt)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull)
open Johnson.Desc.First.ForkMerge.Front (pinI_open_at_346)
open ProofFile.Honest.FirstThread (lettersHead head_valid)
open ProofFile.Honest.K4.W (indexEntry_border)

/-- **The kind's premise on the index masks' message, from `OwnMsgs` at the kind's own lot.** -/
theorem indexTieOfOwn : IndexTieOfOwn := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    claims weights c₀ hB hhalf hOwn blk k s m E ds y cols s' hT hS hblk ds' l c' l' hl ht
  obtain ⟨Bs', _, name, hB', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  have hK := keeps_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (b := 346) hfl hblk hS
  obtain rfl : blk = IM.seatedAs ProofFile.sameReply
      (Johnson.Desc.First.ForkMerge.headClaimMergeKind (_root_.K11.parOf Zp Bs'.G₀)) name IM.k11Place :=
    Option.some.inj (hblk.symm.trans hfl)
  have hb : 346 ≤ cF.blocksInOrder.length := by
    have := (List.getElem?_eq_some_iff.1 hfl).1
    omega
  obtain ⟨⟨l₀, hl₀, hy⟩, _⟩ := hS.1
  obtain ⟨q, c, hlend, _⟩ := stepsOfHalf Bk W₀ Rc ProofFile.Inst Tr X _
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (_root_.K11.parOf Zp Bs'.G₀)
    claims weights name IM.k11Place hhalf k m.st.input l₀ hl₀
  have hin : y.2.st.input = m.st.input := (play_mid l₀ ds [] m y hy).1
  have hV : Vd y.2.st.input := by
    rw [hin]
    exact ((head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m.st.input).1
      hT.1.2.2.2.2.2.2).2
  -- the state behind, written out of the state in front
  obtain ⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩ := hK.1
  -- the reader, at the state in front
  have e1 := fun z wt => (indexEntry_border h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (pl := mergeAt) (m := 24) k11_hp rfl (by decide) hb (by omega) pinI_open_at_346 hT.1 z wt hl
    ht).2
  -- the lot
  have e2 := hOwn k y.2.st.input (y.2.st.heard ++ ds') hV (Nat.zero_le _) true _ _ _
    (indexLotAt Bk W₀ Rc ProofFile.Inst Tr X _ IM.k11Place (_root_.K11.parOf Zp Bs'.G₀) claims weights
      _ _ _ k y.2.st.input _ _ hlend)
  unfold headMergeCoins
  rw [hlend]
  exact (e1 m.st.input.x.pub _).trans e2

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.indexTieOfOwn
