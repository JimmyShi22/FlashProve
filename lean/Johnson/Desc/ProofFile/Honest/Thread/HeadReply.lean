-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadReply.lean: the column `h₀` of the gathering
(`owesS_head_form`, GatherHeadForm.lean) at the first chain's invariant at the full size, with the
border `b₀ := 339`: from border 339 on, the state holds the token that the request asks about as its
reply. Number 338 is the sub-protocol that hears the reply (K7). `k7_laysS` (K7/Lays.lean) says that
after its accepting step, on the honest prover's message, the reply is that token. At every other
number an accepting step leaves the reply: `reply_kept_but` (Johnson/AtFull/Shape/ReplyEnds.lean) of
other authors. The invariant before the step says that the reply is that token from border 339 on.
No definition.

  1  `head_k7Stands`   the hypothesis `K7Stands` of `k7_laysS` at number 338
  2  `head_h0`   the column `h₀`

What is left as a hypothesis: `hhalf`, that the prover's part at K7's place is the kind's own
(`replyHalf`, at segment 24). It is a condition on the argument `H`, the prover.

Limits.
  * That an accepting step exists at any state is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.K7.Lays
import Johnson.Desc.ProofFile.Honest.K7.InScope
import Johnson.Desc.ProofFile.Honest.K13.DebtsKit
import Johnson.AtFull.Shape.ReplyEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The hypothesis `K7Stands` at number 338, from the prover's part at K7's place. -/
theorem head_k7Stands {l V : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf l 1 V))
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[338]? = some blk) (hpl : blk.place = IM.k7Place)
    (hr : blk.rounds = VerifiableInference.Desc.Kinds.Reply.rounds) (ho : blk.oracles = [[]]) :
    K7Stands (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 338 l V blk where
  member := hb
  rounds := hr
  oracles := ho
  half := by
    rw [hpl]
    exact hhalf
  noTree := ProofFile.Honest.K13.fresh_none _ hb (by rw [ho]; rfl)

/-- **The column `h₀` at `b₀ := 339`.** -/
theorem head_h0 (hb₀ : b₀ = 339)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {V : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 V)) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked := by
  intro b _ blk hblk k s m E ds y cols s' hA hd hS hle
  by_cases e : b = 338
  · subst e
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨blk', fs, f, hb', Dm, hpl, hr, ho, -⟩ := k7Made_inScope h.scope h.reads O
    obtain rfl : blk' = blk := Option.some.inj (hb'.symm.trans hblk)
    exact k7_laysS Said
      (head_k7Stands h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hhalf hb' hpl hr ho) Dm 0 0 blk'
      hblk k s m E ds y cols s' hA hd hS
  · have hge : b₀ ≤ b := by omega
    have hrd :
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.rides b m.st.input
          s := hA.1.2.2.2.2.2.1
    have hk := Johnson.AtFull.Shape.reply_kept_but h b e blk hblk _ s _ cols s' _ hS.2
    rw [hk]
    exact hrd.1 hge

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_k7Stands
#print axioms ProofFile.Honest.FirstThread.head_h0
