-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ReplyKeptPaid.lean: `relsReply` (FHeadI.lean) holds after every
sub-protocol's accepted step from a state at which the first chain's invariant holds, at the full
size. It is what `fHeadI` asks of `keeps` beyond `fHeadH`. No definition.

  `head_hreply_paid`   the column `hK` of the gathering at the new relation, for every `Kp` and
     every `Said`. Its one hypothesis beside the library's `AtMgA` is `hB`: `ProofFile.baseOf` returns at
     the public part

How. The relation asks something at the kind K7 alone, and a place of that kind has the number 338
(`k7_number_of`). The sub-protocol there is the lot's own block with the frame's "opened" of the
output head's segment joined behind it (`IM.k7_sits`, Johnson/IMR/FirstSeats.lean). That "opened"
hands the state on as it is. So an accepting decision at number 338 is an accepting decision of the
lot's own block with the same state after it (`IM.k7_sits_yes`, the same file). `h1Keeps_of_decide`
(Honest/K7/Keeps.lean) turns that into `H1Keeps`. The lines up to the call of `IM.k7_sits` are those
of `fHead_keeps_k7` (FHeadKeepsH.lean) and `head_pileKept_k7` (PileKeptPaid.lean) a second time.

Limits.
  * That an accepting step exists at any state is not shown.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadI
import Johnson.Desc.ProofFile.Honest.Thread.PileKeptPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName Block)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **`relsReply` after every sub-protocol's accepted step.** -/
theorem head_hreply_paid {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      relsReply Bs.G₀ blk.place.kind s s' := by
  intro b hb blk hblk k s m E ds y cols s' _ hd hS
  cases hκ : blk.place.kind with
  | K7 =>
    have hb' : b < 358 := by
      have e : b < cF.blocksInOrder.length := hb
      rw [head_len h] at e
      exact e
    have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk
    obtain rfl := k7_number_of hb' hp hκ
    have hy : StepYes 0 blk s s' :=
      stepYes_of_stepped (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread hd hS
    obtain ⟨Bs', base, O⟩ := h.laid.opened
    obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
    obtain ⟨Lk, b0, e1, e2, hj, -⟩ := IM.k7_sits h.scope h.reads O
    have hb1 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (by decide) 0] at hb1
    have hb2 : cF.blocksInOrder[338]? = some b0 := hb1
    have hb3 : cF.blocksInOrder[338]? = some blk := hblk
    obtain rfl : b0 = blk := Option.some.inj (hb2.symm.trans hb3)
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    obtain ⟨d1, d2⟩ := IM.k7_sits_yes h.scope h.reads O hj e
    exact h1Keeps_of_decide (k7Block_lot h.scope h.reads O) d1 d2
  | _ => trivial

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_hreply_paid
