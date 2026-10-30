-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SitsHead.lean: `Sits` (Honest/Thread/File.lean) at the
description that the library's hypothesis `AtMgA` names: the three `Thread`s are `lettersHead … w`
(Honest/Thread/FirstHead.lean) and the `Thread`s of any parameters of the shared and the second
chain (Honest/Thread/Shared.lean, Honest/Thread/Last.lean) that have the description's own flat
lists and a prover's own sides. The term `P5J.F0T o Zp Np cF` has the shared chain's state
`Desc.K14.St` and the second chain's `Desc.Third.S₃` by unfolding (the library's
Johnson/Desc/Sound/AtDescPure.lean says so): so the two later chains' parameters are typed at these.
Fifteen equations: ten by unfolding, five are hypotheses on the later chains' parameters; the three
executable tests on the parameters (`Thread.fits`) are hypotheses. One lemma.

  `sits_at_head`   the lemma

Limits.
  * The full size alone, and the hash function `secondHashFunction` alone (Honest/Thread/FirstAt.lean says which
    that is).
  * A term of the library's hypothesis `AtMgA` exists at the name under four hypotheses on the
    public files (the library's `head_exists_at_name`); this file does not call it, and it proves of
    no such term that the invariant holds at a run.
  * The later chains' parameters are variables: nothing is defined of them here.
  * It is none of the library's goals.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shared
import Johnson.Desc.ProofFile.Honest.Thread.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`Sits` at the description that `AtMgA` names.** A conditional lemma on this folder's own
definitions. It is none of the library's goals. -/
theorem sits_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X P₁ Wt₂ Wt₃ : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (L₂ : SharedThread.Letters Bk Desc.K14.St ProofFile.Cl W₀ Rc OnBytes.TableKey X₀ P₁ Wt₂)
    (L₃ : LastThread.Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst
      Tr X P₁ Wt₃)
    (b₂ : L₂.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) (h₂ : L₂.hs = H.shared)
    (t₃ : L₃.ft = (F0T OnBytes.secondHashFunction Zp Np cF).lastChainFirstTreeNumber)
    (b₃ : L₃.bs = (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder) (h₃ : L₃.hs = H.second)
    (f₁ : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fits
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (f₂ : L₂.thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length = true)
    (f₃ : L₃.thread.fits (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.length = true) :
    Sits (F0T OnBytes.secondHashFunction Zp Np cF) H
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread L₂.thread L₃.thread :=
  { one := sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    two := ⟨rfl, rfl, rfl, b₂, h₂⟩
    three := ⟨rfl, rfl, t₃, b₃, h₃⟩
    fits := ⟨f₁, f₂, f₃⟩ }

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.sits_at_head
