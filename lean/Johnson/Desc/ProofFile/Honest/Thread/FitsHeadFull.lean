-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FitsHeadFull.lean: `Thread.fits` AT THE HEAD's FIRST THREAD,
WITH THE TEST IN ONE PASS PAID. `fits_head` (Honest/Thread/FitsHead.lean) leaves two premises by
name: hone (along the first chain's written list of places, whatever a forward row asks or shuts is
open in front of it) and hfix (on the Script). The files of the kind K4 have had hone
decided by Lean's kernel at the full size's two written lists (`K4.W.onePass_full`,
Honest/K4/Law/W/OnePassFull.lean): here it is handed in. One statement: a call. No definition.

  `fits_head_full`   `fits_head`'s end from hfix alone

Limits. As `fits_head`'s. hfix is shown by nobody. It stands over one file of that house which is
not sealed. None is one of the library's goals. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.FitsHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OnePassFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`Thread.fits` AT THE HEAD's FIRST THREAD, FROM THE PREMISE ON THE SCRIPT ALONE.** A
conditional lemma on our own definitions. It is none of the library's goals. -/
theorem fits_head_full (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.fits
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true :=
  fits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w K4.W.onePass_full hfix

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fits_head_full
