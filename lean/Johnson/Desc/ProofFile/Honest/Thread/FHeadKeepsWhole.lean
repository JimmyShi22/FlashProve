-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsWhole.lean: the column `hK` of the gathering
(`owesS_head_form`, GatherHeadForm.lean) at `f := fHead` (FHead.lean), at all 358 numbers.
`fHead_hK` (FHeadKeepsAll.lean) leaves one hypothesis: the clause at number 354, the proximity test
(K12). `k12Keeps_form_354` (Johnson/Desc/K12/Honest/Shape/TestKeepsAt354.lean) of the authors of
K12's lemmas proves it, at the parameter `H2U.p12OfMade Zp.made`. So that is the argument `p12` of
`fHead` here. No definition.

  1  `fHead_keeps_k12`   the clause at number 354
  2  `fHead_hK_whole`   the column `hK`

Limits.
  * One hypothesis beside the library's `AtMgA`: `hB`, that `ProofFile.baseOf` returns at the public part.
  * That an accepting step exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsAll
import Johnson.Desc.K12.Honest.Shape.TestKeepsAt354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

include h in
/-- At the proximity test, number 354. -/
theorem fHead_keeps_k12 (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (P13 : VerifiableInference.Desc.K13.Where) :
    ∀ blk, cF.blocksInOrder[354]? = some blk → ∀ s s', s.failed = none → StepYes 0 blk s s' →
      fHead Zp cF G take P11 (H2U.p12OfMade Zp.made) P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' h0 hy
  obtain ⟨hk, hc⟩ := ProofFile.Honest.Sh.k12Keeps_form_354 h.toAtMg blk hb
  rw [hk]
  exact hc s s' h0 hy

/-- **The column `hK` at `fHead`, at all 358 numbers.** -/
theorem fHead_hK_whole (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) blk.place.kind blk.place s s' :=
  fHead_hK h (H2U.p12OfMade Zp.made) H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB
    (fHead_keeps_k12 h _ _ _ _)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k12
#print axioms ProofFile.Honest.FirstThread.fHead_hK_whole
