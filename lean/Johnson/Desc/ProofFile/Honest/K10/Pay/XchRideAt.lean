-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchRideAt.lean: the closing of a segment (K10): one clause of the field stand of
`FreshByShared` (Pay/XchFreshField.lean): the table that rides in the sender's message is the table of the closing's fold: of the
closing's count of row variables, and of the stage's count of row variables on the mask table.

  **`stage_h_zero`**    under the head, at a reached state in front of a closing, under `CloseBase`: the stage's count of row variables
                    on the mask table is 0. Why: the fresh mask's message has one mask row (`mask_message`, Pay/FoldAt.lean), and
                    2 ^ h mask rows (`mask_shape_of_base`, Pay/XchFreshAt.lean)
  **`ride_at_stand`**   at a stand of the first chain's thread in front of the closing: where a table of the numbers (kq, 0) rides in
                    message number n and the closing's count of row variables is kq: the clause

Limits. The head is a premise. What rides in the sender's message (hJ), and the closing's count (hk), are premises. The full size
and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSwitchHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.LeftIs (stageB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **In front of a closing the stage's count of row variables on the mask table is 0.** -/
theorem stage_h_zero (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {P : Par} {D : BaseData}
    (Hb : CloseBase P (K9.recOf s) D) : (stageB D (K9.recOf s)).h = 0 := by
  obtain ⟨y, hy, hrows⟩ := mask_shape_of_base Hb
  obtain ⟨y', hy', -, h1, -⟩ := mask_message h hl hr hf Hb.mask
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  rw [h1] at hrows
  rcases Nat.eq_zero_or_pos (stageB D (K9.recOf s)).h with e | e
  · exact e
  · have h2 : 1 < 2 ^ (stageB D (K9.recOf s)).h := Nat.one_lt_two_pow (Nat.ne_of_gt e)
    omega

variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **The table that rides in the sender's message is the closing's fold's.** -/
theorem ride_at_stand {Wj Xj : Type} (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : Nat}
    {pw : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl} (Td : Tied cF Zp l pw Qc blk)
    (J : K1.SendJob Wj Xj) {n kq : Nat} (hJ : J.ride n = some ⟨kq, 0⟩) (hk : Qc.k = kq) :
    ∀ {k s m En ds y cols s'}, StepAt 𝕋 Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → J.ride n = some ⟨Qc.k, (stageB D (K9.recOf s)).h⟩ := by
  intro k s m En ds y cols s' St D Hb
  obtain ⟨hr, hf, hl, -⟩ := stand_reached h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td St
  rw [stage_h_zero h hl hr hf Hb, hk]
  exact hJ

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.stage_h_zero
#print axioms ProofFile.Honest.K10.ride_at_stand
