-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshCoins.lean: the closing of a segment (K10): the pairing of the field fresh of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean), brought down to coins. The sender of the fresh mask lays its table of its own
2 k + 1 coins; the closing's part spends a run of 2 k + 1 values. Where the two are the same values, number by number, and
the witness's table is the sender's, the pairing holds.

  `lay_congr`           the sending's laying of a fold's fresh table reads its first 2 k + 1 coins alone, where the stage has
                    room for the packing
  **`fresh_of_coins`**    the pairing under `CloseBase`, from: the witness's table at the mask's message is the laying of coins
                    c; c agrees with the values of the words u below 2 k + 1
  `fresh_message_mask`  what the shared text of a message's rows (`messageRows`, Honest/K2/Sending.lean) lays at a fold's fresh
                    mask, at the table `freshTable`: inside the mask table, the laying of the 2 n + 1 coins that it has read
                    off its stretch, which begin at `fromE`
  `fresh_message_coin`  these coins, one by one, are the stretch's own

Limits. That the witness's table is the sender's, and that the sender's coins are the spent run's values, are premises. No
head, thread or prover is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFreshAt
import Johnson.Desc.ProofFile.Honest.K12.HideCongr
import Johnson.Desc.ProofFile.Honest.K2.Law.Laid
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads
import Johnson.Desc.ProofFile.Honest.K2.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE Sg readE)
open Cb (HIdx sVars)
open Johnson.Prover.Link (Pairs)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.K2.Honest (zeroG)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open ProofFile.Honest.K12 (packing_at)
open ProofFile.Honest.K2 (Stretch messageRows freshTable fromE inMaskOf)
open ProofFile.Honest.K10.LeftIs (stageB freshB)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- The laying of a fold's fresh table reads its first 2 k + 1 coins alone. -/
theorem lay_congr (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) (c c' : Nat → GE)
    (h : ∀ i, i < 2 * (s.h + s.g) + 1 → c i = c' i) (r j : Nat) :
    (⟨s.h + s.g, s.h⟩ : K1.Ride).lay c r j = (⟨s.h + s.g, s.h⟩ : K1.Ride).lay c' r j := by
  rw [← packing_at s hl, ← packing_at s hl, K12.Light.hideAt_congr _ c c' h]

/-- **The field fresh's pairing under `CloseBase`, from coins.** -/
theorem fresh_of_coins {P : Par} {D : BaseData} {s : First.S} (Hb : CloseBase P (K9.recOf s) D) {Cells Tok : Type}
    (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) {n' : Nat} (hn : n' = P.k) (u : Fin (2 * n' + 1) → OnBytes.E)
    (c : Nat → GE) (hc : ∀ i, i < 2 * n' + 1 → c i = readE (wordsAll u i))
    (hT : ∀ b j, b < 2 ^ (stageB D (K9.recOf s)).h → j < (stageB D (K9.recOf s)).Z.l →
      tabAt s.st.codes arr (seatBy noFirst s.book) s.st v D.m true b j =
        (⟨(stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g, (stageB D (K9.recOf s)).h⟩ : K1.Ride).lay c b j)
    (W : HIdx (sVars GE 2 ((stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g)) → GE) (hW : CoefOf u W) :
    Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
      (freshB D (K9.recOf s) (wordsFirst arr s.st s.book v)) := by
  have hk : n' = (stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g :=
    hn.trans (Hb.stretch.trans (LeftIs.stageB_k Hb))
  refine fresh_of_base Hb arr v hn u (fun b j hb hj => ?_) W hW
  rw [hT b j hb hj]
  exact lay_congr _ (room_of_base Hb) _ _ (fun i hi => hc i (by rw [hk]; exact hi)) b j

/-- What the shared text lays at a fold's fresh mask. -/
theorem fresh_message_mask {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {n : Nat} {data : Nat → Nat → Cb.Gl.E}
    {k : Stretch} {Rr : Rows} (h : messageRows freshTable codes s (some n) data k = .ok Rr) :
    ∃ cM : Array Cb.Gl.E, k.es (fromE codes s) (inMaskOf codes s (some n)) = .ok cM ∧
      ∀ r i, r < s.maskRows → i < (codes.mask.getD s.maskCode default).ell →
        Rr.mask r i = (⟨n, OnBytes.ceilLog2 s.maskRows⟩ : K1.Ride).lay (cM.getD · zeroG) r i := by
  obtain ⟨-, -, -, cF, cE, cM, cT, -, -, hM, -, rfl⟩ := K2.messageRows_laid h
  refine ⟨cM, hM, fun r i hr hi => ?_⟩
  show (if (!(decide (r < s.maskRows) && decide (i < (codes.mask.getD s.maskCode default).ell))) = true
    then zeroG else freshTable n (OnBytes.ceilLog2 s.maskRows) (cM.getD · zeroG) r i) = _
  rw [decide_eq_true hr, decide_eq_true hi]
  rfl

/-- The coins that it has read are the stretch's own, from `fromE` on. -/
theorem fresh_message_coin {codes : OnBytes.Codes} {s : OnBytes.OracleShape} {n : Nat} {k : Stretch}
    {cM : Array Cb.Gl.E} (hM : k.es (fromE codes s) (inMaskOf codes s (some n)) = .ok cM) {i : Nat}
    (hi : i < 2 * n + 1) : k.coins.eAt (fromE codes s + i) = .ok (cM.getD i zeroG) :=
  K2.Reads.es_at hM hi zeroG

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.lay_congr
#print axioms ProofFile.Honest.K10.fresh_of_coins
#print axioms ProofFile.Honest.K10.fresh_message_mask
#print axioms ProofFile.Honest.K10.fresh_message_coin
