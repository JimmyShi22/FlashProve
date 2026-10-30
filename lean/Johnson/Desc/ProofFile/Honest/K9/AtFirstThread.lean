-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/AtFirstThread.lean: WHAT STANDS OF THE KIND K9 AT THE FIRST CHAIN's THREAD OF THE ONLINE PART
(`firstThread`, Honest/Thread/TheFirstThread.lean) AT THE PROVER THAT THE MAKER RETURNS AT THE FILLING `onlineProverPartsInUse`
(Honest/K1/Law/WSideAtFill.lean): the premise "no side of this kind stands in the prover's first list" of this folder's laws is
paid there, so that they stand with no premise on the prover. The index I and its type are variables.

  **`playsS_k9_first`**   l < 25, every Said: `PlaysS (firstThread h parts w) Said` at the numbers 14 l + `IM.nAt l` + 2, + 4, + 6:
                        the first of the five statements at all 75 borders of this kind
  **`own_stays_fHead`**   the hypothesis hB of `fHead_hlay` (Honest/Thread/FHeadStays.lean), to the letter: in a feed-forward
                        segment what the segment's own rounds returned stays over the batching

Limits. The maker's return hA and the head at that return are hypotheses. `PlaysS` speaks at every stand at which the thread's
invariant (`Thr`, Honest/Thread/Thr.lean) holds; that it holds at any run is not proved here. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatPlays
import Johnson.Desc.ProofFile.Honest.K9.NoSideAtBase
import Johnson.Desc.ProofFile.Honest.K9.KeepsReadings
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- **The first of the five, at all 75 borders of this kind, at the first thread at the maker's return.** -/
theorem playsS_k9_first {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (l : ℕ)
    (hl : l < 25) (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    PlaysS (firstThread h parts w) Said (14 * l + IM.nAt l + 2) ∧
      PlaysS (firstThread h parts w) Said (14 * l + IM.nAt l + 4) ∧
      PlaysS (firstThread h parts w) Said (14 * l + IM.nAt l + 6) :=
  playsS_k9_at_head h.head A.H parts.script _ _ 0 _ _ 339 _ _ _ w l hl (no_side_at_base I o Sz O hA) Said

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **What a feed-forward segment's own rounds returned stays over the batching**, in the form in which the first chain's
table of riders asks it. -/
theorem own_stays_fHead : ∀ g, g < 12 → ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.keeps (28 * g + 9) s s' →
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  intro g hg s s' hk
  obtain ⟨Lk, p, ww, Sd⟩ := seated_at_head h (2 * g) (by omega)
  have hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread.bs[28 * g + 9]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
    have e := Sd.batching
    rw [if_neg (by omega : ¬ 2 * g = 24)] at e
    have e2 : 14 * (2 * g) + 7 + 2 = 28 * g + 9 := by omega
    rw [e2] at e
    exact e
  have hK : fHead Zp cF G take P11 p12 P13 KindName.K9 (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place s s' :=
    (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd (fHead Zp cF G take P11 p12 P13) w hb
      (by rw [Sd.seat]) s s').1 hk
  exact own_over_batching h (by omega) Sd hK

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.playsS_k9_first
#print axioms ProofFile.Honest.K9.own_stays_fHead
