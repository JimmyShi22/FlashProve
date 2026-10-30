-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FiveAtShut.lean: ALL FIVE STATEMENTS THAT A SUB-PROTOCOL OWES AT ITS BORDER (`FiveAtBorder`,
Honest/Thread/FiveAtBorder.lean) AT "THE SEGMENT IS SHUT" OF EACH OF THE 25 SEGMENTS, at the first chain's thread of the online part as
a named term (`firstThread`, Honest/Thread/TheFirstThread.lean), at the prover that the maker `onlineProverFromPublicFiles` returns at the filling
`onlineProverPartsInUse`. Every Said, every table of falls.

  `shut_owes_none`       by Lean's kernel: the row at 14 l + `IM.nAt l` + 6 owes no item
  `k9_exchangeS_shut`    so `ExchangeS` holds there, at the first chain's letters, all of them variables
  **`five_at_shut`**      `FiveAtBorder (firstThread h parts w) Said fall (14 l + IM.nAt l + 6)`, l < 25

Where each comes from: "it plays": Honest/K9/AtFirstThread.lean · "behind": Honest/K9/BehindAtFirst.lean · "exchange": here · "rides past":
Honest/K9/RidesShut.lean · "accepted": Honest/K9/ShutAccepted.lean.

Limits. The maker's return hA and the head at that return are hypotheses. All five speak at every stand at which the thread's
invariant (`Thr`) holds; that it holds at any run is not proved here: where it holds at none they hold for nothing. This
sub-protocol has no round: nothing is sent or drawn in it. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtFirstThread
import Johnson.Desc.ProofFile.Honest.K9.BehindAtFirst
import Johnson.Desc.ProofFile.Honest.K9.RidesShut
import Johnson.Desc.ProofFile.Honest.K9.ShutAccepted
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

set_option maxRecDepth 1000000 in
/-- The row at "the segment is shut" owes nothing. -/
theorem shut_owes_none : ((List.range 25).all fun l =>
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes.isEmpty) = true := by
  decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **"Exchange" at "the segment is shut": nothing is owed.** -/
theorem k9_exchangeS_shut (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : ℕ) (hl : l < 25) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (14 * l + IM.nAt l + 6) := by
  refine (exchangeS_iff _ _).2 fun i hi => ?_
  have e : (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes = [] :=
    List.isEmpty_iff.1 (List.all_eq_true.1 shut_owes_none l (List.mem_range.2 hl))
  have hi' : i ∈ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes := hi
  rw [e] at hi'
  exact absurd hi' (List.not_mem_nil)

end

/-- **All five at "the segment is shut", at the first thread at the maker's return.** -/
theorem five_at_shut {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (fall : ℕ → TS → List Fmt.Drawn → Option String) (l : ℕ) (hl : l < 25) :
    FiveAtBorder (firstThread h parts w) Said fall (14 * l + IM.nAt l + 6) where
  plays := (playsS_k9_first I o Sz O hA h parts w l hl Said).2.2
  behind := (k9_behindS_first h parts w Said l hl).2.2
  exchange := k9_exchangeS_shut h.head A.H parts.script _ _ _ _ _ _ _ _ _ w Said l hl
  ridesPast := k9_ridesPastS_shut_exact h.head A.H parts.script _ _ _ _ _ _ _ _ w
    (fun _ _ _ a => a.1.1.1.1.1) _ Said l hl
  accepted := accepted_shut h.head A.H parts.script _ _ _ _ _ _ _ _ _ w l hl Said fall

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.shut_owes_none
#print axioms ProofFile.Honest.K9.k9_exchangeS_shut
#print axioms ProofFile.Honest.K9.five_at_shut
