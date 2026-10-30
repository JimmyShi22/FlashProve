-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/ArmsAtTheFirstScript.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the
place W): WHERE THE LAST CHAIN's THREAD (lastAt, K12/AtFile/WTable.lean) IS LAID OVER THE TABLES OF
THE FIRST CHAIN's THREAD AT THE FIRST CHAIN's SCRIPT (lettersHead at firstScriptAt), UNDER THE
LIBRARY's HYPOTHESIS ON THE FIRST CHAIN, AT WHAT THE MAKER RETURNS AT THE WIDER FILLING, AND AT THE
MAKER's WRITTEN BOOK: FirstArms, WITH NO PREMISE LEFT ON THE FIRST THREAD's TABLES.

WHAT IT IS NOT.
  * It is conditional: on the hypothesis (P5J.AtMgA: the full size and the format's second hash function
    alone) and its opening O; on hA, that the maker returns A at the filling onlineProverPartsInUse; on
    hB, that A's book is the one made of the written description; on made, that jobRealW returns a
    job at the filling's letters.
  * At lastAt over these tables: that another author's last thread is that thread is not said here.
  * It pays FirstArms alone: trees 0 and 1 of the three that the clause "taken" speaks of. It does
    not say that a stand is reached, that a part plays or that a verifier accepts. No count moves
    by it.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; two theorems.

  armsAtTheFirstScript     the first thread's tables of its own trees 1 and 82 are the tables of the
                           first opening's job and of W's sending's job, in the very terms that
                           firstArmsAtLastAt asks; the second is fixed by the rounds in front of
                           member number 356
  firstArmsAtTheFirstScript   **FirstArms at lastAt over these tables**

CALLED. firstArmsAtLastAt (TakenAtTheLastThread.lean). Of other authors: arm_two, arm_w
(AtFullSide/K12/FirstArmsTables.lean); atPure_at_laid_ground (Honest/AtHeadGround.lean).
-/
import AtFullSide.K12.Part4.TakenAtTheLastThread
import AtFullSide.K12.FirstArmsTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Chain Block FileDescription Place Strs)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.K12.AtProof (jobRealW inOf)
open ProofFile.Honest.K12.AtFile (FirstArms lastAt)
open ProofFile.Honest.K1 (LocB readersB firstScriptAt arm_two arm_w lotNo)
open ProofFile.Honest.FirstThread (lettersHead WtF)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **The first thread's tables of its own trees 1 and 82, in the terms that firstArmsAtLastAt
asks**, and the count that fixes the second. -/
theorem armsAtTheFirstScript (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (_root_.Desc.K14.Law.seatZ A.Z Np) (_root_.Desc.K14.Law.secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    (∀ k v hd, (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.table (.own 1) k v hd =
      K1.treeTbl 0 (inOf (readersB I A.Z))
        (K1.placeJob (X := Unit) (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf A.Z)) (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩)
          (K1.firstFold Bs.G₀.first) (K1.lotData S A.Z Bs.G₀)) () 1 k v hd) ∧
    (∀ k v hd, (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.table (.own 82) k v hd =
      K1.treeTbl 0 (inOf (readersB I A.Z))
        (K1.wJobAt (X := Unit) A.Z.first (K1.wGp A.Z) 4 wMsgFull
          (lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (K13.wDataAt Op.pile A.Z Bs.G₀)) () 0 k v
        hd) ∧
    (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
      w).thread.fixed (.own 82) = roundsTo cF.blocksInOrder 356 := by
  obtain ⟨-, ground, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨tableIndex, -⟩ := arm_two h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain ⟨tableW, fixedW⟩ := arm_w h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
  rw [← ground]
  exact ⟨tableIndex, tableW, fixedW⟩

variable {X₀ Wt W₂ : Type}
  (H : Prover W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells X₀ Unit)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : LocB W₀ → VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × TS))
  (order : S₃ → Prop)
  (ends : Coins A.B → LocB W₀ → List Fmt.Drawn → (ProofFile.InstPub × TS) × Desc.K14.St)
  (wit : Coins A.B → LocB W₀ → List Fmt.Drawn → Wt)
  (r₁ n₀ : ℕ) (toCommon : LocB W₀ → W₂)
  (tb₂ : Fmt.TreeSource → Coins A.B → W₂ → List Fmt.Drawn → Place × Table)
  (fx₂ : Fmt.TreeSource → ℕ) (J : TestJob (LocB W₀) Unit)
  (itemL t₁ t₂ : ℕ) (VdL : LocB W₀ → Prop) (RdL : ℕ → LocB W₀ → S₃ → Prop)
  (KpL : Place → S₃ → S₃ → Prop) (wL : LocB W₀)

/-- **FirstArms at the last chain's thread laid over the first chain's thread's tables at the first
chain's Script.** The letters of the two threads are free. -/
theorem firstArmsAtTheFirstScript (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (_root_.Desc.K14.Law.seatZ A.Z Np) (_root_.Desc.K14.Law.secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok A.B)
    (test : ℕ → TS → Option String) (carryX : ℕ → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : ℕ) (Vd : LocB W₀ → Prop) (Rd : ℕ → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) (Fd : FileDescription ProofFile.Inst)
    (enter : Fd.S₃ → Except String T12) (no : Place → ℕ) (weights : LocB W₀ → Weights)
    (rand : Desc.K14.P14 → LocB W₀ → TableRand) {M : ManyJob (LocB W₀) Unit}
    (made : jobRealW S Fd enter Op.pile no (readersB I A.Z) weights rand A.Z Bs.G₀ = some M)
    (Said : ℕ → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    FirstArms (lastAt (Zp := A.Z) (Np := Np) (cF := cF) H N Mg ML PL order ends wit r₁ n₀ toCommon
      (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.table tb₂
      (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.fixed fx₂ J () itemL t₁ t₂ VdL RdL KpL wL) Said M := by
  obtain ⟨tableIndex, tableW, fixedW⟩ :=
    armsAtTheFirstScript h O hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact firstArmsAtLastAt H N Mg ML PL order ends wit r₁ n₀ toCommon _ tb₂ _ fx₂ J () itemL t₁ t₂
    VdL RdL KpL wL h O hB S Fd enter Op.pile no (readersB I A.Z) weights rand made Said _ _ ()
    tableIndex tableW fixedW

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.armsAtTheFirstScript
#print axioms AtFullSide.K12.Part4.firstArmsAtTheFirstScript
