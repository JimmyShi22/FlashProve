-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/AtFirstScript.lean: the five debts of the kind K11 at number 346 of the first thread
with the first chain's written script (firstScriptAt, AtFullSide/K1/FirstScript.lean) in the script's
place, as one value of FiveAtBorder. What the kind asks of the script is proved here; at the online
prover's index only the maker's return, the head at it and the condition on Said stay premises.

  k11_five_at_firstScript the five, at any reader of the index that holds an index in range
  k11_five_at_matrix      the five at the online prover's index: premises: the maker's return, the head
                          at it, and that what is said at each border is of the chain's own words

Limits. Each of the five assumes that the thread's invariant holds in front of the member. That it
holds at any border at any run is not shown here. The prover is the base prover, not the online one,
which reads it through. The maker's return and the head at it are premises. That the prover's sides
of the kinds K2 and K12 play the script's texts is not shown here, and the tie on the mask row reads
K2's text. None of the five says that a step's coins are lent: that is the lending statement, K11Lends.
-/
import AtFullSide.K11.AtFirstThread
import AtFullSide.K11.ScriptAtTheTerm
import AtFullSide.K11.MatrixAtTheTerm
import AtFullSide.K1.FirstScript
import Johnson.HonestTrace.Joint.ReadsLightPaid
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.HonestTrace (Sz)
open OnBytes.Slice (frS frZ)
open Bind.ForProver (cellsOfF)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.K1
open ProofFile.Honest.K11
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.AtFiles.HonestTerm.K11Term

/-- Coins, all zero: what stands where a book does not lend. -/
def csZero (d : Due) : Cs d := ⟨fun _ => 0, fun _ => 0⟩

/-- The same for a list of counts. -/
def csAllZero : (l : List (String × Due)) → CsAll l
  | [] => ()
  | d :: ds => (csZero d.2, csAllZero ds)

variable {W₀ : Type} {I : WiderIn W₀} {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The five debts of the kind at number 346 of the first thread with the written script**, at a
reader of the index whose range holds indices that it reads. -/
theorem k11_five_at_firstScript (hM : baseMaker I Z = .ok A) (hd : HeadAtReturn Z A)
    (numbers : FallNumbers) (w : Input W₀)
    (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop) (hS : ∀ b k m, Said b k m → SaidOk b k m)
    (hm : ∀ w₀, I.inRange w₀ = true → ∃ i : Cm.Idx,
      Holds (cellsOfF frS frZ 402653181 numsRef (I.weights A.Z w₀).entry) i ∧
      ∀ a b, algebraMap Cb.Gl.F Cb.Gl.E ((I.weights A.Z w₀).entry a b) =
        ((i.mat a b : ℤ) : Cb.Gl.E))
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder (firstThread hd ⟨firstScriptAt I Sz.ref openHonest A hd.firstChain, numbers⟩ w)
      Said fall 346 := by
  obtain ⟨Bs, base, O⟩ := hd.head.laid.opened
  have hB := O.made
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground hd.head.laid O.blank hM
  have F := joinFit_first (I := I) (S := Sz.ref) (Op := openHonest) hd.head hM
  have hA' : ∀ v, ReadyInput hd.description A.H v → I.inRange v.w₀ = true := fun v hv => by
    have e := (atPure_ok hM).2.2.2.2.2.1
    have hr : A.H.inRange v.w₀ = true := hv.2.1
    rw [e] at hr
    exact hr
  let c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf A.Z Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf A.Z Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf A.Z Bs.G₀).lay) :=
    (csZero _, csAllZero _, csAllZero _)
  have hO : otherSendersAt I Sz.ref A hd.firstChain =
      (ProofFile.Honest.K2.switchShareAt A.B hd.firstChain.blocksInOrder 0 A.Z Bs.G₀
        (ProofFile.Honest.K2.withSwitchData Sz.ref (K1.lotData Sz.ref) A.Z Bs.G₀) (readersB I A.Z)
        noTree).add (testShareAt I Sz.ref A hd.firstChain) := by
    rw [← eG]
    rfl
  have hP : (jobTwoAt Sz.ref A.Z A.G).P =
      VerifiableInference.Desc.K1.firstPar Bs.G₀.first (VerifiableInference.Desc.K1.gpOf A.Z) := by
    rw [← eG]
    rfl
  have hR : (jobTwoAt Sz.ref A.Z A.G).ride = K1.rideOf (K1.firstFold Bs.G₀.first) := by
    rw [← eG]
    rfl
  have hSc := k11_script_under_head (I := I) hM hB hd.head 0
    (fun w₀ => cellsOfF frS frZ 402653181 numsRef (I.weights A.Z w₀).entry) tokB (witB I A.Z) ()
    (k1MembersW (jobTwoAt Sz.ref A.Z A.G) (jobLaterAt Sz.ref A.Z A.G) (jobWAt openHonest A.Z A.G))
    (jobTwoAt Sz.ref A.Z A.G) (jobLaterAt Sz.ref A.Z A.G) (jobWAt openHonest A.Z A.G) rfl
    (readersB I A.Z) noTree (testShareAt I Sz.ref A hd.firstChain)
    (otherSendersAt I Sz.ref A hd.firstChain) hO
    (fallsAfterBatching (firstFalls A numbers) hd.firstChain)
    (carryExact A.Z (P5J.At.arr A.Z)) 0 hd.description.t₁ hd.description.t₂
    (ReadyInput hd.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses hd)) w c₀ _ F hP hR
    (fun v hv => OnBytes.HonestTrace.U3.Fit.readsLight_of_okStart hd.head O hv.1)
  have hC : K11CellsQ (firstScriptAt I Sz.ref openHonest A hd.firstChain)
      (_root_.K11.parOf A.Z Bs.G₀).lay (I.weights A.Z) (ReadyInput hd.description A.H) :=
    cellsOfIndex A.B W₀ IndexCommitterCoins Cells _ _ _ _ fun v hv => hm v.w₀ (hA' v hv)
  obtain ⟨p1, p2, p3, p4, p5⟩ := k11Five_at_firstThread hM hd
    ⟨firstScriptAt I Sz.ref openHonest A hd.firstChain, numbers⟩ w Said hB c₀ hS hSc hC
  exact ⟨p1, p3, p4, p5, p2 fall⟩

/-- **The five at the online prover's index.** -/
theorem k11_five_at_matrix {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hM : baseMaker matrixInput Z = .ok A) (hd : HeadAtReturn Z A) (numbers : FallNumbers)
    (w : Input FullSizeMatrix) (Said : Nat → Coins A.B → Mid (Input FullSizeMatrix) Unit → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) :
    FiveAtBorder
      (firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩ w)
      Said fall 346 := by
  refine k11_five_at_firstScript hM hd numbers w Said hS (fun M hr => ?_) fall
  obtain ⟨i, hi⟩ := holds_of_inRange hr
  have e : cellsOfF frS frZ 402653181 numsRef (matrixInput.weights A.Z M).entry = M := by
    funext y c
    show algebraMap Cb.Gl.F Cb.Gl.E (AtPublicFiles.Key.cellsReader M y.val c.val) = M y c
    rw [reader_is_mat hi, hi.1 y c]
  refine ⟨i, ?_, fun a b => reader_is_mat hi a b⟩
  rw [e]
  exact hi

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_five_at_firstScript
#print axioms AtFullSide.K11.k11_five_at_matrix
