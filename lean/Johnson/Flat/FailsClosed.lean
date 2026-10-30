-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/FailsClosed.lean: the tests on numbers that the theorems at the input whose rounds' data
and two decisions are letters (“the frame”: Johnson/Flat/TwoSizesAt.lean) ask of the data, as ONE
Bool (IT HAS NO CODE: it names the written rounds `frRds`, which have none: so it cannot run; the
sibling that has code: Johnson/Flat/Dec/FailsClosed.lean); data that FAIL CLOSED under it; and the two named hypotheses on the key file's and
the proof file's soundness at a decision that never says yes.

Why. Johnson/Flat/WiresAtSizes.lean's head: "NOTHING FAILS CLOSED: where a test says no, no law is
said." A description whose data are functions of the public files owes the tests at ALL files in
scope, where nothing can be evaluated. `dataAt` (OnBytes/Maker/Files.lean) shows the way for the makers'
own eight tests: the data of the rounds where the tests pass, and of three empty lists where they do
not. Here the same is done for the frame's tests.

Definitions, statements and proofs (Small for Full at the small size: NOT YET TYPED).
  `frameFitFull K v depthReq depthReqT DK DP`: the test: no round of the three files needs more than K
    blocks; in neither whole file a round has more than 64 bits of work or a tree deeper than 63; the
    compiled verifier's count of typed queries (`cntFrameFull`, Johnson/Flat/CountAtFrame.lean) is at
    most v; K + 2 < 2^49 (which a coding of the queries asks). `FrameFitFull`: what its yes says, test by test. `frameFitFull_iff`.
  `emptyWhole`: the data of three empty lists. `frameFitFull_empty`: the test says yes there, if K has
    blocks enough for the entry file's rounds, K + 2 < 2^49 and 13555 + depthReq + depthReqT ≤ v.
  `closeFullBy Kof v depthReq depthReqT p`: the pair p of data where the test says yes, and twice
    `emptyWhole` where it does not; Kof: the number of blocks as a function of the data.
    `closeFullBy_fit`: THE TEST SAYS YES AT IT, whatever p is, if it does at three empty lists.
    `closeFull K …`, `closeFull_fit`: the same at a K that does not hang on the data.
  `wholeIOR_never`: a file whose decision never says yes accepts nothing.
  `keySoundOfFull_of_never`, `proofSoundOfFull_of_never`: at such a decision `CompilerSoundnessConditionStatements.keySound` |
    `CompilerSoundnessConditionStatements.proofSound` (Johnson/Top/InnerCompiledVerifier.lean) hold, at every data and every εs, all errors 0.

Limits. A CASE SPLIT DOES A HYPOTHESIS's WORK (Ladder.lean's head, 9): at data that fail the test a
description so written has no rounds, and with decisions closed by the same test it REFUSES EVERY
PROOF there. So what these laws buy is worth as much as the test's yes at the files of interest: THAT
YES IS AN EVALUATION AND IS NOT MADE HERE, at any data. The two laws at a decision that never says
yes are TRUE AND EMPTY: they are for the branch that refuses, and say nothing of a decision that
accepts anything. Nothing on soundness of a real decision, on an honest prover or on hiding.
`below_timesShared_zero` is a twin of `below_times_zero` (Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean, at that file's own
list of zeros).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.CountAtFrame
import Johnson.Flat.TwoSizesAt
import OnBytes.Maker.Page.TestsHold
import Ior.KnowWide

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.Flat
open Iop Prob _root_.Run _root_.Run.PQ OnBytes.Maker OnBytes.Slice

/-- A list of zeros, a shared round's counted N times, is below every bound. -/
theorem below_timesShared_zero (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s) (c : ℝ≥0∞),
    Err.Below (Err.timesShared N A (Err.zero s)) c
  | [], _, _ => trivial
  | _ :: s, (a, A), c => ⟨by
      show (((match a.kind with | .lo => 0 | .sh => N * 0 : ℕ) : ℕ) : ℝ≥0∞) ≤ _
      cases a.kind <;> simp, below_timesShared_zero N s A c⟩

/-- **A file whose decision never says yes accepts nothing**, at every data. -/
theorem wholeIOR_never (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
    (never : ∀ x v₁ v₂ v₃, run x v₁ v₂ v₃ = false) (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Tr (chainsOf (ckP .two) D tF tJ t3).sh) :
    (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof.accept x y τ = false := by
  cases hacc : (reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).toInteractiveOracleProof.accept x y τ with
  | false => rfl
  | true =>
    have h' : ((reductionOfWholeFile (ckP .two) D tF tJ t3 silent run).out x y τ).isSome = true := hacc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h'
    cases u
    have h2 := (Option.ite_none_right_eq_some.1 hu).1
    simp only [never, Bool.and_false] at h2
    exact absurd h2 Bool.false_ne_true

/-- The state that is 0 everywhere meets the law on verifier messages with all errors 0. -/
theorem jointLaw_never {X : Type} (N : ℕ) (s : Shape) (A : RoundSplits s) (x : Fin N → Option X) :
    JointLaw N s A (Err.timesShared N A (Err.zero s))
      fun j => (x j).map fun _ => fun _ : PTr s => false :=
  BatchH4.jointLaw_of_verLaw N s A (Err.zero s) _ fun j S hS τ _ => by
    have hS' : (x j).map (fun _ => fun _ : PTr s => false) = some S := hS
    cases hx : x j with
    | none => rw [hx] at hS'; cases hS'
    | some a =>
      rw [hx] at hS'
      obtain rfl := Option.some.inj hS'
      rw [cnt_false fun c hc => Bool.false_ne_true hc]
      exact Nat.zero_le _

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm (cntWhole)
open _root_.Run.PQ (kMax)

/-! ## The test -/

/-- **The frame's tests on numbers at the full size, as one test.** K: the wiring's blocks; v: the
bound on the compiled verifier's count; the two depths of request trees. -/
def frameFitFull (K v depthReq depthReqT : ℕ) (DK DP : WholeD) : Bool :=
  decide (kThree .two DK frRds DP ≤ K) && DK.workFit && DK.depthFit && DP.workFit && DP.depthFit &&
    decide (cntFrameFull DK DP depthReq depthReqT ≤ v) && decide (K + 1 + 1 < 2 ^ 49)

/-- What its yes says, test by test. -/
structure FrameFitFull (K v depthReq depthReqT : ℕ) (DK DP : WholeD) : Prop where
  hk : kThree .two DK frRds DP ≤ K
  wK : DK.workFit = true
  dK : DK.depthFit = true
  wP : DP.workFit = true
  dP : DP.depthFit = true
  hcnt : cntFrameFull DK DP depthReq depthReqT ≤ v
  hK : K + 1 + 1 < 2 ^ 49

theorem frameFitFull_iff (K v depthReq depthReqT : ℕ) (DK DP : WholeD) :
    frameFitFull K v depthReq depthReqT DK DP = true ↔
      FrameFitFull K v depthReq depthReqT DK DP := by
  unfold frameFitFull
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩,
    fun h => ⟨⟨⟨⟨⟨⟨h.hk, h.wK⟩, h.dK⟩, h.wP⟩, h.dP⟩, h.hcnt⟩, h.hK⟩⟩

/-- Two tests more on the data, which a coding of the queries asks, follow from the tests on work. -/
theorem FrameFitFull.small {K v depthReq depthReqT : ℕ} {DK DP : WholeD}
    (h : FrameFitFull K v depthReq depthReqT DK DP) (a : ℕ) :
    OnBytes.Maker.Page.kindsAndWorkBelow256 (DK.at a) = true ∧ OnBytes.Maker.Page.kindsAndWorkBelow256 (DP.at a) = true :=
  ⟨OnBytes.Maker.Page.smallD_of_work _ h.wK, OnBytes.Maker.Page.smallD_of_work _ h.wP⟩

/-! ## Data that fail closed -/

/-- The data of three empty lists. -/
def emptyWhole : WholeD := ⟨0, [], [], [], id, id, id⟩

/-- At three empty lists each whole file's count is 7 and the depth of its request tree. -/
theorem cntFrameFull_empty (depthReq depthReqT : ℕ) :
    cntFrameFull emptyWhole emptyWhole depthReq depthReqT = 13555 + depthReq + depthReqT := by
  show (2 + ((1 + (0 + (1 + (0 + (1 + 0)))) + 1) + (0 * _ + (depthReqT + 1)))) + 13541 +
    (2 + ((1 + (0 + (1 + (0 + (1 + 0)))) + 1) + (0 * _ + (depthReq + 1)))) = _
  omega

/-- At three empty lists the three files' number of blocks is the entry file's. -/
theorem kThree_empty :
    kThree .two emptyWhole frRds emptyWhole = kMax (fun e k => (bsRound .two e k).b) frRds := by
  show max 0 (max _ 0) = _
  omega

/-- **The test says yes at three empty lists**, under three premises on numbers. -/
theorem frameFitFull_empty {K v depthReq depthReqT : ℕ}
    (hK : kMax (fun e k => (bsRound .two e k).b) frRds ≤ K) (hK2 : K + 1 + 1 < 2 ^ 49)
    (hv : 13555 + depthReq + depthReqT ≤ v) :
    frameFitFull K v depthReq depthReqT emptyWhole emptyWhole = true :=
  (frameFitFull_iff _ _ _ _ _ _).2
    ⟨kThree_empty ▸ hK, rfl, rfl, rfl, rfl, (cntFrameFull_empty depthReq depthReqT).le.trans hv,
      hK2⟩

/-- **The data at which the frame stands**: the pair where the test says yes, and three empty lists
twice where it does not. Kof: the wiring's number of blocks, as a function of the data. -/
def closeFullBy (Kof : WholeD → WholeD → ℕ) (v depthReq depthReqT : ℕ) (p : WholeD × WholeD) :
    WholeD × WholeD :=
  if frameFitFull (Kof p.1 p.2) v depthReq depthReqT p.1 p.2 then p else (emptyWhole, emptyWhole)

theorem closeFullBy_of_fit {Kof : WholeD → WholeD → ℕ} {v depthReq depthReqT : ℕ}
    {p : WholeD × WholeD} (h : frameFitFull (Kof p.1 p.2) v depthReq depthReqT p.1 p.2 = true) :
    closeFullBy Kof v depthReq depthReqT p = p := if_pos h

theorem closeFullBy_of_not {Kof : WholeD → WholeD → ℕ} {v depthReq depthReqT : ℕ}
    {p : WholeD × WholeD} (h : ¬ frameFitFull (Kof p.1 p.2) v depthReq depthReqT p.1 p.2 = true) :
    closeFullBy Kof v depthReq depthReqT p = (emptyWhole, emptyWhole) := if_neg h

/-- **The test says yes at the closed data, whatever the pair is**, if it does at three empty
lists. -/
theorem closeFullBy_fit {Kof : WholeD → WholeD → ℕ} {v depthReq depthReqT : ℕ}
    (h0 : frameFitFull (Kof emptyWhole emptyWhole) v depthReq depthReqT emptyWhole emptyWhole = true)
    (p : WholeD × WholeD) :
    frameFitFull (Kof (closeFullBy Kof v depthReq depthReqT p).1
        (closeFullBy Kof v depthReq depthReqT p).2) v depthReq depthReqT
      (closeFullBy Kof v depthReq depthReqT p).1 (closeFullBy Kof v depthReq depthReqT p).2 = true := by
  by_cases h : frameFitFull (Kof p.1 p.2) v depthReq depthReqT p.1 p.2 = true
  · rw [closeFullBy_of_fit h]
    exact h
  · rw [closeFullBy_of_not h]
    exact h0

/-- The same at a number of blocks that does not hang on the data. -/
def closeFull (K v depthReq depthReqT : ℕ) (p : WholeD × WholeD) : WholeD × WholeD :=
  closeFullBy (fun _ _ => K) v depthReq depthReqT p

theorem closeFull_fit {K v depthReq depthReqT : ℕ}
    (hK : kMax (fun e k => (bsRound .two e k).b) frRds ≤ K) (hK2 : K + 1 + 1 < 2 ^ 49)
    (hv : 13555 + depthReq + depthReqT ≤ v) (p : WholeD × WholeD) :
    frameFitFull K v depthReq depthReqT (closeFull K v depthReq depthReqT p).1
      (closeFull K v depthReq depthReqT p).2 = true :=
  closeFullBy_fit (Kof := fun _ _ => K) (frameFitFull_empty hK hK2 hv) p

/-- The entry file's written rounds at the full size need at most 140 blocks. By Lean's kernel. -/
theorem kMax_frRds_le : kMax (fun e k => (bsRound .two e k).b) frRds ≤ 140 := by decide +kernel

/-! ## A decision that never says yes -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}

/-- **The key file's named hypothesis at a decision that never says yes**: true and empty; at every
data and every εs; all errors 0. -/
theorem keySoundOfFull_of_never (never : ∀ r v₁ v₂ v₃, runK r v₁ v₂ v₃ = false)
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T) :=
  ⟨Err.zero _, below_timesShared_zero _ _ _ _, fun x y _ =>
    Doomed.of_forall _ _ fun τ =>
      wholeIOR_never (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK never x y τ⟩

/-- **The proof file's named hypothesis at a decision that never says yes**: true and empty; at every
data and every εs; all errors 0; the witness map is constant. -/
theorem proofSoundOfFull_of_never (never : ∀ x v₁ v₂ v₃, runP x v₁ v₂ v₃ = false)
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T) :=
  ⟨fun _ _ _ => (), Err.timesShared _ _ (Err.zero _), below_timesShared_zero _ _ _ _, fun rec =>
    (sndBKT_laws _ _ _ _ _ _ _ _ _ _).2
      ⟨fun _ h => (by cases h), fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
        fun _ _ _ h => (by cases h),
        fun y x τ _ hacc => (Bool.false_ne_true ((wholeIOR_never (DP.at frS.P.T.a) (front₀ rP)
          (join₀ rP) ByteArray.empty silP runP never (x, rec) y τ).symm.trans hacc)).elim,
        fun _ x => jointLaw_never _ _ _ x⟩⟩

end

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.wholeIOR_never
#print axioms VerifiableInference.OnPublicFiles.frameFitFull_iff
#print axioms VerifiableInference.OnPublicFiles.closeFullBy_fit
#print axioms VerifiableInference.OnPublicFiles.closeFull_fit
#print axioms VerifiableInference.OnPublicFiles.kMax_frRds_le
#print axioms VerifiableInference.OnPublicFiles.keySoundOfFull_of_never
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFull_of_never
