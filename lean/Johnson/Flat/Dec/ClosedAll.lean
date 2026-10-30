-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/ClosedAll.lean: at the full-size frame with the entry file's three letters: THE CLOSING, WHOLE: the
three files' data AND THE TWO DEPTHS of request trees fail closed together under the one test on numbers
(`sizeNumbersFitAtFullSize`, Johnson/Flat/Dec/FailsClosed.lean); THE THREE DECISIONS are closed by a gate; and what follows at a
frame so written, stated.

Why. In Johnson/Flat/Dec/FailsClosed.lean (F1) the depths stand beside the closed data and INSIDE
the count, and the premise h0 is owed at these depths: so "at every public file" holds there only
where the depths are numerals; (F2) no definition there closes the decisions, which is the whole
matter for the three hypotheses on soundness at the branch that refuses; and the law "the verifier's
own count of queries is at most v at the closed frame" is not stated there.

Main names.
  `FrameAll`: the three files' data and the two depths. `emptyAll`: no rounds; both depths 0. `FrameAll.fit p K v`: the test.
  `closeAll Kof v p`: p where the test says yes at K := Kof p; `emptyAll` where it does not. `liveAll Kof v p`: that yes.
  `closeAll_fit`: THE TEST SAYS YES AT THE CLOSED VALUE, WHATEVER p IS, under two premises ON NUMERALS AND Kof ALONE:
    Kof emptyAll + 2 < 2^40 and 17 ≤ v. No premise on a depth is left.
  `gatedFileDecision live run`, `gatedLinkDecision live dec`: the decision behind a gate: "live and run". `gate3_true`, `gate1_true`: at yes it is the
    decision itself.
  `tVC_closed`: at the closed value, at every other letter: tVC of the frame's wire is at most v.
  `compilerSoundnessConditionsAtFullSize_closed`: at the closed value and the three gated decisions: the fifteen of `CompilerSoundnessConditions` from: the two premises on
    numerals; commitment; keySound, entrySound, proofSound WHERE THE TEST SAYS YES AT p.
  (That the test says yes at the written lists of the full-size example, at 24086 blocks, v = 2^63
    and depths 6 and 0: `frameFitFullD_written`, Johnson/Flat/Dec/FitAtWritten.lean.)
  `closedAll_hasCode`: outside the noncomputable section: Lean compiles a call of the closing and of the gates.

Limits. THE CLOSING IS A CHANGE OF THE VERIFIER's TEXT: a test on what is made of the public files alone, in front of the three
decisions: it asks more; it is harmless just where it says yes. WHERE IT SAYS NO THE VERIFIER REFUSES ALL, AND THE THREE HYPOTHESES ON
SOUNDNESS HOLD THERE FOR NOTHING. That it says yes at the release's files: a theorem at the written lists; evaluated at the
plan's own data. Nothing is shown of any decision. NO VALUE OF THIS FRAME HAS RUN ON A REAL PROOF. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.CoreOfFit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The data and the depths -/

/-- The three files' data of rounds and the depths of the two request trees. -/
structure FrameAll where
  DK : WholeD
  DP : WholeD
  ds : List TypedOracleCompiler.Run.PQ.RD
  xs : List _root_.Run.PQ.XO
  depthReq : ℕ
  depthReqT : ℕ

/-- No rounds at all; both depths 0. -/
def emptyAll : FrameAll := ⟨emptyWhole, emptyWhole, [], [], 0, 0⟩

/-- The test on numbers at such a value. -/
def FrameAll.fit (p : FrameAll) (K v : ℕ) : Bool :=
  sizeNumbersFitAtFullSize K v p.depthReq p.depthReqT p.DK p.DP p.ds p.xs

/-- The test's yes at p, at the number of blocks that Kof makes of p. -/
def liveAll (Kof : FrameAll → ℕ) (v : ℕ) (p : FrameAll) : Bool := p.fit (Kof p) v

/-- **The value at which the frame stands.** -/
def closeAll (Kof : FrameAll → ℕ) (v : ℕ) (p : FrameAll) : FrameAll :=
  if liveAll Kof v p then p else emptyAll

theorem closeAll_of_live {Kof : FrameAll → ℕ} {v : ℕ} {p : FrameAll} (h : liveAll Kof v p = true) :
    closeAll Kof v p = p := if_pos h

theorem closeAll_of_dead {Kof : FrameAll → ℕ} {v : ℕ} {p : FrameAll}
    (h : liveAll Kof v p = false) : closeAll Kof v p = emptyAll :=
  if_neg (by rw [h]; exact Bool.false_ne_true)

/-- **The test says yes at the closed value, whatever p is.** -/
theorem closeAll_fit {Kof : FrameAll → ℕ} {v : ℕ} (hK : Kof emptyAll + 1 + 1 < 2 ^ 40)
    (hv : 17 ≤ v) (p : FrameAll) :
    (closeAll Kof v p).fit (Kof (closeAll Kof v p)) v = true := by
  cases h : liveAll Kof v p with
  | true =>
    rw [closeAll_of_live h]
    exact h
  | false =>
    rw [closeAll_of_dead h]
    exact frameFitFullD_empty (depthReq := 0) (depthReqT := 0) hK (by omega)

/-! ## The decisions -/

/-- A file's decision behind a gate. -/
def gatedFileDecision {α : Type} (live : Bool) (run : α → PQ.View → PQ.View → PQ.View → Bool) :
    α → PQ.View → PQ.View → PQ.View → Bool := fun x v₁ v₂ v₃ => live && run x v₁ v₂ v₃

/-- The entry file's decision behind a gate. -/
def gatedLinkDecision {α : Type} (live : Bool) (dec : α → PQ.View → Bool) : α → PQ.View → Bool :=
  fun x v => live && dec x v

theorem gate3_true {α : Type} (run : α → PQ.View → PQ.View → PQ.View → Bool) :
    gatedFileDecision true run = run := rfl

theorem gate1_true {α : Type} (dec : α → PQ.View → Bool) : gatedLinkDecision true dec = dec := rfl

theorem gate3_dead {α : Type} {live : Bool} (h : live = false)
    (run : α → PQ.View → PQ.View → PQ.View → Bool) (x : α) (v₁ v₂ v₃ : PQ.View) :
    gatedFileDecision live run x v₁ v₂ v₃ = false := by
  subst h
  rfl

theorem gate1_dead {α : Type} {live : Bool} (h : live = false) (dec : α → PQ.View → Bool) (x : α)
    (w : PQ.View) : gatedLinkDecision live dec x w = false := by
  subst h
  rfl

/-! ## At a frame so written -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
  (Kof : FrameAll → ℕ) (v : ℕ) (p : FrameAll)

/-- The closed value. -/
local notation "q" => closeAll Kof v p

/-- **The compiled verifier's own count of typed queries at the closed value is at most v**, at every
other letter of the frame. -/
theorem tVC_closed (hK : Kof emptyAll + 1 + 1 < 2 ^ 40) (hv : 17 ≤ v)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (early : X → X) (salt K : ℕ)
    (P : (threeProtocolsAtFullSize A R (q).DK (q).DP runK runP (q).ds (q).xs dec rK rP (q).depthReq early
      salt).Provers) :
    tVC (wireOfFullD A R (q).DK (q).DP runK runP (q).ds (q).xs dec rK rP (q).depthReq early salt P K
      (q).depthReqT) ≤ v := by
  rw [tVC_wireOfFullD]
  exact (frameFitFullD_parts (closeAll_fit hK hv p)).hcnt

variable {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {early : X → X} {salt : ℕ}

/-- **The fifteen at the closed value and the three gated decisions.** The three hypotheses on soundness
are asked only where the test says yes at p. -/
theorem compilerSoundnessConditionsAtFullSize_closed (hK : Kof emptyAll + 1 + 1 < 2 ^ 40) (hv : 17 ≤ v)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) (q).DK (q).DP (gatedFileDecision (liveAll Kof v p) runK)
      (gatedFileDecision (liveAll Kof v p) runP) (q).ds (q).xs (gatedLinkDecision (liveAll Kof v p) dec) rK rP (q).depthReq
      early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E (q).DK (q).DP (gatedFileDecision (liveAll Kof v p) runK)
      (gatedFileDecision (liveAll Kof v p) runP) (q).ds (q).xs (gatedLinkDecision (liveAll Kof v p) dec) rK rP (q).depthReq
      early salt (Kof (q)) P)
    (hT : T.depthReqT = (q).depthReqT)
    (kS : liveAll Kof v p = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T))
    (eS : liveAll Kof v p = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T))
    (pS : liveAll Kof v p = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T))
    (cm : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataAtFullSize T)) : CompilerSoundnessConditions (soundnessAnalysisDataAtFullSize T) := by
  have hfit : sizeNumbersFitAtFullSize (Kof (q)) v (q).depthReq T.depthReqT (q).DK (q).DP (q).ds (q).xs =
      true := by
    rw [hT]
    exact closeAll_fit hK hv p
  have hl : RemainingSoundnessConditionsAtFullSize T :=
    remainingSoundnessConditionsAtFullSize_live (liveAll Kof v p) (fun h => gate3_dead h runK) (fun h => gate1_dead h dec)
      (fun h => gate3_dead h runP) kS eS pS cm
  exact compilerSoundnessConditionsAtFullSize_of_fit hfit hl

end

end VerifiableInference.OnPublicFiles

end

/-- OUTSIDE THE NONCOMPUTABLE SECTION: Lean compiles this call of the closing and of the two gates, or the
file is red. -/
def VerifiableInference.OnPublicFiles.closedAll_hasCode : Bool :=
  let z := VerifiableInference.OnPublicFiles.closeAll (fun _ => 0) 17 VerifiableInference.OnPublicFiles.emptyAll
  VerifiableInference.OnPublicFiles.gatedFileDecision (VerifiableInference.OnPublicFiles.liveAll (fun _ => 0) 17 z)
      (fun (_ : Unit) _ _ _ => true) () ⟨[], []⟩ ⟨[], []⟩ ⟨[], []⟩ &&
    VerifiableInference.OnPublicFiles.gatedLinkDecision true (fun (_ : Unit) _ => true) () ⟨[], []⟩

#print axioms VerifiableInference.OnPublicFiles.closeAll_fit
#print axioms VerifiableInference.OnPublicFiles.tVC_closed
#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsAtFullSize_closed
