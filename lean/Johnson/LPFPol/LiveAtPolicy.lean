-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/LiveAtPolicy.lean: THE TEST `protocolDataWellFormed` (Johnson/Goal/Description/Live.lean) GIVES ONE
VERDICT AT TWO SETS OF PUBLIC FILES IN THE GOALS' SCOPE THAT PART IN THE THREE LINES C, theta, cap
OF THE PARAMETER FILE ALONE. Statements and proofs.
  `at_ v lay KL`: the three public files with the parameter file written at the free numbers v.
  `depths_of_live`: in scope, where the key file's and the proof file's seats return and `dataWellFormedAtFullSizeDepth`
      accepts a plan's record G with their data, the two depths in G add up to at most 332598.
  `live_up`: in scope at both: a yes at v gives a yes at v with other numbers C, theta, cap.
  **`theLive_policy_free`**: one verdict at both.
  `live_at_stored_scales`: so a yes at the stored full-size example's files gives a yes at every
      policy in scope at that example's layout file, scale file and five other free numbers.
How. In scope `protocolDataWellFormed` accepts wherever its three makers return and two depths are small
(`theLive_of_returns`, Johnson/Goal/Skeleton/LiveOfReturns.lean). Each maker returns at the second
files where it returns at the first: the public record (Johnson/LPFPol/PublicInScope.lean), the
plan's seat (PlanSeat.lean), the key file's seat (KeySeat.lean), the proof file's seat
(LaidAtPolicy.lean, under `HeadSame` of Lots.lean, which HeadInScope.lean pays in scope).
What is not claimed. THAT `protocolDataWellFormed` ACCEPTS ANYWHERE: at the stored files (the term `VerifierAndGoals.storedPublicFiles`)
another file proves it: `theLive_zFull` (AtFullSide/Top/LiveAtFull.lean), with that file's limits.
WHICH POLICIES ARE IN SCOPE: here, that the second set is in scope is a premise; the range is
`inScope_iff_range` (ScopeAtPolicy.lean), and LiveCorollaries.lean lays it in. A yes of `protocolDataWellFormed` is
no sign that the verifier accepts anything. The two descriptions are not shown to be one: the output
head's own block holds the policy. Nothing where the scale file or one of the five other free
numbers parts too. At the format's second hash function by name, not at a letter. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.LPFPol.LaidAtPolicy
import Johnson.LPFPol.PublicInScope
import Johnson.LPFPol.HeadInScope
import Johnson.LPFPol.KeySeat
import Johnson.LPFPol.PlanSeat
import Johnson.Goal.Skeleton.LiveOfReturns
import Johnson.Goal.Numbers.PublicAtMeaning
import Johnson.Goal.Files.ScopeExample

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 3000

namespace LPFPol
open VerifierAndGoals FlashProve
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.PlanWritten (publicOfO)
open Johnson.G (writtenKFull writtenPFull cntFrameFull_written)

/-- The three public files with the parameter file written at the free numbers v. -/
def at_ (v : FreeLines) (lay KL : ByteArray) : PublicFiles := ⟨policyFile v, lay, KL⟩

/-- The stored full-size example's files are of the form. -/
theorem zFull_form : storedPublicFiles = at_ storedLines storedPublicFiles.lay storedPublicFiles.KL := by
  unfold at_
  rw [← pol_zFull]

/-- The three numbers laid back. -/
theorem back_lines (v : FreeLines) (C theta cap : Nat) :
    ({ ({ v with C := C, theta := theta, cap := cap } : FreeLines) with
      C := v.C, theta := v.theta, cap := v.cap } : FreeLines) = v := rfl

attribute [local irreducible] VerifierAndGoals.policyFile

/-- In scope, where the two seats return and `dataWellFormedAtFullSizeDepth` accepts G with their data, G's two depths are
small. -/
theorem depths_of_live {Z : PublicFiles} (hZ : InScope Z = true)
    {G : OnBytes.Flat.FilesParameters LPFD.Full.XF OnBytes.Flat.RecFull}
    {K : OnBytes.Maker.WholeD × (OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
        _root_.Run.PQ.View → Bool)}
    {P : OnBytes.Maker.WholeD ×
      (LPFD.Full.XF × OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
          _root_.Run.PQ.View → Bool)}
    (hK : keyDataAndDecisionOrRefusalAt OnBytes.secondHashFunction (asDescriptionFiles Z) = .ok K)
    (hP : proofDataAndDecisionOrRefusalAt OnBytes.secondHashFunction (asDescriptionFiles Z) = .ok P) (hl : dataWellFormedAtFullSizeDepth G K.1 P.1 = true) :
    G.c.first.binding.logLeaves + G.k.oneTime.binding.logLeaves ≤ 332598 := by
  have eK : K.1 = writtenKFull :=
    VerifiableInference.PlanWritten.laid_data_written (o := OnBytes.secondHashFunction) (r := K.2) hZ hK
  have eP : P.1 = writtenPFull := LPFD.Full.laidPOf_written (o := OnBytes.secondHashFunction) (r := P.2) hZ hP
  simp only [dataWellFormedAtFullSizeDepth, dataWellFormedApartFromDepth, Bool.and_eq_true] at hl
  have hc := (frameFitFullD_parts (show sizeNumbersFitAtFullSize _ _ _ _ _ _ _ _ = true from hl.2.1)).hcnt
  rw [eK, eP, cntFrameFullD_landed, cntFrameFull_written] at hc
  unfold theQueries at hc
  omega

/-- A set in scope is read. -/
theorem read_of_scope {Z : PublicFiles} (hZ : InScope Z = true) : ∃ pp, readFiles Z = .ok pp := by
  cases hR : readFiles Z with
  | ok pp => exact ⟨pp, rfl⟩
  | error e =>
    unfold InScope at hZ
    rw [hR] at hZ
    simp at hZ

/-- **A yes at v gives a yes at v with other numbers C, theta, cap**, both sets in scope. -/
theorem live_up (v : FreeLines) (C theta cap : Nat) (lay KL : ByteArray)
    (h0 : InScope (at_ v lay KL) = true)
    (h1 : InScope (at_ { v with C := C, theta := theta, cap := cap } lay KL) = true)
    (hl : protocolDataWellFormed (asDescriptionFiles (at_ v lay KL)) = true) :
    protocolDataWellFormed (asDescriptionFiles (at_ { v with C := C, theta := theta, cap := cap } lay KL)) = true := by
  obtain ⟨K, P, hG, hK, hP, hlive⟩ := theLiveAt_made OnBytes.secondHashFunction _ hl
  obtain ⟨X, hX, hKX⟩ := ProofFile.Law.exBind_ok
    (show (publicOfO OnBytes.secondHashFunction (policyFile v) KL (some lay)).bind
      (fun X => VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest X lay) = .ok K from hK)
  have hX' : publicOfO OnBytes.secondHashFunction (policyFile { v with C := C, theta := theta, cap := cap }) KL
      (some lay) =
      .ok (X.withPol C theta cap) := publicOfO_returns_inScope hX h1
  have hs := VerifiableInference.PlanWritten.ScopeCore.scan_of_publicO hX
  have hs' : polScan (policyFile { v with C := C, theta := theta, cap := cap }) =
      .ok (X.P.withPol C theta cap) :=
    VerifiableInference.PlanWritten.ScopeCore.scan_of_publicO hX'
  obtain ⟨pp, hR⟩ := read_of_scope h0
  obtain ⟨pp', hR'⟩ := read_of_scope h1
  have hH : HeadSame X C theta cap := headSame_read hX hR hR'
  obtain ⟨P', hP', -⟩ := laidPOf_wp hX hX' hs hs' hH
    (show LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction (policyFile v) lay KL = .ok P from hP)
  obtain ⟨G', hG', d1, d2⟩ := planLaid_wp hX hX'
    (show filesParametersOrRefusalAt OnBytes.secondHashFunction ⟨policyFile v, lay, KL⟩ = .ok _ from hG)
  have hd := depths_of_live h0 hK hP hlive
  refine theLive_of_returns _ h1 (G := G') (K := K) (P := P') hG' ?_ hP' (by rw [d1, d2]; exact hd)
  show (publicOfO OnBytes.secondHashFunction (policyFile { v with C := C, theta := theta, cap := cap }) KL
      (some lay)).bind
    (fun X => VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest X lay) = .ok K
  rw [hX']
  show VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest (X.withPol C theta cap) lay = .ok K
  rw [laidFixed_withPol]
  exact hKX

/-- **ONE VERDICT AT BOTH.** Two sets of public files in the goals' scope that part in the three
lines C, theta, cap of the parameter file alone. -/
theorem theLive_policy_free (v : FreeLines) (C theta cap : Nat) (lay KL : ByteArray)
    (h0 : InScope (at_ v lay KL) = true)
    (h1 : InScope (at_ { v with C := C, theta := theta, cap := cap } lay KL) = true) :
    protocolDataWellFormed (asDescriptionFiles (at_ { v with C := C, theta := theta, cap := cap } lay KL)) =
      protocolDataWellFormed (asDescriptionFiles (at_ v lay KL)) := by
  cases a : protocolDataWellFormed (asDescriptionFiles (at_ v lay KL)) with
  | true => exact live_up v C theta cap lay KL h0 h1 a
  | false =>
    cases b : protocolDataWellFormed (asDescriptionFiles (at_ { v with C := C, theta := theta, cap := cap } lay KL)) with
    | false => rfl
    | true =>
      have c := live_up { v with C := C, theta := theta, cap := cap } v.C v.theta v.cap lay KL h1
        (by rw [back_lines]; exact h0) b
      rw [back_lines, a] at c
      cases c

/-- **A yes at the stored files gives a yes at every policy in scope at the stored scales.** -/
theorem live_at_stored_scales (live : protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true) (C theta cap : Nat)
    (hs : InScope (at_ { storedLines with C := C, theta := theta, cap := cap } storedPublicFiles.lay storedPublicFiles.KL) =
        true) :
    protocolDataWellFormed (asDescriptionFiles (at_ { storedLines with C := C, theta := theta, cap := cap } storedPublicFiles.lay
                                  storedPublicFiles.KL)) = true := by
  have h0 : InScope (at_ storedLines storedPublicFiles.lay storedPublicFiles.KL) = true := by
    rw [← zFull_form]
    exact inScope_full
  have l0 : protocolDataWellFormed (asDescriptionFiles (at_ storedLines storedPublicFiles.lay storedPublicFiles.KL)) = true := by
    rw [← zFull_form]
    exact live
  exact live_up storedLines C theta cap storedPublicFiles.lay storedPublicFiles.KL h0 hs l0

end LPFPol

#print axioms LPFPol.live_up
#print axioms LPFPol.theLive_policy_free
#print axioms LPFPol.live_at_stored_scales
