-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Order.lean: A YES OF THE PROXIMITY TEST's DECISION LEAVES THE STATEMENT IN ORDER (Means.InOrder, Johnson/Desc/Means/Order.lean: every group in order; every open row within its group's tables; every sample row on its own message), WHERE THE CODES' LENGTHS ARE IN ORDER. Statements with proofs.
OBJECT. (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide; and the key file's ranges' test's block. USER. Johnson/RunOne/Law/K12Free15.lean's premise hord; whoever wants InOrder behind one of the four proximity tests of the key file.
LETTERS. p t0 tE rs gs | one N s s': free. Premises: the yes · the codes' lengths are in order (Codes.lengthsOk: a test with code on public data) · the statement in front is in order.
NOT THIS FILE's MATHEMATICS: the kind's files show that a yes of the test is A RUN OF THE GROUND's PLAIN CALLS (k12_calls, Johnson/Desc/K12/Law/Calls.lean: no premise), that the rows which a sending makes lie on their message (rowsFor_on | sampleFit_of, RowsForOn.lean), and from the two that such a run keeps Means.Tidy (calls_tidy, CallsWalkG.lean). Tidy is InOrder WITH THREE MORE INVARIANTS, which the key file's tables do not promise at border 15: so calls_tidy cannot be called there. Here the same induction is made for InOrder ALONE, step by step by the twelve laws of Johnson/Desc/Means/Page.lean.

  call_order: one step of the ground keeps InOrder. calls_order: a run does.
  k12_inOrder: the test. ranges_inOrder: the key file's block (through its two doors).
Limits. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.Law.CallsWalkG
import Johnson.Desc.Means.Page
import Johnson.RunOne.Law.RngAtKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Order
open OnBytes OnBytes.Params OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.Out (DS Call Calls dT call_codes k12_calls rowsFor_on sampleFit_of)

variable {ft : Nat}

/-- One step of the ground keeps the statement in order. -/
theorem call_order (d d' : DS) (hl : d.st.codes.lengthsOk = true) (h : Call ft d d') (hI : InOrder d.st) : InOrder d'.st := by
  cases h with
  | newGroup h => exact newGroupP_keeps h hI
  | recv h => exact recvP_keeps h hI
  | admit hs hfit hlong hr h =>
    refine admitP_keeps h hI ?_
    have h' := h
    unfold admitP at h'
    split at h'
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
      obtain ⟨x, hx, pl, hpl, _⟩ := h'
      rw [hx] at hs
      obtain rfl := Option.some.inj hs
      have hpl' : Send.pad d.st.codes x.shape = some pl := hpl
      exact rowsFor_on d.st _ x hx _ (sampleFit_of d.st x _ pl hl hfit hlong hpl') _ _ _ _ _
        (fun r hr' => by simp at hr') hr
    · cases h'
  | join h => exact joinP_keeps h hI
  | addRow h => exact (addRowP_keeps h hI).1
  | closeLedger h => exact closeLedgerP_keeps h hI
  | spend h => exact spendAsMaskP_keeps h hI
  | begin h => exact beginRunP_keeps h hI
  | count t => exact hI
  | cols l => exact hI

/-- A run of the ground's calls keeps the statement in order. -/
theorem calls_order {d d' : DS} (h : Calls ft d d') (hl : d.st.codes.lengthsOk = true) (hI : InOrder d.st) : InOrder d'.st := by
  induction h with
  | nil d => exact hI
  | cons s _ ih => exact ih (by rw [call_codes _ _ s]; exact hl) (call_order _ _ hl s hI)

/-- **A yes of the proximity test's decision leaves the statement in order.** -/
theorem k12_inOrder (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t0 rs gs = .ok tE) (hl : t0.st.codes.lengthsOk = true) (hI : InOrder t0.st) : InOrder tE.st :=
  calls_order (k12_calls p t0 tE rs gs h [] []) hl hI

open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)
open Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngAnyCl Johnson.RunOne.Law.RngAtKeyD

/-- **The key file's ranges' test leaves the statement in order.** No premise on the plan. -/
theorem ranges_inOrder (one : OneTime) (N : H2U.PlaceNums) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s')
    (hl : s.d.st.codes.lengthsOk = true) (hI : InOrder s.d.st) : InOrder s'.d.st := by
  obtain ⟨tE, _, _, _, hd, _, e⟩ := keyD_yes h
  have hd' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (recD s) rs gs = .ok tE := by
    rw [(same_k12 (A := Unit) (B := Claim) guardedProximityTestParts (rangesParams N)).decide]
    exact hd
  have e' : s'.d.st = tE.st := by rw [e]
  rw [e']
  exact k12_inOrder _ _ _ _ _ hd' hl hI

end Johnson.RunOne.Law.K12Order

#print axioms Johnson.RunOne.Law.K12Order.calls_order
#print axioms Johnson.RunOne.Law.K12Order.k12_inOrder
#print axioms Johnson.RunOne.Law.K12Order.ranges_inOrder
