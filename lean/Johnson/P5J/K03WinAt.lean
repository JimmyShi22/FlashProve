-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03WinAt.lean: THE LOOKUP ARGUMENTS ON THE DIGITS: THE PREMISE hWin OF THE LOOKUPS'
AUTHORS' `ridesAtR_digits_att` AND `ridesAtR_digits_head`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean [not imported here]): "IN FRONT OF THE DIGITS' LOOKUP
THE WINDOW OF THE CALLS' LOOKUP's SUMCHECK OVER THE LEAVES IS FREE IN THE LEDGER AND ENDS AT OR
BELOW ITS NEXT SLOT", IN ITS OWN TEXT, AT THE CLOSED CONSTANT, AT EVERY SEGMENT l < 25, UNDER THE
HEAD `AtMgA` ALONE: OFF THE TABLE's PROMISE IN FRONT: no fact on reached states is spent.
  `k03_win_front`: the sentence, from the promise in front and "no mark".
  **`k03_hWin`**: in the binder's own hands.
WHOSE. All of it is the lookups' authors': the law `hwin_of_onOut`
(Johnson/Top/H/Keep/CallersStay.lean) · the closed fact `planesFront_mgMore`
(Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean: by the kernel, at all 25: the calls' item lookOut is
open or tied in front of the digits' place, and leftOn is among the public items there) · AND THE
TWO LIFTS OFF THE PROMISE (the test `k3OnOut` off `K3At.lookOut`; the sentence `k3LeftOnItem` off
`K3At.pLeftOn`): THESE STAND INSIDE THE PROOF OF THEIR `hPlanesIt_dig` (the same file), AND STAND
AS `callsItems_front_dig` (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean). OUR PROOF FOLLOWS
THE LINES INSIDE `hPlanesIt_dig`; IT DOES NOT CALL THAT LEMMA.

Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03OthersPubAt
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesIt
import Johnson.Desc.Sound.MgAt.K3RidesDigStep
import Johnson.Top.H.Keep.CallersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Pub pubSets)
open VerifiableInference.Desc.First.Look (placeAt k3OnOutAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **The window, from the promise in front.** -/
theorem k03_win_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {b' : VerifiableInference.Desc.Block S ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (z : ProofFile.InstPub) (u : S × (FrD).E.Str)
    (hu : onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l true) u) (hun : u.1.failed = none) :
    ∀ F, u.1.fork? = some F → ∀ g₀,
      (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm).heard u.1 = some g₀ →
        g₀.leaves.first + lvLen g₀ ≤ F.next ∧ g₀.leaves.first + lvLen g₀ ≤ F.ns ∧
        ∀ j, g₀.leaves.first ≤ j → j < g₀.leaves.first + lvLen g₀ →
          ¬ OnBytes.PscRun.Filled F j := by
  have eM : (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more = mgMore :=
    mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl
  have hfront := onQ_front hu hun
  rw [eM] at hfront
  have hQ : ∀ p ∈ (pubSets (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS)[k3K l true]?.getD [],
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pubP p (z, u.1) := by
    obtain ⟨-, hm | ⟨-, -, -, h4⟩⟩ := hu
    · exact absurd hun hm
    · exact h4
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l true b' hb
  obtain ⟨sub, -, a2, hpcT⟩ := K3Lot.k03_sub_full l hl
  have hFr := List.all_eq_true.1 planesFront_mgMore l (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m1 : Pub.lookOut l (IM.k3Place l false).piece ∈ frontDig mgMore l := by
    simpa using hFr.1
  have m2 : Pub.leftOn l ∈ (pubSets mgMore linksFull PS)[k3K l true]?.getD [] := by
    simpa using hFr.2
  have ePc : (IM.k3Place l false).piece =
      VerifiableInference.Desc.K3.pieceAt (At.X Zp) l false := by
    have a1 := pieceAt_calls (At.X Zp) l
    omega
  have hLfAt : k3LeftOnItemAt (At.X Zp) l u.1 := by
    have h0 := hQ _ (by rw [eM]; exact m2)
    rw [(k3At_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pLeftOn] at h0
    exact h0
  obtain ⟨pc, hpcAt, hLf⟩ := hLfAt
  have hO : VerifiableInference.Desc.K3.k3OnOut pc u.1 = true := by
    have h0 := hfront _ m1
    rw [ePc, (k3At_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).lookOut] at h0
    unfold k3OnOutAt at h0
    rw [hpcAt] at h0
    exact h0
  have hdc : pc.digits = false := by
    unfold placeAt at hpcAt
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hpcAt
    rfl
  intro F hF g₀ hg
  exact hwin_of_onOut hdc hF hO hLf g₀ hg

/-- **hWin AT THE CONSTANT, AT EVERY SEGMENT.** -/
theorem k03_hWin (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {b' : VerifiableInference.Desc.Block S ProofFile.Cl}
    (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b') :
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F → ∀ g₀,
        (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm).heard u.1 = some g₀ →
        g₀.leaves.first + lvLen g₀ ≤ F.next ∧ g₀.leaves.first + lvLen g₀ ≤ F.ns ∧
        ∀ j, g₀.leaves.first ≤ j → j < g₀.leaves.first + lvLen g₀ →
          ¬ OnBytes.PscRun.Filled F j :=
  fun z u _ hu _ hm _ _ => k03_win_front h hl hb z u hu (Classical.not_not.1 hm)

end P5J

#print axioms P5J.k03_win_front
#print axioms P5J.k03_hWin
