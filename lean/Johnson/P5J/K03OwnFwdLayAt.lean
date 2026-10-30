-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OwnFwdLayAt.lean: THE KIND "LOOKUP" (K3): ACROSS AN ACCEPT OF THE LOOKUP ON THE
DIGITS OF A LAYERS' SEGMENT THE CALLING KIND's TWO RUNS "front" AND "back" GO FORWARD, AT THE
CLOSED CONSTANT, FROM THE HEAD AND THE FREE LETTERS' THREE EQUATIONS; AND SO THE FIELD rides AT THE
TWELVE LAYERS' DIGITS FROM THE SAME. Five theorems: one by the kernel, the others joinings of three
groups of theorems.
  `k03_dig_number`: the border in front of the digits' lookup of the layers' segment 2 g is number
    28 g + 8.
  `k03_states_lay`: at the head's own chain's link 2 g: what it states at sub-protocol number 2
    under "front" and "back" answers as the calling kind's own block's runs, at every state
    (`StatesAt`): by `IM.k4_of`, `IM.claims_alone` (Johnson/IMR/K4Seat.lean, SeatForm.lean) and
    `statesAt_guarded`, `k4C_front`, `k4C_back`, `hsame_reply`
    (Johnson/Road/K4/InT/SeatTie.lean, Riders/SeatsTies.lean).
  `k03_wins_at`: `wins_reached` (Johnson/Road/K4/InT/WinsReached.lean) at
    "reached" := the tower's (`AtMg.rch_is_reach`), at that border: a layers' link is open, what
    the calling kind's hearing returned is there, the ledger has its sizes, two of the three
    windows end at or below its next slot.
  `k03_fwd_lay`: THE PREMISE hOwn OF `k03_rides_dig_layers` (Johnson/P5J/K03RidesDigAt.lean), IN
    ITS OWN TEXT: by `hOwn_of_below`
    (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean), its premise hWin := `k03_wins_at`: THE
    FIRST COMPILED MEETING OF THE TWO.
  `k03_rides_dig_layers_paid`: the field, in the form in which the kind's condition asks it.
Limits: joinings. The head h and the free letters' three equations are premises; a member of the
head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). At
OnBytes.secondHashFunction. The full size alone. No soundness is claimed.

-/
import Johnson.P5J.K03RidesDigLeft
import Johnson.P5J.RchAtMg
import Johnson.Desc.Sound.MgAt.K3DigitsStaysBelow
import Johnson.Road.K4.InT.WinsReached
import Johnson.Road.K4.Riders.SeatsTies
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.K9 (statesOfLink holesAt)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Road.K4.InT (StatesAt statesAt_guarded)
open OnBytes.Road.K4.Riders (k4C_front k4C_back hsame_reply)
open Johnson.Desc.First.Walk.Tied (reach_raw)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- The number of the border in front of the digits' lookup of the layers' segment 2 g. -/
theorem k03_dig_number : ∀ g, g < 12 → k3K (2 * g) true = 28 * g + 8 := by decide

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **What the head's own chain's link 2 g states at number 2 under "front" and "back".** -/
theorem k03_states_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    (Lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
    (hLk : cF.links[2 * g]? = some Lk) :
    ∃ pK, ∀ name, name = "front" ∨ name = "back" → ∀ t, StatesAt (statesOfLink Lk) 2 pK name t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L1, b, x, e1, e2, -, ha, -⟩ := IM.k4_of h.scope h.reads O g hg
  obtain rfl : Lk = L1 := Option.some.inj (hLk.symm.trans e1)
  have hcl : b.claims = (OnBytes.Desc.First.K4.blockAtC { x.2 with k3Runs := true }).claims.map
      fun c => (c.1, fun n t => (c.2 n t).bind fun y =>
        (VerifiableInference.Desc.seatSame ProofFile.sameReply t y.2).map fun _ => y) := by
    have h0 := IM.claims_alone ha
    exact h0
  obtain ⟨rF, hF⟩ := k4C_front { x.2 with k3Runs := true }
  obtain ⟨rB, hB⟩ := k4C_back { x.2 with k3Runs := true }
  refine ⟨{ x.2 with k3Runs := true }, fun name hn t => ?_⟩
  rcases hn with rfl | rfl
  · exact statesAt_guarded e2 hcl hsame_reply (Or.inl rfl) hF t
  · exact statesAt_guarded e2 hcl hsame_reply (Or.inr rfl) hB t

/-- **What is reached in front of the digits' lookup of the layers' segment 2 g**:
`wins_reached` (Johnson/Road/K4/InT/WinsReached.lean), at "reached" := the tower's. -/
theorem k03_wins_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12)
    (z : ProofFile.InstPub) (u : VerifiableInference.Desc.First.S × (FrD).E.Str)
    (hr : h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2)) :
    ∃ (al : VerifiableInference.Desc.First.LayOwn) (o : OnBytes.Model.Layer.Own),
      u.1.here = .lay al ∧ al.own = some o ∧ OnBytes.PscRun.Sized al.F ∧
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ al.F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ al.F.next ∧
      u.1.lookHeard? = some o.H.fo := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' := reach_raw (h.toAtMg.rch_is_reach _ _ hr)
  rw [k03_dig_number g hg] at hr'
  exact OnBytes.Road.K4.InT.wins_reached h.scope h.reads O h.laid.planOk hg hr'

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **hOwn AT THE TWELVE LAYERS' DIGITS, AT THE CONSTANT.** -/
theorem k03_fwd_lay : ∀ g < 12,
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true) u →
      h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g)) p.1 p.2 u.1 v.1 := by
  intro g hg b' hb'
  have hl : 2 * g < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  obtain ⟨pK, hSt⟩ := k03_states_lay h hg Lk hLk
  have hne : ¬ ((2 * g == 24) = true) := by
    rw [beq_iff_eq]
    omega
  have hsil : ∀ (b : ℕ) (n : String) (s : VerifiableInference.Desc.First.S),
      (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g) Lk).silent b n s = none := by
    intro b n s
    unfold holesAt
    rw [h24]
    dsimp only
    rw [if_neg hne]
  exact hOwn_of_below (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch
    (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g) Lk) Lk K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' pK hb'
    (Pc.planOk (2 * g) hl true b' hb') rfl (k03_pieceAt_dig h.toAtMg (2 * g))
    (by
      show (if (true : Bool) = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) + 1 = 7
      rw [if_pos rfl, if_neg (by omega)])
    rfl hl hsub (k03_hlink h (2 * g) Lk hLk)
    (fun z u _ hr _ => k03_wins_at h hg z u hr)
    (fun _ u _ _ _ _ _ _ p _ => hsil p.1 p.2 u.1) hSt

/-- **THE FIELD rides AT THE TWELVE LAYERS' DIGITS, FROM THE HEAD ALONE.** -/
theorem k03_rides_dig_layers_paid : ∀ g < 12,
    ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b' →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K (2 * g) true) q b' := by
  intro g hg q hq b' hb'
  exact k03_rides_dig_lay_own h 𝔏 q₁ q₂ q₃ g hg q hq b' hb' (k03_fwd_lay h 𝔏 q₁ q₂ q₃ g hg b' hb')

end

end P5J

#print axioms P5J.k03_dig_number
#print axioms P5J.k03_states_lay
#print axioms P5J.k03_wins_at
#print axioms P5J.k03_fwd_lay
#print axioms P5J.k03_rides_dig_layers_paid
