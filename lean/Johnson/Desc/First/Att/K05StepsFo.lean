-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05StepsFo.lean: kind K5: THE KIND's HEARING BLOCK's DECISION STEPS: where it says yes, what the lookup on the calls was heard to return stands as it was, and the segment's ledger
is a later one with its sizes: Block.Steps (CarriesFo S.fork? S.lookHeard?) (Johnson/Desc/First/LedgerAtFo.lean), of the block k5AtN (Johnson/Desc/First/Att/SeatN.lean).

Main names:
  later_of_hear_sized: behind the kind's hearing from a ledger WITH ITS SIZES the ledger is later (Fo.Later) and has its sizes. NO PREMISE ON ROOM: a hearing that returns has found its slots. "keep" is the hearing's
    law's Stays (hear_said, Att/K5SaidAll.lean); "next" and "ns" are hear_below's (Att/K05HearBelow.lean).
  k5_decide_stepsFo: the decision at the seat seatSO. k5AtN_stepsFo: **the block.**
IS IT EMPTY HERE? Where the decision refuses nothing is said. The premise planOk = true is not spent.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Att.K5Shape
import Johnson.Desc.First.Att.K5SaidAll
import Johnson.Desc.First.Att.K05HearBelow
import Johnson.Desc.First.Att.K05LeavesTl
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (Block CarriesFo)

/-- **Behind the kind's hearing from a sized ledger the ledger is later, and has its sizes.** -/
theorem later_of_hear_sized {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ} {h : Heard}
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F) : Fo.Later F G ∧ OnBytes.PscRun.Sized G := by
  obtain ⟨_, _, _, _, _, zG, st⟩ := hear_said hh hz
  obtain ⟨_, bl⟩ := hear_below hh hz
  refine ⟨⟨bl.1, bl.ns, fun j hj => ?_⟩, zG.vp, zG.mf, zG.got⟩
  obtain ⟨a, b, d⟩ := st j _ _ ⟨hj, rfl, rfl⟩
  exact ⟨a, b, d⟩

/-- The decision at the seat. -/
theorem k5_decide_stepsFo (p : Par) {s s' : First.S} {rs : List Fmt.RoundView} (hd : decide seatSO p s rs = .ok s') :
    CarriesFo First.S.fork? First.S.lookHeard? s s' := by
  obtain ⟨_, F, h, G, l1, hh, l2⟩ := (decide_lays seatSO p _ _ _).1 hd
  obtain ⟨a, he, rfl⟩ := seatSO_lay l2
  have eF : a.F = F := by
    have : (match s.here with | .att a => some a.F | _ => none) = some F := l1
    rw [he] at this
    exact Option.some.inj this
  refine ⟨fun g hg => ?_, fun F' hF' sF' => ?_⟩
  · unfold First.S.lookHeard? at hg ⊢
    rw [he] at hg
    exact hg
  · have e : F' = F := by
      unfold First.S.fork? at hF'
      rw [he] at hF'
      exact (Option.some.inj hF').symm.trans eF
    subst e
    obtain ⟨lt, sG⟩ := later_of_hear_sized hh ⟨sF'.1, sF'.2.1, sF'.2.2⟩
    exact ⟨G, rfl, lt, sG⟩

/-- **THE KIND's HEARING BLOCK's DECISION STEPS.** -/
theorem k5AtN_stepsFo {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)}
    {b : Block First.S VerifiableInference.Desc.Claim} (hb : k5AtN W l g before = some b) :
    b.planOk = true → b.Steps (CarriesFo First.S.fork? First.S.lookHeard?) := by
  intro _
  unfold k5AtN at hb
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun s rs _ s' h => k5_decide_stepsFo _ h

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.later_of_hear_sized
#print axioms VerifiableInference.Desc.First.Att.P.k5_decide_stepsFo
#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_stepsFo
