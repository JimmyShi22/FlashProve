-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/SamplesPublic.lean: The public half of hFirst of samples_at_lastThread
(AtFullSide/K1/SamplesAtEnd.lean), under the library's head, at V := LLT25.vAt Zp h.𝔇.N: the two
members' shapes among the members of the sample's list, and the list of seats.

  sits_written       the kernel: at messages 4 and 197 the seat and the shape agree with the plan
  sits_shape_of      a law: from seatIsB, every member at the seat has the shape
  sits_index_shape, sits_w_shape   the statements hShI, hShW
  seats_nodup        no seat stands twice
  laid_places_seats  the listed seats are the plan's seats

Limits. Public data alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatSeats
import Johnson.Second.Seam.PlanSitsInScope
import Johnson.P5J.PlanSitsCore
import Johnson.LLT25R.LastV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (Mem SitsAt seatOf)
open OnBytes.Maker (WholeD)
open P5T (psFull)

set_option maxRecDepth 1000000 in
/-- **The kernel.** -/
theorem sits_written :
    ((K13.Law.LFull.places[4]?).any fun q => (K13.Law.MFull[4]?).any (seatIsB q)) = true ∧
    ((K13.Law.LFull.places[197]?).any fun q => (K13.Law.MFull[197]?).any (seatIsB q)) = true ∧
    K13.Law.seatsFull.Nodup ∧ K13.Law.LFull.places = K13.Law.seatsFull := by
  decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **Every member at a seat that the test names has the shape.** -/
theorem sits_shape_of {q : ℕ × ℕ} {sh : OracleShape} (hs : seatIsB q sh = true) :
    ∀ μ ∈ P5J.At.ms Zp Z.lay, SitsAt μ q.1 q.2 → (μ.1.l.get μ.2).1 = sh := by
  have eP := (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).1
  have hM : ∀ y : OnBytes.OracleShape × (Nat × Nat),
      y ∈ (P5J.At.ms Zp Z.lay).map (fun m => ((m.1.l.get m.2).1, seatOf m)) ↔
        y ∈ (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
    intro y
    have e := P5T.memsSame_atR Zp (P5J.At.rad Zp Z.lay) y
    rw [eP] at e
    exact e
  unfold seatIsB at hs
  rw [Bool.and_eq_true, List.all_eq_true] at hs
  intro μ hμ hsit
  obtain ⟨p', hp', e'⟩ := List.mem_map.1
    ((hM ((μ.1.l.get μ.2).1, seatOf μ)).1 (List.mem_map.2 ⟨μ, hμ, rfl⟩))
  have e1 : p'.shape = (μ.1.l.get μ.2).1 := congrArg Prod.fst e'
  have e3 : p'.seat = seatOf μ := congrArg Prod.snd e'
  have hq : seatOf μ = q := hsit
  have hw := hs.2 p' hp'
  rw [Bool.or_eq_true] at hw
  rcases hw with hw | hw
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hw
    exact absurd (e3.trans hq) hw
  · rw [← e1]
    exact of_decide_eq_true hw

/-- The plan's two members. -/
theorem plan_sits : ToldDesc.PlanSits K13.Law.LFull K13.Law.MFull (LLT25.vAt Zp h.𝔇.N) 4 197 := by
  have P := Second.Seam.planSits_at_N h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h) cF
  rw [h.toAtMg.msgs_at_head] at P
  exact P

/-- **hShI.** -/
theorem sits_index_shape :
    ∀ μ ∈ P5J.At.ms Zp Z.lay, SitsAt μ (LLT25.vAt Zp h.𝔇.N).index.1 (LLT25.vAt Zp h.𝔇.N).index.2 →
      (μ.1.l.get μ.2).1 = (LLT25.vAt Zp h.𝔇.N).indexShape := by
  have P := plan_sits h
  have e := sits_written.1
  rw [P.seatI, P.shapeI] at e
  exact sits_shape_of h e

/-- **hShW.** -/
theorem sits_w_shape :
    ∀ μ ∈ P5J.At.ms Zp Z.lay, SitsAt μ (LLT25.vAt Zp h.𝔇.N).w.1 (LLT25.vAt Zp h.𝔇.N).w.2 →
      (μ.1.l.get μ.2).1 = (LLT25.vAt Zp h.𝔇.N).wShape := by
  have P := plan_sits h
  have e := sits_written.2.1
  rw [P.seatW, P.shapeW] at e
  exact sits_shape_of h e

/-- **No seat stands twice.** -/
theorem seats_nodup : (P5J.At.seats Zp).Nodup := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [(K1.atAll_letters h O (K1.pin1_atAll h)).2.1]
  exact sits_written.2.2.1

/-- **The listed seats are the plan's.** -/
theorem laid_places_seats : K13.Law.LFull.places = P5J.At.seats Zp := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [(K1.atAll_letters h O (K1.pin1_atAll h)).2.1]
  exact sits_written.2.2.2

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.sits_written
#print axioms ProofFile.Honest.K1.sits_shape_of
#print axioms ProofFile.Honest.K1.plan_sits
#print axioms ProofFile.Honest.K1.sits_index_shape
#print axioms ProofFile.Honest.K1.sits_w_shape
#print axioms ProofFile.Honest.K1.seats_nodup
#print axioms ProofFile.Honest.K1.laid_places_seats
