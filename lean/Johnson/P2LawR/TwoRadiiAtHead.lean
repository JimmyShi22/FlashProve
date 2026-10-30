-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/TwoRadiiAtHead.lean: THE TWO TESTS "THE RADIUS FITS" THAT STAY OF THE LAST TABLE's
FIELD planAt, AT W's MEMBER AND AT THE INDEX MASKS' MEMBER, SAY TRUE UNDER THE HEAD ALONE (the head
at the name is itself made with the condition rowsRead Z: this file removes radWB, not rowsRead). A
JOIN OF THREE OTHER FILES' THEOREMS, AND TWO CLOSED FACTS BY LEAN's KERNEL ON A WRITTEN LIST (the
test, which is spent, and its negative test). THE THREE. rad_in_scope
(Johnson/HB/LLHARD/RadiiInScope.lean): in the goals' scope, where the public part returns, the pin
on what was made accepts AND THE ROWS' MAKER RETURNS R: the law's own reader of a radius at R is the
written list's. rad_at_laid over it (Johnson/Desc/First/Close/Law/AlikeInScope.lean, kind
K10): so the composed meaning's radii At.rad Zp Z.lay are radW. BOTH KEEP ONE NAMED CONDITION: that
return: "asked by no test of the verifier, given by no theorem" (the two heads' words; row 14 of the
proof file's entry tests, rowsMadeB, asks it now: Johnson/Desc/Laid/ProofAsks.lean). rows_at_head
(Johnson/IMR/RadAtHead.lean): under the head the rows' maker returns (off the head's own field
plan.radii: at no rows that test is false).
  radAtF ρ t radAtB's text (Johnson/IMR/RadAtHead.lean), with a function ρ in the place of the radii
      of a list of rows.
  **rad_written**   at radW both tests accept: at (82, 0) and at (1, 0). By the kernel.
  rad_control   A NEGATIVE TEST: with every radius one less both reject.
  **AtMg.rad_is_written**   under the head At.rad Zp Z.lay = radW: two calls.
  radB_at_seatF one seat's share: radB_at_seat's proof (the same file), with that
      equation in the place of its premise on the closed term rowsW.
  **AtMg.two_radii** radB_at_head's statement (the same file), to the token, WITHOUT ITS
      PREMISE radWB = true: and so the premises hRW | hRI of P5J.AtMg.planAt_two_radii
      (Johnson/P2LawR/PlanAtTwoRadii.lean).
Limits. At the second hash function alone (the three files' theorems stand there). NO MEMBER: that
a head can be had is not said. It leans on the door's issue 2 (its pin on what was made is spent).
(Where this and lean/THEOREM.md differ, the page holds.) The full size alone.
Nothing on what a radius means: numbers are compared. That the written list is what the maker
computes is rad_in_scope's matter, not evaluated here. Raised limits: maxRecDepth
1000000 and maxHeartbeats 4000000 at the two closed facts. Nothing on soundness.

-/
import Johnson.IMR.RadAtHead
import Johnson.Desc.First.Close.Law.AlikeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open H2K.Member (piWFull rWFull)
open P2Law.PlanLeft (radB)
open ToldDesc (p14At)
open IM (zW pins p14_codes)
open IM.Seats
open VerifiableInference.Desc.First.Close (radW rad_at_laid)

/-- At every written entry that sits at t: the radius test, at the radii ρ. -/
def radAtF (ρ : ℕ → ℕ → ℕ) (t : ℕ × ℕ) : Bool :=
  match piWFull.nums.stages with
  | st :: _ =>
    (List.range Johnson.G.proofSendsFull.1.sends.length).all fun k =>
      (P5T.mineAt P5T.psFull k).zipIdx.all fun x =>
        !decide (x.1.seat = t) || radE zW.codes rWFull st (x.1.shape, ρ k x.2)
  | [] => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- **At the written radii both tests accept.** -/
theorem rad_written : radAtF radW (82, 0) = true ∧ radAtF radW (1, 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- A NEGATIVE TEST: with every radius one less both reject. -/
theorem rad_control :
    radAtF (fun k i => radW k i - 1) (82, 0) = false ∧
      radAtF (fun k i => radW k i - 1) (1, 0) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **UNDER THE HEAD THE MEMBERS' RADII ARE THE WRITTEN ONES.** -/
theorem AtMg.rad_is_written (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    At.rad Zp Z.lay = radW := by
  obtain ⟨R, hR, -⟩ := rows_at_head h
  exact rad_at_laid h.scope h.laid hR

/-- One seat's share. -/
theorem radB_at_seatF (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {t : ℕ × ℕ}
    (T : radAtF radW t = true) {st : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (hst : piWFull.nums.stages = st :: rest) :
    (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = t)).all
      fun y => radB (p14At Zp).codes rWFull st y) = true := by
  refine List.all_eq_true.2 fun y hy => ?_
  obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
  obtain ⟨k, hk, x, hx, e, es⟩ := member_entry _ _ _ y hy1
  rw [h.seats] at hx
  rw [(pins h.pins.1).2.2.2.2] at hk
  unfold radAtF at T
  rw [hst] at T
  have a := List.all_eq_true.1 (List.all_eq_true.1 T k hk) x hx
  have hs : x.1.seat = t := es.symm.trans (of_decide_eq_true hy2)
  rw [decide_eq_true hs, Bool.not_true, Bool.false_or] at a
  rw [radB_is, e, p14_codes h.pins.1, h.rad_is_written]
  exact a

/-- **THE TWO RADIUS TESTS THAT STAY OF planAt, FROM THE HEAD ALONE.** -/
theorem AtMg.two_radii (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = (At.N Zp cF).w)).all
        fun y => radB (p14At Zp).codes rWFull st y) = true ∧
      (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = (At.N Zp cF).index)).all
        fun y => radB (p14At Zp).codes rWFull st y) = true := by
  intro st rest hst
  have hs : piWFull.nums.stages = st :: rest := by
    rw [← hst, stages_at_head h]
  rw [h.N_six.2.2.2.1.trans (congrArg Prod.snd P5T.N0Full_seats),
    h.N_six.2.2.1.trans (congrArg Prod.fst P5T.N0Full_seats)]
  exact ⟨radB_at_seatF h rad_written.1 hs, radB_at_seatF h rad_written.2 hs⟩

end P5J

#print axioms P5J.rad_written
#print axioms P5J.rad_control
#print axioms P5J.AtMg.rad_is_written
#print axioms P5J.radB_at_seatF
#print axioms P5J.AtMg.two_radii
#print axioms VerifiableInference.Desc.First.Close.rad_at_laid
#print axioms VerifiableInference.Desc.LinkJoin.rad_in_scope
#print axioms IM.Seats.rows_at_head
