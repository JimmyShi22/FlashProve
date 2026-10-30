-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38E/MemAtHead.lean: the third clause of the closed side of `DigAheadOk`
(Johnson/Desc/First/Look/K3DigitsAhead.lean) under the one head: at every member of the digits' list
of a segment, the first member of the table's list at that member's seat has its shape (`MemAt`,
Johnson/Desc/First/Att/K05MsgTieAt.lean). And the one closed test that this road asks, "any two
members at one seat have one shape" (`oneShapeB`, Johnson/Desc/First/Look/K3MaskOkTools.lean), is
paid at the head.

Row or tool. A general law, a fact on a written value with a negative test, and ties under the head
by calls. For the law on the digits of the sub-protocol K8: the condition `DigAheadOk` at the state
behind the draw of the approximate range proof.

What it spends. Rows are those of the proof file's entry tests, `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean), counted from 1: row 1 holds the
declared rounds to the written ones, row 9 the made plan (`madeRow`), row 11 is the lookups' digits'
row (`digEntry`). `memAt_at_head`: no row: the head's field `k3` (its part `digSomeB`), and the
premise h6. `oneShape_at_head`: rows 9 and 1: row 9 by the first half of `pins_of_laid`
(Johnson/Goal/Skeleton/PinsOfLaid.lean); row 1 inside `seats_in_scope`
(Johnson/P5T/PlanSeatsTie.lean), which takes "the value is laid" and calls `plans_written`.
`oneShape_of_plan`, `onePlan_written` and `e_onePlan_rejects`: no field of the head.

What is here (namespace Q38).
  `memAt_at_head`: under `h6 : oneShapeB (At.ms Zp Z.lay) = true`: `MemAt` at every member. By
    `P5T.some_of_someB` (Johnson/P5J/Rad3Seat3At.lean) and `memAt_of_some`; that the place bears the
    segment's number is `digAt_link` (Johnson/HB/LLHARD/Q38A/DigAtLink.lean).
  `onePlanB ps`: of a list of entries of `planSeats` (Johnson/P5T/PlanSeats.lean: each a seat with
    the shape of the oracle message that sits there): any two at one seat have one shape.
  `oneShape_of_plan`: general, free of the radii: `onePlanB` at the sampled entries of `planSeats`
    gives `oneShapeB` at the members that are made of them: by `memsSame_atR`
    (Johnson/P5T/MembersByMake.lean).
  `onePlan_written`: `onePlanB` accepts at the sampled entries of the written list `psFull`. No new
    evaluation: no seat stands twice among them (`seats_one`, Johnson/HB/LLHARD/Q38E/SeatsOne.lean,
    by Lean's kernel there; 167 entries). So the accept says no more than "no two at one seat".
  `e_onePlan_rejects`: the negative test: with a copy of the first sampled entry laid in front whose
    shape has one main row more, it rejects.
  `oneShape_at_head`: so `oneShapeB (At.ms Zp Z.lay) = true` at the head.
By an evaluation in Lean's kernel (`decide +kernel`): `e_onePlan_rejects`.

Limits. `oneShapeB` is the one of the namespace VerifiableInference.OnPublicFiles; a test of the same text
in another namespace is not touched. Nothing on soundness.


-/
import Johnson.HB.LLHARD.Q38E.SeatsOne
import Johnson.HB.LLHARD.Q38A.DigAtLink
import Johnson.P5J.MgAtAll
import Johnson.P5T.MembersByMake
import Johnson.P5T.PlanSeatsTie
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.Desc.First.Look.K3CallsAddress
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.P5J.Rad3Seat3Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (MemAt)
open VerifiableInference.OnPublicFiles (oneShapeB memAt_of_some)
open P5T (PSeat psFull planSeats msAtR memsSame_atR seats_in_scope)
open P5J (AtMgA)

/-- Of a list of entries of `planSeats`: any two at one seat have one shape. -/
def onePlanB (ps : List PSeat) : Bool :=
  ps.all fun p => ps.all fun q => !decide (p.seat = q.seat) || p.shape == q.shape

/-- **From the sampled entries of `planSeats` to the members that are made of them.** -/
theorem oneShape_of_plan (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ) :
    onePlanB ((planSeats Z Z.D.1).filter (·.smpd)) = true → oneShapeB (msAtR Z rad) = true := by
  intro h
  simp only [onePlanB, List.all_eq_true] at h
  simp only [oneShapeB, List.all_eq_true]
  intro y hy y' hy'
  obtain ⟨p, hp, ep⟩ := List.mem_map.1 ((memsSame_atR Z rad _).1 (List.mem_map.2 ⟨y, hy, rfl⟩))
  obtain ⟨q, hq, eq⟩ := List.mem_map.1 ((memsSame_atR Z rad _).1 (List.mem_map.2 ⟨y', hy', rfl⟩))
  obtain ⟨p1, p2⟩ := Prod.mk.inj ep
  obtain ⟨q1, q2⟩ := Prod.mk.inj eq
  have t := h p hp q hq
  rw [p1, p2, q1, q2] at t
  exact t

/-- **The test accepts at the written list's sampled entries.** -/
theorem onePlan_written : onePlanB (psFull.filter (·.smpd)) = true := by
  simp only [onePlanB, List.all_eq_true]
  intro p hp q hq
  by_cases e : p.seat = q.seat
  · have e2 : ((p.shape, p.seat) : OracleShape × (ℕ × ℕ)) = (q.shape, q.seat) :=
      List.inj_on_of_nodup_map seats_one (List.mem_map.2 ⟨p, hp, rfl⟩)
        (List.mem_map.2 ⟨q, hq, rfl⟩) e
    rw [(Prod.mk.inj e2).1]
    simp
  · simp [e]

/-- The written sampled entries, with a bent copy of the first in front. -/
def e_bent : List PSeat :=
  ((psFull.filter (·.smpd)).head?.toList.map fun p =>
    { p with shape := { p.shape with mainRows := p.shape.mainRows + 1 } }) ++
      psFull.filter (·.smpd)

set_option maxRecDepth 1000000 in
/-- The negative test. -/
theorem e_onePlan_rejects : onePlanB e_bent = false := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : Place}

/-- **"One seat, one shape", at the head.** -/
theorem oneShape_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    oneShapeB (P5J.At.ms Zp Z.lay) = true := by
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hl := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have hps := (seats_in_scope h.scope h.laid.pub hy hl).1
  refine oneShape_of_plan Zp (P5J.At.rad Zp Z.lay) ?_
  rw [hps]
  exact onePlan_written

set_option maxRecDepth 40000 in
/-- **At every member of the digits' list: the first member of the table's list at its seat has its
shape.** -/
theorem memAt_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    {x : Place} {tl : HTailF2} (hx : digAt (P5J.At.X Zp) l = some (x, tl))
    (h6 : oneShapeB (P5J.At.ms Zp Z.lay) = true) :
    ∀ k : Fin (digList x h.𝔇.sent h.𝔇.l3.rad).length,
      MemAt h.𝔇.ms (digList x h.𝔇.sent h.𝔇.l3.rad) (fun j => h.𝔇.l3.seat x.link true j.1) k := by
  obtain rfl := digAt_link hx
  have hlen : x.link < P5J.At.links.length := Nat.lt_succ_of_le hl
  have hs : P5J.At.digSomeB Zp Z.lay x.link = true :=
    (P5J.At.k3SeatsB_at Zp cF Z.lay h.k3 x.link hlen).2.2.2.2.1
  intro k
  exact memAt_of_some (P5T.some_of_someB _ _ _ hs k) h6

end

end Q38


#print axioms Q38.oneShape_of_plan
#print axioms Q38.onePlan_written
#print axioms Q38.e_onePlan_rejects
#print axioms Q38.oneShape_at_head
#print axioms Q38.memAt_at_head
