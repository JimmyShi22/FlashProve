-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/DeclaredSeatsAtHead.lean: THE SEATS THAT THE FIRST CHAIN's FLAT LIST DECLARES (tree by
tree, the trees counted from 0 along the list; tenant by tenant of each declared oracle message)
AGAINST THE PLAN's LIST OF THE FIRST CHAIN's SEATS (P5J.At.seats Zp, Johnson/P5J/LettersAt.lean).
For the authors of a joined Script, whose test on a list of seats asks: does the list hold every
seat that the flat list declares. PUBLIC DATA ALONE: declared trees and tenants, a plan's seats:
where a message sits, never what stands in it. One definition, eight theorems. A TRIAL THAT COUNTS
IN NO COLUMN.
NO PROPERTY IS CLAIMED.

With no premise:
  - first_in_all: each seat of the plan's list of the first chain (P5J.At.pseats Zp) stands in the
    list of all three chains' (P5J.At.pseatsAll Zp): by the text of P5T.planSeatsAll, which begins
    with the first chain's.
At the written data:
  - declaredSeatsW: A DEFINITION: the seats that the written cut's rows declare (over the library's
    ToldDesc.toldFirstFull, Johnson/ToldDescR/PlanShapesOfCut.lean: 83 trees).
  - declaredW_in_plan: each of them is (p.j, p.t) of a seat p of the written plan's list P5T.psFull.
    By evaluation in Lean's kernel. declaredW_bent: A NEGATIVE TEST: against that list without its
    first member the test says no.
  - plan_in_declaredW, declaredW_count: the other way round, and the two lists are equally long.
Under h (the library's head: A HYPOTHESIS):
  - told_head: what the flat list's blocks declare, in a row, is the written list of 83.
  - declared_head: **each seat that the flat list declares is a seat of the plan's list of the
    first chain**: stated at the text of another house's flatSeats
    (Johnson/Desc/ProofFile/Honest/Thread/JoinFit.lean; NOT IMPORTED), written out: so it can be
    handed to a premise on flatSeats cF.blocksInOrder as it stands.
  - declared_head_all: the weaker form: it is (q.j, q.t) of a q in the list of all three chains'.

By what. The library's oraclesOf_cut (PlanShapesOfCut.lean: what blocks declare is read off their
cut's rows), cut_of_head and written_of_head (Johnson/Road/K4/K4HeadWritten.lean: under the head the
first chain's cut is the written one) and seatsAt_written (Johnson/Road/K4/K4PlanTied.lean).

Kin. told_head HAS A SISTER IN THE LIBRARY: oracles_of_cut (Johnson/Desc/AtSeats/FromTheCut.lean):
where the cut is the written one, what the blocks declare is osC
(Johnson/Desc/AtSeats/FitsAtPlan.lean): another written spelling of the list of 83; that osC and
toldFirstFull are one list is stated nowhere that we found. We go by toldFirstFull, which
oraclesOf_cut gives by rewriting alone. first_in_all stands as an inner step of a proof in
Johnson/Goal/HonestTrace/SeatsApartAtHead.lean; here it has a name. Near plan_in_declaredW:
fits_written and seats_below (FitsAtPlan.lean): the plan's 167 sampled seats against osC; and the
library's test on one seat (is its tree told; has it that tenant): seatFaultO,
Johnson/P5T/SeatsFitWritten.lean. Our
rows numbered_two, numbered_fifty and numbered_w (Johnson/Desc/ProofFile/Honest/K1/Law/
SeatsAtTwo.lean, SeatsAtFifty.lean, SeatsAtW.lean) have, under their own premises, the sender's own
seats in P5J.At.seats Zp, member by member, at the messages that have an answer.

Limits. THE FULL SIZE ALONE. The three last are CONDITIONAL on h, at the format's second hash function. THE
FIRST CHAIN ALONE. WHO OWNS A SEAT IS NOT SAID: that a declared seat in one of a sender's sendings
is among that sender's lots' seats is another sentence. That no seat is declared twice is not said.
Nothing on a run, or on what any coin is. Nothing on soundness, on completeness or on any other
property.
Whoever calls one of the last three in front of a law over coins names h beside it: it is a premise,
paid nowhere here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.ToldDescR.PlanShapesOfCut
import Johnson.Road.K4.K4HeadWritten
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open OnBytes.Road.K4 (written_of_head cut_of_head seatsAt_written)
open ToldDesc (toldFirstFull oraclesOf_cut)

/-- With no premise: the first chain's seats stand in the list of all three chains'. -/
theorem first_in_all (Zp : ProofFile.Pub) : ∀ p ∈ P5J.At.pseats Zp, p ∈ P5J.At.pseatsAll Zp :=
  fun _ hp => List.mem_append_left _ (List.mem_append_left _ hp)

/-- The seats that the written cut's rows declare: tree by tree, tenant by tenant. -/
def declaredSeatsW : List (ℕ × ℕ) :=
  toldFirstFull.zipIdx.flatMap fun o => (List.range o.1.tenants.length).map fun t => (o.2, t)

set_option maxRecDepth 1000000 in
/-- Each seat that the written cut declares is a seat of the written plan's list. -/
theorem declaredW_in_plan :
    (declaredSeatsW.all fun s => (P5T.psFull.map fun p => (p.j, p.t)).contains s) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: against the plan's list without its first member it says no. -/
theorem declaredW_bent :
    (declaredSeatsW.all fun s => (P5T.psFull.map fun p => (p.j, p.t)).tail.contains s) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The other way round: each seat of the written plan's list is declared. -/
theorem plan_in_declaredW :
    ((P5T.psFull.map fun p => (p.j, p.t)).all fun s => declaredSeatsW.contains s) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The two lists are equally long. -/
theorem declaredW_count : declaredSeatsW.length = P5T.psFull.length := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- h IS A PREMISE. What the flat list's blocks declare, in a row, is the written list. -/
theorem told_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder.flatMap fun blk => blk.oracles.flatMap id) = toldFirstFull := by
  have e := oraclesOf_cut cF.blocksInOrder
  rw [cut_of_head h.toAtMg] at e
  exact e

/-- h IS A PREMISE. **EACH SEAT THAT THE FLAT LIST DECLARES IS A SEAT OF THE PLAN's LIST OF THE
FIRST CHAIN.** -/
theorem declared_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ s ∈ ((cF.blocksInOrder.flatMap fun blk => blk.oracles.flatMap id).zipIdx.flatMap fun o =>
      (List.range o.1.tenants.length).map fun t => (o.2, t)), s ∈ P5J.At.seats Zp := by
  intro s hs
  rw [told_head h] at hs
  have e : P5J.At.seats Zp = P5T.psFull.map fun p => (p.j, p.t) := by
    show (P5J.At.pseats Zp).map _ = _
    rw [show P5J.At.pseats Zp = P5T.psFull from seatsAt_written (written_of_head h.toAtMg)]
  rw [e]
  exact List.contains_iff_mem.1 (List.all_eq_true.1 declaredW_in_plan s hs)

/-- h IS A PREMISE. The weaker form: a declared seat is the seat of a member of the list of all
three chains'. -/
theorem declared_head_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ s ∈ ((cF.blocksInOrder.flatMap fun blk => blk.oracles.flatMap id).zipIdx.flatMap fun o =>
      (List.range o.1.tenants.length).map fun t => (o.2, t)),
      ∃ q ∈ P5J.At.pseatsAll Zp, s = (q.j, q.t) := by
  intro s hs
  obtain ⟨q, hq, e⟩ := List.mem_map.1 (declared_head h s hs)
  exact ⟨q, first_in_all Zp q hq, e.symm⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.first_in_all
#print axioms AtFullSide.K1.declaredSeatsW
#print axioms AtFullSide.K1.declaredW_in_plan
#print axioms AtFullSide.K1.declaredW_bent
#print axioms AtFullSide.K1.plan_in_declaredW
#print axioms AtFullSide.K1.declaredW_count
#print axioms AtFullSide.K1.told_head
#print axioms AtFullSide.K1.declared_head
#print axioms AtFullSide.K1.declared_head_all
