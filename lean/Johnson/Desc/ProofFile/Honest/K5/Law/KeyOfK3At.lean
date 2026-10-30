-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeyOfK3At.lean: CONDITIONAL, under the library's hypothesis on
the public input (`P5J.AtMgA`): WHAT THE READER OF THE KEY POINTS `keyOfK3`
(Honest/K5/Law/KeyOfK3.lean) IS AT THE TWELVE ATTENTION SEGMENTS: `keyPtsAt` (Honest/K3/Heard.lean)
at the group's plan's shape and at the number of the first chain's rounds in front of the segment's
lookup on the calls; and that the cut of a point of the right length has the form that the library
asks of a lookup's key points (`K3Pts`, Johnson/Desc/First/Att/K05LookAll.lean).

  `steps3AllB`, `steps3_closed`, `steps3_bite`   the written table of steps counts 1982 + 3857 g
                    rounds in front of "A‹g›.1.call": a closed fact, by the kernel, with a control
  `flat3AllB`, `flat3_closed`, `flat3_bite`      the written rows have as many in front of the row
                    number 14 (2 g + 1) + 3: likewise
  `place3B`, `place3_closed`, `place3_bite`      that row's place is the segment's piece 2, of the
                    kind K3: the written place right in front of the kind's own: likewise
  `base3_at_head`   CONDITIONAL: the table of steps counts, in front of "A‹g›.1.call", the rounds in
                    front of that member
  `keyOfK3_at_head` CONDITIONAL: **the reader is `keyPtsAt` at the plan's shape and that number**:
                    so under the hypothesis its idle arm is not taken
  `k3Pts_cut`       CONDITIONAL: **`K3Pts` of the cut of a point with dT + rK coordinates**, where
                    the shape has four calls

Limits. At the full size and the written tables alone. h is a hypothesis of every statement that
names it. The closed facts are facts on written tables: that any public files give these tables is
the hypothesis's matter. Nothing here says that the reader's value is what the verifier's state
holds.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.KeyOfK3
import Johnson.Desc.ProofFile.Honest.K5.Law.BaseAt
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns
import Johnson.Desc.First.Att.K05LookAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First.Att.P (K3Pts)
open VerifiableInference.PlanWritten (cutOf cutFirstFull pubBy_entries)
open H2K5.Row (roundsBy cutPairsW roundsBefore_by cuts_of_plans asBy)
open OnBytes.Maker (WholeD)
open ProofFile.Honest.K3 (keyPtsOf keyPtsAt)
open P5J (AtMgA TS)

/-! ## 1 Three closed facts on written tables -/

/-- The test: the written table of steps counts `want g` rounds in front of "A‹g›.1.call". -/
def steps3AllB (want : Nat → Nat) : Bool :=
  (List.range 12).all fun g =>
    decide (roundsBy cutPairsW ("A" ++ toString g ++ ".1.call") = some (want g))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written table of steps, at the twelve names.** No premise: a closed fact, by the kernel.
-/
theorem steps3_closed : steps3AllB (fun g => 1982 + 3857 * g) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no. No premise: a closed fact, by the kernel. -/
theorem steps3_bite : steps3AllB (fun g => 1983 + 3857 * g) = false := by decide +kernel

/-- The test: the written rows have `want g` rounds in front of the row number 14 (2 g + 1) + 3. -/
def flat3AllB (want : Nat → Nat) : Bool :=
  (List.range 12).all fun g =>
    decide (((cutFirstFull.take (14 * (2 * g + 1) + 3)).map (·.2.2.1)).sum = want g)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written rows, in front of the twelve members.** No premise: a closed fact, by the kernel.
-/
theorem flat3_closed : flat3AllB (fun g => 1982 + 3857 * g) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no. No premise: a closed fact, by the kernel. -/
theorem flat3_bite : flat3AllB (fun g => 1983 + 3857 * g) = false := by decide +kernel

/-- The test: the written place number 14 (2 g + 1) + 3 is the piece `pc` of segment 2 g + 1, of the
kind K3. -/
def place3B (pc : Nat) : Bool :=
  (List.range 12).all fun g =>
    decide (P5J.At.ps[14 * (2 * g + 1) + 3]? = some ⟨1, some (2 * g + 1), pc, .K3⟩)

set_option maxRecDepth 1000000 in
/-- **The written place right in front of the kind's own is the segment's lookup on the calls.** No
premise: a closed fact, by the kernel. -/
theorem place3_closed : place3B 2 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can say no. No premise: a closed fact, by the kernel. -/
theorem place3_bite : place3B 3 = false := by decide +kernel

/-! ## 2 Under the hypothesis -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **THE TABLE OF STEPS COUNTS, IN FRONT OF "A‹g›.1.call", THE ROUNDS IN FRONT OF THE SEGMENT's
LOOKUP ON THE CALLS.** CONDITIONAL: under the hypothesis h; g is below 12. -/
theorem base3_at_head {g : Nat} (hg : g < 12) :
    Zp.roundsBefore? ("A" ++ toString g ++ ".1.call") =
      some (roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3)) := by
  obtain ⟨hm, hc⟩ := H2K5.Door.pins_at_head h.toAtMg
  have W := H2K12.written354_of_pins h.scope h.laid.pub hm h.laid.laidPOf
  have hZ := asBy h.laid.pub
  have hcuts := cuts_of_plans hZ ((pubBy_entries hZ).1.symm.trans W.entries)
  have e1 := of_decide_eq_true (List.all_eq_true.1 steps3_closed g (List.mem_range.2 hg))
  have e2 := of_decide_eq_true (List.all_eq_true.1 flat3_closed g (List.mem_range.2 hg))
  rw [roundsBefore_by, hcuts, roundsTo_cut, hc]
  exact e1.trans (congrArg some e2.symm)

/-- **THE READER IS `keyPtsAt` AT THE PLAN's SHAPE AND THAT NUMBER.** CONDITIONAL: under the
hypothesis h; g is below 12; hG: G is the ground that the description's maker makes; the group's
plan. -/
theorem keyOfK3_at_head {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) (heard : List Fmt.Drawn) :
    keyOfK3 Zp G (2 * g + 1) heard =
      (keyPtsAt a.fs (roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3)) heard).zk := by
  have e0 : (2 * g + 1) / 2 = g := by omega
  have e1 : G.W.A[g]? = some a := by
    rw [ground_at_head h hG]
    exact ha
  unfold keyOfK3
  rw [e0, e1, base3_at_head h hg]

end

/-! ## 3 The cut has the library's form -/

/-- **`K3Pts` OF THE CUT.** CONDITIONAL: the point has dT + rK coordinates; the shape has four
calls. -/
theorem k3Pts_cut (s : OnBytes.Model.Forest.Shape) {p : Array E} (hp : p.size = s.dT + s.rK)
    (nc : s.NC = 4) :
    K3Pts s (keyPtsOf s p).zx (keyPtsOf s p).zy (keyPtsOf s p).zk
      (OnBytes.Slice.readV ((keyPtsOf s p).zx ++ (keyPtsOf s p).zy)) where
  nx := by
    show (p.extract 0 s.dT).size = s.dT
    rw [Array.size_extract]
    omega
  ny := by
    show (p.extract s.dT p.size).size = s.rK
    rw [Array.size_extract]
    omega
  zk := fun q => by
    have hq : q.1 < s.NC := by
      rw [nc]
      exact q.2
    show ((Array.range s.NC).map fun c =>
      (p.extract s.dT p.size).extract (s.rK - s.iota.getD c 0) (p.extract s.dT p.size).size ++
        p.extract 0 s.dT).getD q.1 #[] = _
    simp [keyPtsOf, Array.getD_eq_getD_getElem?, hq]
  z := rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.steps3_closed
#print axioms ProofFile.Honest.K5.steps3_bite
#print axioms ProofFile.Honest.K5.flat3_closed
#print axioms ProofFile.Honest.K5.flat3_bite
#print axioms ProofFile.Honest.K5.place3_closed
#print axioms ProofFile.Honest.K5.place3_bite
#print axioms ProofFile.Honest.K5.base3_at_head
#print axioms ProofFile.Honest.K5.keyOfK3_at_head
#print axioms ProofFile.Honest.K5.k3Pts_cut
