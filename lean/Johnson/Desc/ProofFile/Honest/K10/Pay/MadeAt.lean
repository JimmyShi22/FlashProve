-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeAt.lean: the closing of a segment (K10): in front of the closing of segment l, at
a state that the first chain's own blocks reach, under the library's head: the lot's job makes the group's rows and they pass
the public test `rowsFit`, from three premises on the filling and on what was heard.

  `dues_of_borne`   the counts of the carried runs hang on the shape, the codes and the link alone
  `made_reached`    the field made of `CarryOwed` (Honest/K10/Xch/CarryTop.lean) at one input and list of challenges

Limits. Premises: that the lot's segments are the written ones; the test `ownReady` on the filling (Honest/K2/AtPlan.lean);
`heardAll`. The head is a premise. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeClosed
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeFit
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeRoomy
import Johnson.Desc.K10.Honest.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par noK10 kbAt seatsPlanW)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2 linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2 (SegmentPub Stretch ownReady freshTable segmentsOf)
open ProofFile.Honest.K2.Law (segsW)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- The counts of what the part at segment l carries hang on no sender. -/
theorem borneOf_counts (s : OnBytes.Params.ReqShape) (codes : OnBytes.Codes) (f g : Nat → Nat → Addr) (l : Nat) :
    (borneOf s codes f l).map (·.count) = (borneOf s codes g l).map (·.count) := by
  unfold borneOf borneIn
  simp only [List.map_flatMap, List.map_map]
  rfl

/-- At the written shape and codes the counts of the lot's carried runs are the written ones. -/
theorem dues_of_borne {Zp : ProofFile.Pub} (hs : Zp.first.shape = shapeFull) (hc : Zp.first.codes = codesFull2) (Q : Par) :
    (closeCarries ⟨Q, borneAt Zp Q⟩).map (·.2) = duesW Q.link := by
  show ((borneAt Zp Q).map fun m => (carriedName m.sender m.msg (closeAddr Q), m.count)).map (·.2) = _
  rw [List.map_map]
  show (borneAt Zp Q).map (·.count) = _
  unfold borneAt borneAtOf duesW
  rw [hs, hc]
  exact borneOf_counts _ _ _ _ _

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr : Type}

/-- **In front of a closing the lot's job makes the group's rows, and they pass the public test.** -/
theorem made_reached (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {Qc : Par} (hQ : Qc.link = l) {Gr : ProofFile.Ground} (hS : segmentsOf Zp Gr = segsW)
    {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (w : Local W₀ Rc ProofFile.Inst Tr) (front : List Fmt.Drawn)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Zp Gr Qc).pub))
    (hReady : ownReady (rows w.x) Gr.first.layout (askPlace (addrsAt Zp Gr)) (lotSegs Zp Gr Qc) front = .ok ())
    (hHeard : heardAll (lotSegs Zp Gr Qc) front = .ok ()) :
    ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows w front ca = .ok R ∧ rowsFit s.st D.G R = true := by
  have eS : lotSegs Zp Gr Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Gr).take (Qc.link + 1) = _
    rw [hS, hQ]
  have eD : (closeCarries (lotJob readers rows stAt Zp Gr Qc).pub).map (·.2) = duesW l := by
    rw [← hQ]
    exact dues_of_borne h.toAtMg.shape_full h.toAtMg.codes_full Qc
  -- the closed tests at l
  have hk := List.all_eq_true.1 segs_written l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨k1, k3⟩ := hk
  have k2 := roomy_take (l + 1)
  obtain ⟨S, hLast, hS3⟩ : ∃ S, (segsW.take (l + 1)).getLast? = some S ∧ lastTest S = true := by
    have hw := List.all_eq_true.1 last_written l (List.mem_range.2 hl)
    cases e : (segsW.take (l + 1)).getLast? with
    | none =>
      rw [e] at hw
      cases hw
    | some S =>
      rw [e] at hw
      exact ⟨S, rfl, hw⟩
  have hRuns : (borneAt Zp Qc).length = runsAsked (lotSegs Zp Gr Qc) := by
    have e1 := congrArg List.length eD
    rw [List.length_map] at e1
    have e2 : (closeCarries (lotJob readers rows stAt Zp Gr Qc).pub).length = (borneAt Zp Qc).length :=
      List.length_map _
    rw [eS, ← k3, ← e1, e2]
  -- the shared text returns
  have hTest := List.all_eq_true.1 rows_written l (List.mem_range.2 hl)
  obtain ⟨ms, hms, hmw⟩ : ∃ ms, groupS (segsW.take (l + 1)) (duesW l) = some ms ∧
      ms.map (fun m => (m.shape, m.kept)) = membersW l := by
    unfold rowsTest at hTest
    cases e : groupS (segsW.take (l + 1)) (duesW l) with
    | none =>
      rw [e] at hTest
      cases hTest
    | some ms =>
      rw [e] at hTest
      exact ⟨ms, rfl, eq_of_beq hTest⟩
  have hK : DuesAt (duesW l) (Stretch.carried _ ca) := eD ▸ carried_dues _ ca
  rw [← eS] at hms
  obtain ⟨R, hR, hRm⟩ := groupRows_ok freshTable (lotOwn readers rows Zp Gr Qc w front) front hK
    (fun i S' hi c => roomy_at (l + 1) i S' (eS ▸ hi) c) hms
  refine made_of_parts readers rows stAt Zp Gr Qc w front ca hReady hHeard (eS ▸ hLast) (eS ▸ k1) (eS ▸ k2) hRuns hR ?_
  -- the public test
  obtain ⟨hI, hc, hsh, -, -⟩ := facts_reached h hr hf
  have H := shapes_reached h hl hr hf D.G Hb.there
  have e1 : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.laid.seats h.toAtMg.scope
  have e2 : P5J.At.seats Zp = seatsPlanW := by
    unfold P5J.At.seats
    rw [e1]
  rw [e1, e2] at H
  unfold lastTest at hS3
  simp only [Bool.and_eq_true, beq_iff_eq] at hS3
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hS3
  have es : (recOf s).frame.shape = shapeFull := hsh.trans h.toAtMg.shapeAt_full
  refine rowsFit_of_parts H Hb.inOrder ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (hc.trans h.toAtMg.codes_full).trans a1.symm
  · show D.G.code = S.sizes.code
    rw [Hb.code, es, a2]
  · show D.G.maskCode = S.sizes.maskCode
    rw [Hb.maskCode, es, a3]
  · show OnBytes.powerOfTwo (S.sizes.codes.base.getD S.sizes.code default).ell = true
    rw [a1, a2]
    exact a4
  · show OnBytes.powerOfTwo (S.sizes.codes.mask.getD S.sizes.maskCode default).ell = true
    rw [a1, a3]
    exact a5
  · exact List.all_eq_true.1 rising_written l (List.mem_range.2 hl)
  · rw [out_members S (groupRows_count hR), hRm]
    exact hmw

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.borneOf_counts
#print axioms ProofFile.Honest.K10.dues_of_borne
#print axioms ProofFile.Honest.K10.made_reached
