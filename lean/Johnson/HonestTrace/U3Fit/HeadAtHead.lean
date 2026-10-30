-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/HeadAtHead.lean

Under the head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) and two more premises,
"valsHalf" (same file) says yes at the seat of segment 24, the output head's: the maker of the
values of "U3" (Johnson/HonestTrace/U3Rows.lean) returns there, its rounds end where the sending
begins, and its number of reads is the array's columns. The two premises: "cov.sized G.W.hS.T =
true" (as many covered positions as positions) and "LookFits Zp spotsWritten 24 .K6 G.W.HLy.fs"
(Johnson/HonestTrace/U3Fit/ValsGeneral.lean). One definition; theorems. Public data alone. A SegVals
is carried whole; its field vec, a function that awaits the trace's cells, is applied nowhere here.

Main theorems:
* "headRounds_at_head": the output head's own table of rounds ("(headParAt G).rounds") is the
  written table's list at "H:4", by the steps of "k6_rounds_row" (Johnson/AtFull/Rounds/K6.lean).
* "headInFront_at_head": the reader of the output head's challenges counts 82 rounds.
* "entries_at_head", "nU_at_head": the declared rounds' entries and the plan's number of reads are
  the written ones.
* "valsHalf_head_at_head": the end.

Definition: "headW", a test at written values: the places of K6 and K3 at segment 24 are found; the
written entries, cut at the K6 place's first round, 82 of them, are those of "H:4"; at the seat of
segment 24 these rounds end where the sending begins, and the array's columns are the written number
of reads, which is not 0.

Limits. The head is a premise: the full size and the format's second hash function alone. "LookFits" is a
premise here; "lookFits_head" (Johnson/HonestTrace/U3Fit/LookFits.lean) shows it under the head. Two
closed facts, "headW_yes" and "headW_can_fail" (four controls), are shown by "decide +kernel", each
under "set_option maxRecDepth 1000000", which raises the elaborator's depth of recursion. "headW"
asks nothing of a list without a seat of segment 24; that there is one is "seat_of_seg"
(Johnson/HonestTrace/U3Fit/ReturnsAtHead.lean). No control parts its clause on "heard" from the one
on the columns, and none reaches its arm for a place that is not found.
Not claimed: anything on the vector's entries, on "ready", on the other 24 segments. No property of
a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.HonestTrace.U3Fit.MatsAtHead
import Johnson.AtFull.Rounds.K6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest.K3 (tlOf)
open ProofFile.Honest.K6 (headParAt headInFront headCut headLt headLPd)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.Kinds.Head (rounds)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.Prices (recAt k6_entries)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (numbers_in_scope work_ref)
open VerifiableInference.PlanWritten (xShapeOf)
open Johnson.AtFull.Lots (lPdAt)
open Johnson.AtFull.Rounds (listAt k6RoundsAt k6_rounds_written)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.G (xShapeFull)
open P5J (AtMgA TS)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head, two numbers of the output head's shape: ten bits of positions, thirteen of features. -/
theorem headBits_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : G.W.hS.lt = 10 ∧ lPdAt G.W.hS = 13 := by
  have hW := IM.ground_publicK h.laid.pub hG
  have N := numbers_in_scope h.scope h.reads hW
  refine ⟨N.lt, ?_⟩
  unfold lPdAt VerifiableInference.Desc.Kinds.Norm.lPd
  rw [show (letI := VerifiableInference.Desc.Kinds.Head.sizesOf G.W.hS; VerifiableInference.Desc.Kinds.Norm.d) = 5120 from N.d]
  decide

/-- **The output head's own table of rounds is the written table's list at "H:4".** -/
theorem headRounds_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : (headParAt G).rounds = listAt "H:4" := by
  have hW := IM.ground_publicK h.laid.pub hG
  obtain ⟨hlt, hl⟩ := headBits_at_head h hG
  have hw : workOf G.W = 0 := by
    unfold workOf
    rw [_root_.Meaning.HeadS.frame_in_scope h.scope h.reads hW]
    exact work_ref
  have e := @k6_entries (VerifiableInference.Desc.Kinds.Head.sizesOf G.W.hS) (workOf G.W) (by
    show 0 < G.W.hS.lt
    rw [hlt]
    decide)
  have k : (headParAt G).rounds = k6RoundsAt (workOf G.W) G.W.hS.lt (lPdAt G.W.hS) := by
    show (@rounds (VerifiableInference.Desc.Kinds.Head.sizesOf G.W.hS)).map
      (fun r => ({ entry := VerifiableInference.Desc.Kinds.Round.entry (workOf G.W) r } :
        Fmt.DeclaredRound)) = _
    unfold k6RoundsAt
    rw [show OnBytes.Tie.Pv.Head.headOwnList (workOf G.W) (recAt G.W.hS.lt (lPdAt G.W.hS)) =
      (@rounds (VerifiableInference.Desc.Kinds.Head.sizesOf G.W.hS)).map (VerifiableInference.Desc.Kinds.Round.entry (workOf G.W))
      from e.symm, List.map_map]
    rfl
  rw [k, hw, hlt, hl]
  exact of_decide_eq_true k6_rounds_written

/-- The reader of the output head's challenges counts 82 rounds. -/
theorem headInFront_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) : headInFront (headParAt G) 8 = 82 := by
  obtain ⟨hlt, hl⟩ := headBits_at_head h hG
  have a : headLt (headParAt G) = 10 := hlt
  have b : headLPd (headParAt G) = 13 := hl
  unfold headInFront headCut
  rw [a, b]
  rfl

/-- The declared rounds' entries are the written ones. -/
theorem entries_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) :
    Zp.D.1.map (·.entry) = P5T.esFull.1 :=
  H2K5.Row.hD_made h.laid.pub
    (VerifiableInference.PlanWritten.Joined.proof_plans_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h))

/-- The plan's number of reads at the output head, off the written shape part. -/
theorem nU_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    G.W.H.nU.getD 2 0 = xShapeFull.2.1.getD 2 0 := by
  obtain ⟨ls, -, eW, -, -⟩ := IM.blank_ground hG
  have S := VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub
    (VerifiableInference.Desc.K1.pin1_atAll h)
  rw [← S, eW]
  show Zp.p.X.H.nU.getD 2 0 = Zp.p.X.H.nU.toList.getD 2 0
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **A TEST AT WRITTEN VALUES** (told at the top of this file). cuts, sps: the table of steps and its
places; es: the declared rounds' entries; own: the output head's own table of rounds; n: the number
of reads; seats: the seats of "U3". -/
def headW (cuts : List VerifiableInference.Desc.First.Cut) (sps : List Spot) (es : List Fmt.Entry)
    (own : List Fmt.DeclaredRound) (n : Nat) (seats : List Seat) : Bool :=
  match placeBy cuts sps 24 .K6, placeBy cuts sps 24 .K3 with
  | .ok k6, .ok _ =>
    own.length == 82 && (es.drop k6.2).take 82 == own.map (·.entry) && n != 0 &&
      seats.all fun s => s.seg != 24 || (k6.2 + 82 == s.heard && s.array.sizeC == n)
  | _, _ => false

set_option maxRecDepth 1000000 in
/-- The test says yes at the written values. -/
theorem headW_yes : headW cutWritten spotsWritten P5T.esFull.1 (listAt "H:4")
    (xShapeFull.2.1.getD 2 0) (seatsW "U3") = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls: the list of "H:3" in the place of "H:4"'s · the written entries without their first ·
one read more · the seats of "BZ": the test says no. -/
theorem headW_can_fail :
    (headW cutWritten spotsWritten P5T.esFull.1 (listAt "H:3") (xShapeFull.2.1.getD 2 0)
        (seatsW "U3") ||
      headW cutWritten spotsWritten (P5T.esFull.1.drop 1) (listAt "H:4") (xShapeFull.2.1.getD 2 0)
        (seatsW "U3") ||
      headW cutWritten spotsWritten P5T.esFull.1 (listAt "H:4") (xShapeFull.2.1.getD 2 0 + 1)
        (seatsW "U3") ||
      headW cutWritten spotsWritten P5T.esFull.1 (listAt "H:4") (xShapeFull.2.1.getD 2 0)
        (seatsW "BZ")) = false := by decide +kernel

/-- **UNDER THE HEAD, cov.sized AND THE LOOKUP's TWO CLAUSES: "valsHalf" AT THE SEAT OF THE OUTPUT
HEAD's SEGMENT.** -/
theorem valsHalf_head_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cov : Head.Covered}
    (hc : cov.sized G.W.hS.T = true) (hL : LookFits Zp spotsWritten 24 .K6 G.W.HLy.fs) :
    ∀ s ∈ u3Seats Zp G, s.seg = 24 → valsHalf Zp G cov s = true := by
  intro s hs h24
  obtain ⟨Y, hb, hk, -⟩ := (IM.ground_named h.scope h.reads h.laid.pub hG).2
  have hw := headW_yes
  unfold headW at hw
  have q6 := placeIn_by Zp spotsWritten 24 .K6
  have q3 := placeIn_by Zp spotsWritten 24 .K3
  rw [cuts_at_head h] at q6 q3
  cases e6 : placeBy cutWritten spotsWritten 24 .K6 with
  | error e =>
    rw [e6] at hw
    cases hw
  | ok k6 =>
    cases e3 : placeBy cutWritten spotsWritten 24 .K3 with
    | error e =>
      rw [e6, e3] at hw
      cases hw
    | ok k3 =>
      rw [e6, e3] at hw
      rw [e6] at q6
      rw [e3] at q3
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hw
      obtain ⟨⟨⟨w1, w2⟩, w3⟩, w4⟩ := hw
      have hr := headRounds_at_head h hG
      have hlen : ((headParAt G).rounds.map (·.entry)).length = 82 := by
        rw [List.length_map, hr]
        exact w1
      have hm : fitsMats G.W 24 G.W.H.tl.mats = true := by
        have k := fitsMats_at_head h hG (seg := 24) (by decide)
        rw [tlOf_planMats (marks_at_head h hG) (by decide : 24 < 25)] at k
        exact k
      obtain ⟨V, hV, hn, hf⟩ := headVals_returns (cov := cov) q6 q3
        (by rw [hlen, declared_by, entries_at_head h, hr]; exact w2)
        (by rw [hlen]; exact headInFront_at_head h hG) hc
        (fitsSeg_ok (hL k3 k6 q3 q6) (by rw [nU_at_head h hG]; exact w3) hm)
      have hs' : s ∈ seatsW "U3" := by
        rw [← seats_at_head h hG "U3"]
        exact hs
      have w5 := List.all_eq_true.1 w4 s hs'
      rw [h24] at w5
      simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at w5
      unfold valsHalf
      rw [h24, valsAt_head (spots_at_head h) hb hk cov, hV]
      show (V.front == s.heard && s.array.sizeC == V.n) = true
      rw [hf, hn, hlen, nU_at_head h hG, w5.1, w5.2, beq_self_eq_true, beq_self_eq_true]
      rfl

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.headBits_at_head
#check @OnBytes.HonestTrace.U3.Fit.headRounds_at_head
#check @OnBytes.HonestTrace.U3.Fit.headInFront_at_head
#check @OnBytes.HonestTrace.U3.Fit.entries_at_head
#check @OnBytes.HonestTrace.U3.Fit.nU_at_head
#check @OnBytes.HonestTrace.U3.Fit.headW_yes
#check @OnBytes.HonestTrace.U3.Fit.headW_can_fail
#check @OnBytes.HonestTrace.U3.Fit.valsHalf_head_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.headBits_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.headRounds_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.headInFront_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.entries_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.nU_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.headW_yes
#print axioms OnBytes.HonestTrace.U3.Fit.headW_can_fail
#print axioms OnBytes.HonestTrace.U3.Fit.valsHalf_head_at_head
