-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AttValsAtHead: conditional: under the library's head the maker of the values of the vector of reads "U3" at an
attention segment ("attVals", Johnson/HonestTrace/U3Rows.lean) returns at each of the twelve groups, at the written
places. Its number of reads is the number of columns of the written layout's array; its rounds end where the written
row of the segment's own rounds ends. Public data alone.
A SegVals is carried whole; its field vec, a function that awaits the trace's cells, is applied nowhere here.
The full size and the format's second hash function alone.
The head is the one hypothesis "P5J.AtMgA" that ties the library's letters to the proof file's description.

"attVals" asks thirteen things of public data before it returns (each search for a place counted as one, though it
can reject under three names). Each, with what gives it here:
  the group's attention has a plan                       k5_member
  the segment has places of the kinds K5 and K3, each with a first step that the table of steps knows
                                                         attPlacesW_yes [kernel], under cuts_at_head
  the declared rounds from K5's place on are the entries of attention's own table of rounds
                                                         k5_member (the member's rounds) and slice_at_head
  the reader of attention's challenges counts as many rounds as that table has
                                                         cut_sum: general, no premise
  the two clauses of "fitsSeg" on the lookup's rounds    lookFits_att
  the plan's number of reads is not 0                    u3_array_att and attColsW_yes [kernel]
  the five clauses of "fitsSeg" on the matrices          fitsMats_at_head; the plan's list "Plan.mats" is by its text
                                                         the list of the plan's smallness test, and that is the
                                                         segment's (tlOf_odd)

  u3AttPar, u3AttEntries   what "attVals" hands to the kind's table of rounds, and the table's entries
  rounds_of_own       general: the kind's table of rounds reads of its public numbers the planner's record and the
                      policy's work alone
  attVals_returns     general: the maker returns where its steps do; its n and front are said
  tlOf_odd            under the plans' marks the structure at an odd segment is the group's attention plan's
  attPlacesW [a test], attPlacesW_yes [kernel], attPlacesW_can_fail [kernel; a control]
  attColsW [a test], attColsW_yes [kernel], attColsW_can_fail [kernel; a control]
  attDeclared_at_head the two places, the plan, the declared rounds
  nW_at_head          the plan's number of reads is the number of columns of the written layout's array
  attVals_at_head     the return, with its n and its front
  att_returns_at_head, att_returns_at_open   the return alone: at a blank ground; at an opening's ground

It stands over six files under Johnson/HonestTrace/U3Fit/ (SeatsAtHead, ValsGeneral, MatsAtHead, Slice, LayersLaid,
LookFits): it is worth what they are worth.
A raised limit: «set_option maxRecDepth 1000000» stands at the four closed facts: it bears on the elaborator's
depth of recursion, not on the kernel's verdict.
Not empty: the head has a member at the stored full-size files (AtFullSide.Top.headMember_zFull, in a side library;
its own Limits say what it is worth). Under the head there is an opening O (the head's field laid.opened), and with
it the ground: G is whatever "blankBy" returns at Zp, and under O that is Bs.G₀ (IM.Open.blank).
What it is not. Nothing on the vector's entries: the field "vec" of what is returned may still reject at every list
of challenges. Nothing on "ready", on "u3AllFit", on a seat. No property of the protocol is claimed: nothing on
soundness, completeness or what anything reveals.
Limits. The four closed facts are evaluations in Lean's kernel at written values. The head is a premise.
-/
import Johnson.HonestTrace.U3Fit.LookFits
import Johnson.HonestTrace.U3Fit.LayersLaid
import Johnson.Desc.ProofFile.Honest.K5.Law.Member
import Johnson.Desc.ProofFile.Honest.K5.Law.Shapes
import Johnson.Desc.First.Att.Door.Law.K5U3Cols
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Att

open OnBytes OnBytes.Model
open OnBytes.HonestTrace.U3.Fit
open ProofFile (Pub Ground Spot)
open ProofFile.Honest.K3 (tlOf linkH stepOf)
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.G (layoutFull)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

local notation "ParP" => VerifiableInference.Desc.First.Att.P.Par
local notation "roundsP" => VerifiableInference.Desc.First.Att.P.rounds

/-! ## 1 General: no head, no size -/

/-- The public numbers that "attVals" hands to the kind's table of rounds. pc: the number of the kind's
sub-protocol inside the segment. -/
def u3AttPar (G : Ground) (seg pc : Nat) (A : Attention.Plan) : ParP :=
  { link := seg, piece := pc, own := A.own, before := []
    work := (OnBytes.Params.settingOf G.W.P.frame).workOf .field .request }

/-- The entries of attention's own table of rounds, as "attVals" makes them. -/
def u3AttEntries (G : Ground) (seg pc : Nat) (A : Attention.Plan) : List Fmt.Entry :=
  (roundsP (u3AttPar G seg pc A)).map (·.entry)

/-- **General: the kind's table of rounds reads of its public numbers the planner's record and the policy's work
alone.** -/
theorem rounds_of_own {p q : ParP} (ho : p.own = q.own) (hw : p.work = q.work) :
    roundsP p = roundsP q := by
  unfold VerifiableInference.Desc.First.Att.P.rounds
  rw [ho, hw]

/-- **General: attention's maker returns where its steps do.** That the reader of the challenges counts the table's
rounds is no premise: it holds at every plan. -/
theorem attVals_returns {Z : Pub} {G : Ground} {sps : List Spot} {seg g : Nat}
    {A : Attention.Plan} {k5 k3 : Spot × Nat}
    (e : G.W.A[g]? = some A) (p5 : placeIn Z sps seg .K5 = .ok k5)
    (p3 : placeIn Z sps seg .K3 = .ok k3)
    (hd : declared Z k5.2 (u3AttEntries G seg k5.1.place.piece A).length =
      u3AttEntries G seg k5.1.place.piece A)
    (hf : fitsSeg Z G seg A.fs k3.2 k5.2 A.nW A.mats = .ok ()) :
    ∃ V, attVals Z G sps seg g = .ok V ∧ V.n = A.nW ∧
      V.front = k5.2 + (u3AttEntries G seg k5.1.place.piece A).length := by
  have hc : (H2K5.Honest.cut A.own).sum = (u3AttEntries G seg k5.1.place.piece A).length := by
    unfold u3AttEntries
    rw [List.length_map]
    exact ProofFile.Honest.K5.cut_sum (u3AttPar G seg k5.1.place.piece A)
  unfold u3AttEntries u3AttPar at hd hc ⊢
  unfold attVals
  rw [e, p5, p3]
  simp only [have_, bind, Except.bind, ask, hd, hc, hf, beq_self_eq_true, if_true, pure,
    Except.pure]
  exact ⟨_, rfl, rfl, rfl⟩

/-- Under the marks the structure at an odd segment is the group's attention plan's. -/
theorem tlOf_odd {X : Verify.Public} (M : PlanMarks X) {g : Nat} {a : Attention.Plan}
    (e : X.A[g]? = some a) : tlOf X (2 * g + 1) = a.seam.tl := by
  have e1 : stepOf X = 2 := by
    unfold stepOf
    rw [M.p4]
    rfl
  have e2 : linkH X = 24 := by
    unfold linkH
    rw [e1, M.groups]
  have a1 : (2 * g + 1 == 24) = false := by
    have : 2 * g + 1 ≠ 24 := by omega
    simpa using this
  have b : ((2 * g + 1) % 2 == 0) = false := by
    have : (2 * g + 1) % 2 = 1 := by omega
    rw [this]
    rfl
  have c : (2 * g + 1) / 2 = g := by omega
  unfold tlOf
  rw [e1, e2, a1, b, c, e]
  rfl

/-! ## 2 Two tests at written values -/

/-- **A test at written values.** At the twelve odd segments "placeBy" finds the places of the kinds K5 and K3, and
the table of steps counts in front of them what the written rows count in front of rows 14 (2 g + 1) + 4 and
14 (2 g + 1) + 3. off: a shift of the rows, for the control. -/
def attPlacesW (off : Nat) : Bool :=
  (List.range 12).all fun g =>
    match placeBy cutWritten spotsWritten (2 * g + 1) .K5,
      placeBy cutWritten spotsWritten (2 * g + 1) .K3 with
    | .ok k5, .ok k3 =>
      k5.2 == rowsBeforeW (14 * (2 * g + 1) + 4 + off) &&
        k3.2 == rowsBeforeW (14 * (2 * g + 1) + 3 + off)
    | _, _ => false

set_option maxRecDepth 1000000 in
theorem attPlacesW_yes : attPlacesW 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: against the rows one further on the test says no. -/
theorem attPlacesW_can_fail : attPlacesW 1 = false := by decide +kernel

/-- **A test at written values.** cols: the number of columns of the array "U3" at a segment: it is not 0 at the
twelve odd segments. -/
def attColsW (cols : Nat → Nat) : Bool := (List.range 12).all fun g => cols (2 * g + 1) != 0

set_option maxRecDepth 1000000 in
theorem attColsW_yes : attColsW colsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: two segments further on eleven of the twelve still have their array; the last, number 25, has none:
the test says no. -/
theorem attColsW_can_fail : attColsW (fun k => colsW (k + 2)) = false := by decide +kernel

/-! ## 3 Under the head -/

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **Under the head, at each group: the two places, the plan, and «the declared rounds are the entries of
attention's own table of rounds».** -/
theorem attDeclared_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12) :
    ∃ (k5 k3 : Spot × Nat) (a : Attention.Plan),
      placeIn Zp spotsWritten (2 * g + 1) .K5 = .ok k5 ∧
      placeIn Zp spotsWritten (2 * g + 1) .K3 = .ok k3 ∧
      k5.2 = rowsBeforeW (14 * (2 * g + 1) + 4) ∧ k3.2 = rowsBeforeW (14 * (2 * g + 1) + 3) ∧
      G.W.A[g]? = some a ∧
      declared Zp k5.2 (u3AttEntries G (2 * g + 1) k5.1.place.piece a).length =
        u3AttEntries G (2 * g + 1) k5.1.place.piece a ∧
      (cutFirstFull[14 * (2 * g + 1) + 4]?).map (·.2.2.1) =
        some (u3AttEntries G (2 * g + 1) k5.1.place.piece a).length := by
  obtain ⟨blk, a, hb0, Pl, Dc⟩ := ProofFile.Honest.K5.k5_member h hg
  have hb : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some blk := hb0
  obtain ⟨_, -, eW0, -, -⟩ := IM.blank_ground hG
  have eW : G.W = P5J.At.X Zp := eW0
  have ea : G.W.A[g]? = some a := by
    rw [eW]
    exact Pl.plan
  have w := List.all_eq_true.1 attPlacesW_yes g (List.mem_range.2 hg)
  have q5 := placeIn_by Zp spotsWritten (2 * g + 1) .K5
  have q3 := placeIn_by Zp spotsWritten (2 * g + 1) .K3
  rw [cuts_at_head h] at q5 q3
  cases e5 : placeBy cutWritten spotsWritten (2 * g + 1) .K5 with
  | error e =>
    rw [e5] at w
    cases w
  | ok k5 =>
    cases e3 : placeBy cutWritten spotsWritten (2 * g + 1) .K3 with
    | error e =>
      rw [e5, e3] at w
      cases w
    | ok k3 =>
      rw [e5, e3] at w
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.add_zero] at w
      rw [e5] at q5
      rw [e3] at q3
      have er : blk.rounds = roundsP (u3AttPar G (2 * g + 1) k5.1.place.piece a) :=
        Dc.rounds.trans (rounds_of_own rfl
          (congrArg (fun X : Verify.Public =>
            (OnBytes.Params.settingOf X.P.frame).workOf .field .request) eW.symm))
      have el : blk.rounds.length = (u3AttEntries G (2 * g + 1) k5.1.place.piece a).length := by
        rw [er]
        exact (List.length_map _).symm
      have s := slice_at_head h hb
      refine ⟨k5, k3, a, q5, q3, w.1, w.2, ea, ?_, ?_⟩
      · rw [w.1, ← el, s]
        exact congrArg (List.map Fmt.DeclaredRound.entry) er
      · rw [← el]
        exact len_at_head h hb

/-- **Under the head the plan's number of reads is the number of columns of the written layout's array.** -/
theorem nW_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12)
    {a : Attention.Plan} (ea : G.W.A[g]? = some a) : a.nW = colsW (2 * g + 1) := by
  have hX := IM.ground_publicK h.laid.pub hG
  have M := marks_at_head h hG
  obtain ⟨_, -, eW, -, eF⟩ := IM.blank_ground hG
  obtain ⟨hp, _, _, _, e, -⟩ := (IM.ground_tails h.scope h.reads h.laid.pub hG).1 g hg
  have eL : Zp.first.layout = layoutFull := by
    rw [← eF]
    exact (first_at_head h hG).2.2
  rw [eW] at e ea
  obtain ⟨A, a1, -, a3⟩ := H2K5.Door.u3_array_att (by rw [← eW]; exact hX) h.laid.pub
    (by rw [← eW]; exact M.p4) e ea
  have eC : A.sizeC = colsW (2 * g + 1) := by
    unfold colsW
    rw [← eL, a1]
    rfl
  exact a3.symm.trans eC

/-- **Under the head attention's maker returns at group g**, with its number of reads and the round at which its own
rounds end. -/
theorem attVals_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12) :
    ∃ V, attVals Zp G spotsWritten (2 * g + 1) g = .ok V ∧ V.n = colsW (2 * g + 1) ∧
      (cutFirstFull[14 * (2 * g + 1) + 4]?).map
          (fun c => rowsBeforeW (14 * (2 * g + 1) + 4) + c.2.2.1) = some V.front := by
  obtain ⟨k5, k3, a, q5, q3, w5, -, ea, hd, hlen⟩ := attDeclared_at_head h hG hg
  have en := nW_at_head h hG hg ea
  have hn0 : a.nW ≠ 0 := by
    rw [en]
    exact bne_iff_ne.1 (List.all_eq_true.1 attColsW_yes g (List.mem_range.2 hg))
  have hm : fitsMats G.W (2 * g + 1) a.mats = true := by
    have k := fitsMats_at_head h hG (seg := 2 * g + 1) (by omega)
    rw [tlOf_odd (marks_at_head h hG) ea] at k
    exact k
  obtain ⟨V, hV, e1, e2⟩ := attVals_returns ea q5 q3 hd
    (fitsSeg_ok (lookFits_att h hG hg ea k3 k5 q3 q5) hn0 hm)
  refine ⟨V, hV, e1.trans en, ?_⟩
  rw [e2, w5]
  cases hc : cutFirstFull[14 * (2 * g + 1) + 4]? with
  | none =>
    rw [hc] at hlen
    cases hlen
  | some c =>
    rw [hc] at hlen
    have : c.2.2.1 = (u3AttEntries G (2 * g + 1) k5.1.place.piece a).length :=
      Option.some.inj hlen
    show some (rowsBeforeW (14 * (2 * g + 1) + 4) + c.2.2.1) = _
    rw [this]

/-- **Under the head attention's maker returns at the twelve odd segments**, at a blank ground. -/
theorem att_returns_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    ∀ g < 12, ∃ V, attVals Zp G spotsWritten (2 * g + 1) g = .ok V := by
  intro g hg
  obtain ⟨V, hV, -⟩ := attVals_at_head h hG hg
  exact ⟨V, hV⟩

/-- **The same at an opening's ground.** -/
theorem att_returns_at_open (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ g < 12, ∃ V, attVals Zp Bs.G₀ spotsWritten (2 * g + 1) g = .ok V :=
  att_returns_at_head h O.blank

end OnBytes.HonestTrace.U3.Att

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Att.rounds_of_own
#check @OnBytes.HonestTrace.U3.Att.attVals_returns
#check @OnBytes.HonestTrace.U3.Att.tlOf_odd
#check @OnBytes.HonestTrace.U3.Att.attPlacesW_yes
#check @OnBytes.HonestTrace.U3.Att.attPlacesW_can_fail
#check @OnBytes.HonestTrace.U3.Att.attColsW_yes
#check @OnBytes.HonestTrace.U3.Att.attColsW_can_fail
#check @OnBytes.HonestTrace.U3.Att.attDeclared_at_head
#check @OnBytes.HonestTrace.U3.Att.nW_at_head
#check @OnBytes.HonestTrace.U3.Att.attVals_at_head
#check @OnBytes.HonestTrace.U3.Att.att_returns_at_head
#check @OnBytes.HonestTrace.U3.Att.att_returns_at_open
#print axioms OnBytes.HonestTrace.U3.Att.rounds_of_own
#print axioms OnBytes.HonestTrace.U3.Att.attVals_returns
#print axioms OnBytes.HonestTrace.U3.Att.tlOf_odd
#print axioms OnBytes.HonestTrace.U3.Att.attPlacesW_yes
#print axioms OnBytes.HonestTrace.U3.Att.attPlacesW_can_fail
#print axioms OnBytes.HonestTrace.U3.Att.attColsW_yes
#print axioms OnBytes.HonestTrace.U3.Att.attColsW_can_fail
#print axioms OnBytes.HonestTrace.U3.Att.attDeclared_at_head
#print axioms OnBytes.HonestTrace.U3.Att.nW_at_head
#print axioms OnBytes.HonestTrace.U3.Att.attVals_at_head
#print axioms OnBytes.HonestTrace.U3.Att.att_returns_at_head
#print axioms OnBytes.HonestTrace.U3.Att.att_returns_at_open
#print axioms OnBytes.HonestTrace.U3.Att.u3AttPar
#print axioms OnBytes.HonestTrace.U3.Att.u3AttEntries
#print axioms OnBytes.HonestTrace.U3.Att.attPlacesW
#print axioms OnBytes.HonestTrace.U3.Att.attColsW
