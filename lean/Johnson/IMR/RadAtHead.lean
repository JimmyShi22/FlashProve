-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/RadAtHead.lean: THE TWO TESTS "THE RADIUS FITS" (P2Law.PlanLeft.radB) THAT STAY OF
THE LAST TABLE's FIELD planAt, AT W's MEMBER AND AT THE INDEX MASKS' MEMBER, SAY TRUE UNDER THE ONE
HEAD AND ONE CLOSED Bool ON WRITTEN TERMS (radWB). ITS TOP IS OVERTAKEN: P5J.AtMg.two_radii
(Johnson/P2LawR/TwoRadiiAtHead.lean) has radB_at_head's statement WITHOUT the premise radWB = true.

WHAT IT IS NOT, FIRST. NOT "from the head alone": radWB = true STAYS A PREMISE. radWB is a term
without a free letter: it reads no public file: it is true or false once and for all. It holds
LinkJoin.rowsW (Johnson/LPFE1R/RowsAtWritten.lean), which Lean's
kernel is reported to refuse to reduce. NOT PROVED.

  member_entry      a member of the list by the make has the shape and the seat of an entry with a
                    sample of its sending, and the radius rad k i at that entry's place
  rows_at_head      under the head the second reading of the three public files returns (out of the
                    head's own field plan.radii: at no rows that test is false)
  rad_at_head       ... and where rowsW returns w: At.rad Zp Z.lay = P5T.radOf w (rows_are_W)
  radE · radAtB w t   the radius test at an entry; at every written entry that sits at t, at the
                    written codes, the closed place's first stage and the radii of w
  radE_written · stage_written   closed facts, by the kernel, none touching rowsW: W's shape passes
                    with 3131972 and fails with one less; the index masks' message's with 6117
  entries_written   a closed fact, by the kernel: one written entry alone sits at (82, 0): (81, 0),
                    with W's shape; one alone at (1, 0): (0, 3), with the index masks' message's
  radOfB x · radWB  the two at what a reading x returns (false where it refuses); THE CLOSED Bool
                    radWB := radOfB rowsW: rowsW returns, and radAtB at (82, 0) and at (1, 0)
  **radB_at_head**  the head and radWB = true give radB at whoever of the first table's members sits
                    at W's seat, and at whoever sits at the index masks' seat, at the first of the
                    own test's place's stages

CALLED: LinkJoin.rows_are_W (Johnson/LPFE1R/RowsOneInScope.lean), LinkJoin.pub_files
(Johnson/LPFE1R/RadiiAt.lean), P5J.pins_of_laid, P5J.AtMg.seats | N_six | pins
(Johnson/P5T/CoreAtMg.lean, FenceAtMg.lean), H2K.Sizes.place_W_of_full, IM.pins and p14_codes.
At the second hash function alone. The full size alone. Nothing on what a radius means: numbers are
compared. No member. No soundness.

-/
import Johnson.IMR.SampleAtW
import Johnson.IMR.OneOmegaAtHead
import Johnson.P2LawR.PlanLeftAt
import Johnson.LPFE1R.RowsOneInScope
import Johnson.LPFE1R.RadiiAt
import Johnson.P5T.CoreAtMg
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Seats

open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (Mem seatOf msOf mem_msOf Sending)
open VerifiableInference.Desc.LinkJoin (rowsW rows_are_W pub_files)
open OnBytes.Maker (WholeD)
open H2K.Member (piWFull rWFull)
open H2K.Pub (sgOf)
open H2K.Pin (aOfB)
open P2Law.PlanLeft (radB)
open ToldDesc (p14At)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- A member by the make: its entry and its seat. -/
theorem member_entry (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List P5T.PSeat) (y : Mem)
    (hy : y ∈ msOf (P5T.memberListsR n rad ps)) :
    ∃ k ∈ List.range n, ∃ x ∈ (P5T.mineAt ps k).zipIdx,
      y.1.l.get y.2 = (x.1.shape, rad k x.2) ∧ seatOf y = x.1.seat := by
  obtain ⟨p, hp, e⟩ := mem_msOf _ y hy
  obtain ⟨s, i⟩ := y
  have e' : s = Sending.ofLists p.1 p.2 := e
  subst e'
  unfold P5T.memberListsR at hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
  have hi : i.val < (P5T.mineAt ps k).length := by
    have := i.isLt
    simpa [Sending.ofLists] using this
  refine ⟨k, hk, ((P5T.mineAt ps k)[i.val], i.val), ?_, ?_, ?_⟩
  · rw [List.mem_zipIdx_iff_getElem?]
    simp [hi]
  · simp [Sending.ofLists]
  · simp [seatOf, Sending.ofLists, hi]

set_option maxRecDepth 1000000 in
/-- Closed facts, by the kernel: there is a written sending, and the first has an entry with a
sample. -/
theorem sends_pos : 0 < Johnson.G.proofSendsFull.1.sends.length := by decide +kernel

set_option maxRecDepth 1000000 in
theorem first_has : 0 < (P5T.mineAt P5T.psFull 0).length := by decide +kernel

/-- The own test's place's stages are the closed place's. -/
theorem stages_at_head {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) :
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = piWFull.nums.stages := by
  have hpN : (H2K.JointK.descN o ProofFile.pureRoad.links VerifiableInference.Desc.K12.guardedProximityTestParts Zp Np
      cF).planOk = true := h.laid.planOk
  rw [H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ Np.W
    (H2K.JointK.plan_at_seat_W o Zp ProofFile.pureRoad.links Np cF hpN)]
  exact (H2K.Sizes.place_W_of_full (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub)
    h.laid.places).1

/-- Under the head the second reading of the three public files returns. -/
theorem rows_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R ∧
      (P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD [] = R := by
  obtain ⟨e1, e2⟩ := pub_files h.laid.pub
  have hr := h.plan.radii
  rw [e1, e2] at hr ⊢
  unfold P5T.rowsAt? at hr ⊢
  cases hq : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL with
  | ok R => exact ⟨R, rfl, rfl⟩
  | error w =>
    exfalso
    rw [hq] at hr
    have hs : At.pseats Zp = P5T.psFull := h.seats
    rw [hs, (pins h.pins.1).2.2.2.2] at hr
    have a := List.all_eq_true.1 hr 0 (List.mem_range.2 sends_pos)
    have b := List.all_eq_true.1 a 0 (List.mem_range.2 first_has)
    cases b

/-- Where the closed term returns w, the head's radii are w's. -/
theorem rad_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {w : List Johnson.G.SendRow}
    (K : rowsW = .ok w) : At.rad Zp Z.lay = P5T.radOf w := by
  obtain ⟨R, hR, e⟩ := rows_at_head h
  unfold At.rad
  rw [e, rows_are_W h.scope h.laid.pub (pins_of_laid h.scope h.laid).1 hR K]

/-- The radius test, at an entry. -/
def radE (cs : Codes) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage) (e : OracleShape × ℕ) : Bool :=
  decide (r (sgOf st).st < (e.2 + 1) * 2 ^ ((sgOf st).C.a - aOfB cs e.1))

theorem radB_is (cs : Codes) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage) (x : Mem) :
    radB cs r st x = radE cs r st (x.1.l.get x.2) := rfl

set_option maxRecDepth 1000000 in
/-- Closed facts, by the kernel, none touching rowsW: at the closed place's first stage W's shape
passes with the radius 3131972 and fails with one less; the index masks' message's shape passes
with 6117 and fails with one less. -/
theorem radE_written : ∀ st ∈ piWFull.nums.stages.head?,
    radE zW.codes rWFull st (shW, 3131972) = true ∧ radE zW.codes rWFull st (shW, 3131971) = false ∧
      radE zW.codes rWFull st (shI, 6117) = true ∧ radE zW.codes rWFull st (shI, 6116) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- ... and there is such a stage. -/
theorem stage_written : piWFull.nums.stages.head?.isSome = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A closed fact, by the kernel: of the written entries with a sample one alone sits at (82, 0):
number 0 of sending 81, with W's shape; one alone at (1, 0): number 3 of sending 0, with the index
masks' message's shape. -/
theorem entries_written :
    ((List.range Johnson.G.proofSendsFull.1.sends.length).flatMap fun k =>
      ((P5T.mineAt P5T.psFull k).zipIdx.filter fun x => decide (x.1.seat = (82, 0))).map
        fun x => (k, x.2, x.1.shape)) = [(81, 0, shW)] ∧
    ((List.range Johnson.G.proofSendsFull.1.sends.length).flatMap fun k =>
      ((P5T.mineAt P5T.psFull k).zipIdx.filter fun x => decide (x.1.seat = (1, 0))).map
        fun x => (k, x.2, x.1.shape)) = [(0, 3, shI)] := by
  decide +kernel

/-- At every written entry that sits at t: the radius test, at the radii of w. -/
def radAtB (w : List Johnson.G.SendRow) (t : ℕ × ℕ) : Bool :=
  match piWFull.nums.stages with
  | st :: _ =>
    (List.range Johnson.G.proofSendsFull.1.sends.length).all fun k =>
      (P5T.mineAt P5T.psFull k).zipIdx.all fun x =>
        !decide (x.1.seat = t) || radE zW.codes rWFull st (x.1.shape, P5T.radOf w k x.2)
  | [] => false

/-- The two tests at what a reading returns; false where it refuses. -/
def radOfB (x : Except String (List Johnson.G.SendRow)) : Bool :=
  match x with
  | .ok w => radAtB w (82, 0) && radAtB w (1, 0)
  | .error _ => false

theorem radOfB_ok {x : Except String (List Johnson.G.SendRow)} (K : radOfB x = true) :
    ∃ w, x = .ok w ∧ radAtB w (82, 0) = true ∧ radAtB w (1, 0) = true := by
  cases x with
  | error e => cases K
  | ok w =>
    obtain ⟨k1, k2⟩ := Bool.and_eq_true_iff.1 (show (_ && _) = true from K)
    exact ⟨w, rfl, k1, k2⟩

/-- **THE CLOSED Bool**: a term without a free letter. -/
def radWB : Bool := radOfB rowsW

/-- One seat's share. -/
theorem radB_at_seat (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {w : List Johnson.G.SendRow}
    (K : rowsW = .ok w) {t : ℕ × ℕ} (T : radAtB w t = true) {st : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} (hst : piWFull.nums.stages = st :: rest) :
    (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = t)).all
      fun y => radB (p14At Zp).codes rWFull st y) = true := by
  refine List.all_eq_true.2 fun y hy => ?_
  obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
  obtain ⟨k, hk, x, hx, e, es⟩ := member_entry _ _ _ y hy1
  rw [h.seats] at hx
  rw [(pins h.pins.1).2.2.2.2] at hk
  unfold radAtB at T
  rw [hst] at T
  have a := List.all_eq_true.1 (List.all_eq_true.1 T k hk) x hx
  have hs : x.1.seat = t := es.symm.trans (of_decide_eq_true hy2)
  rw [decide_eq_true hs, Bool.not_true, Bool.false_or] at a
  rw [radB_is, e, p14_codes h.pins.1, rad_at_head h K]
  exact a

/-- **The two radius tests that stay of planAt, from the head and the closed Bool.** -/
theorem radB_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (K : radWB = true) :
    ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = (At.N Zp cF).w)).all
        fun y => radB (p14At Zp).codes rWFull st y) = true ∧
      (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = (At.N Zp cF).index)).all
        fun y => radB (p14At Zp).codes rWFull st y) = true := by
  intro st rest hst
  have hs : piWFull.nums.stages = st :: rest := by
    rw [← hst, stages_at_head h]
  obtain ⟨w, hw, k1, k2⟩ := radOfB_ok K
  rw [h.N_six.2.2.2.1.trans (congrArg Prod.snd P5T.N0Full_seats),
    h.N_six.2.2.1.trans (congrArg Prod.fst P5T.N0Full_seats)]
  exact ⟨radB_at_seat h hw k1 hs, radB_at_seat h hw k2 hs⟩

end IM.Seats

#print axioms IM.Seats.member_entry
#print axioms IM.Seats.sends_pos
#print axioms IM.Seats.first_has
#print axioms IM.Seats.stages_at_head
#print axioms IM.Seats.rows_at_head
#print axioms IM.Seats.rad_at_head
#print axioms IM.Seats.radB_is
#print axioms IM.Seats.radE_written
#print axioms IM.Seats.stage_written
#print axioms IM.Seats.entries_written
#print axioms IM.Seats.radOfB_ok
#print axioms IM.Seats.radB_at_seat
#print axioms IM.Seats.radB_at_head
