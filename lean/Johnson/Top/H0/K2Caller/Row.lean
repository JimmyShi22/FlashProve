-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/Row.lean: the code switch (SEND seed, LOC) at a place's own numbers: one
plain record of numbers, one test on it with code, and: where the test says yes, the caller made of
that record meets the block's condition, and the plan's two rounds at these numbers cover the
block's two errors.

Johnson/G/SwitchKeptLit.lean and Johnson/G/SwitchCovers.lean have this at written lists: for every
list in front, every sending, every pricing group and every group in front out of four written
lists, free of each other. Each of their premises on numbers is one evaluation over these lists,
beneath general theorems. Here the same general theorems are called at ONE record, whose fields
belong together:
  SwRow: set: the setting · cs: the codes · lo: the sampled messages of the group in front, each
      with a radius · g: the group in front, as the planner sizes it (the stage in front is stageOf
      g; the round LOC is priced by g: one letter for both) · rad: the joint radius · l: the sampled
      messages that the switch sends · o: the planner's samples of these, in order · roots: the
      trees of the prover's message · kept: which members of lo are kept whole · rider: the message
      without a sample that is sent with them: the next fold's fresh mask
  SwRow.ok: the test: see its clauses. Five of them are read by no theorem here; they keep records
      out at which the promise would say nothing or speak of another place. The library's test
      allMeet at the list in front, and inJB (Johnson/Top/H/StageJ.lean): the joint radius is below
      the stage's distance and below its Johnson radius: without these two the radii have no
      ceiling, and at a radius as large as the code's length the round LOC's count is 0 and every
      word is within the radius. No place is kept twice. Its last clause but one, rowsOK: the
      group's numbers k, h and slots are those that the programs' rule makes of the members' rows
      and of which are kept: it is there because the plan's round LOC keeps of a group only its
      codes, its rule and m (OnBytes/Params/Planner.lean: pricedOf): without it a record of a stage
      with another number of row variables passes. Its last clause, riderOK: the rider has a fresh
      mask's shape: the block's condition asks nothing of the rider's code
  mem, kp, rowsAt, heldAt, callerOf, callerAt: the members; the kept members; the group's data; the
      choice of kept messages; the caller: switchVec (Johnson/Top/H/SwitchVec.lean) at heldPort
      (Johnson/Top/H/SwitchKept.lean), with as many positions as the planner's baseCount and the
      rider's code portCode cs rider (Johnson/Pack/Port.lean)
  specs r: the plan's two rounds at the record: sendSeed r.set r.o r.roots; locRound r.set .request
      r.g (24 a) 0 a, a := samples * the number of samples
  row_ok: r.ok = true → SendLocRide.OK (callerAt r …)
  row_covers: r.ok = true → round by round, the block's count of bad values over its number of
      values is at most the error that the plan holds for the planned round (Cb.Pv.Covered)
  SwRow.Holds: both, at a record, for all letters
  K02Condition, k02Condition: one closed proposition: Holds at every record at which the test says
      yes; its proof
  K02At, k02At: at a list of records: the test says yes at each, and Holds
SPENT: of the library: OnBytes.Tie.Pv.Switch.sendLoc_covers · Johnson.Pack (allMeet, bMax, bitsZ,
lOf, aOf, cMain, cMask) · OnBytes.Slice.cardE_card_GE ·
Johnson.Top.H.switchKept_ok · switchOf_prices · switchVec_ok_of · switchVec_prices ·
switchVec_fits · Johnson.Pack.eS · eA · member_place.
Limits: the letters that are left: the rows in front of the fold with their forms and coefficients
(B, Sb, sl, Z), the carried joint (Kc, St₀, Wp, E₀, A₀), how the folded word's message and
randomness are read off the new messages (cutN), the witness w₀, the stage's number of draws t₀, the
members' first rows (oM, oZ), and which messages stay open (kq): the statement holds at all of them;
that each can be laid is not shown here. The members are the messages of lo with a main row. The
stage in front, stageOf g, has of the group its two codes and its numbers k and h; it does not read
the number of slots (Johnson/Top/H/StageJ.lean: the stage is the group's only where that number is
1). Here the kept members' rows stand in the kept slots of the group's shape (Rows.keep,
Johnson/Top/H/GroupRowsKept.lean); that this shape has the programs' number of slots is not shown:
the test holds the number against the kept rows alone. The fresh mask of the fold in front, a member
of the programs' group, is in no list here; the fresh mask of the NEXT fold is the block's rider.
The test does not read roots (the two rounds' errors do not depend on it), and of the groups that
price a sample it asks the one inequality alone: that these are the plan's, and that a record is a
plan's, is the matter of Table.lean and of the tests of TestTableSmall.lean and TestTableFull.lean.
That a switch of the programs' protocol is a value of this caller is not said. The prices are those
with the proof of work not counted. One answer a sample. Nothing on soundness: that the two counts
bound a prover's chance is SendLocRide.hAt, under SendLocRide.OK. On hiding nothing.

-/
import Johnson.Top.H.SwitchKept
import Johnson.Top.H.SwitchVec
import Johnson.Pack.SeedDraw
import OnBytes.Tie.Pv.PortKit
import OnBytes.Slice.RecordPriceGlue
import Johnson.Top.H.StageJ
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch

/-- **The numbers of a place of the code switch.** -/
structure SwRow where
  set : Setting
  cs : Codes
  lo : List (OracleShape × ℕ)
  g : GroupSize
  rad : ℕ
  l : List (OracleShape × ℕ)
  o : List SampleSize
  roots : ℕ
  kept : List ℕ
  rider : OracleShape

/-- What the planner has tested of a round, as a test. -/
def goodB (s : Setting) (c : Scope) (x : RoundSpec) : Bool :=
  decide ((x.bound s c).bad = false) && decide (x.work s c < s.target) &&
    decide (x.work s c ≠ 0 → x.work s c + 6 ≤ 8 * s.nonceBytes)

theorem good_of (s : Setting) (c : Scope) (x : RoundSpec) (h : goodB s c x = true) : x.Good s c :=
    by
  unfold goodB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  cases x with
  | said _ _ _ _ _ _ _ => exact ⟨h.1.1, h.1.2, h.2⟩
  | silent _ _ _ => trivial
  | record _ _ _ => trivial

/-- From the form in which sendLoc_covers concludes. -/
theorem covered_of {s : Setting} {xs : List (ℕ × ℕ)} {ys : List RoundSpec}
    (h : List.Forall₂ (fun (x : ℕ × ℕ) (ρ : PlanRound) => (x.1 : ℝ) / (x.2 : ℝ) ≤ ((ρ.error.val : ℚ)
        : ℝ)) xs
      (ys.map fun y => y.round s .request)) : List.Forall₂ (Cb.Pv.Covered s .request) xs ys :=
  (List.forall₂_map_right_iff (f := fun y : RoundSpec => y.round s .request)).1 h

namespace SwRow
variable (r : SwRow)

/-- A member in front stands under the stage's two codes, its tree is no longer than the stage's
positions, and the joint radius implies its own. -/
def memberOK (x : OracleShape × ℕ) : Bool :=
  decide (cMain r.cs x.1 = (stageOf r.g 0).C) && decide (x.1.maskRows ≠ 0 → cMask r.cs x.1 =
      (stageOf r.g 0).Z) &&
    decide (aOf r.cs x.1 ≤ (stageOf r.g 0).C.a) &&
    decide (r.rad ≤ 2 ^ ((stageOf r.g 0).C.a - aOf r.cs x.1) * x.2 + (2 ^ ((stageOf r.g 0).C.a - aOf
        r.cs x.1) - 1))

/-- A sample is the message's: its cube has the message's bits; the library's bound on the message's
list is at most the planner's list size at the sample's groups. -/
def sampleOK (y : (OracleShape × ℕ) × SampleSize) : Bool :=
  decide (y.2.cubeBits = bitsZ r.cs y.1.1) && decide (lOf r.cs y.1.1 y.1.2 ≤ largestList r.set
      y.2.groups)

/-- The main rows of the members that are not kept, each message's rounded up to a power of two (the
programs' rowBlock). -/
def mainBlocks : ℕ := ((r.lo.zipIdx.filter fun x => !r.kept.contains x.2).map fun x => rowBlock
    x.1.1.mainRows).sum

/-- The mask rows of the members, each message's rounded up to a power of two. A message without a
main row is no member: at the first link one such is sent at the start, for no link's group. -/
def maskBlocks : ℕ := ((r.lo.filter fun x => x.1.mainRows != 0).map fun x => rowBlock
    x.1.maskRows).sum

/-- The main rows of the kept members. -/
def keptRows : ℕ := (r.kept.map fun i => ((r.lo[i]?).map fun x => x.1.mainRows).getD 0).sum

/-- The group's three numbers of rows are those that the programs' rule makes of the members' rows
(OnBytes/Iop/Req.lean: reqGroupAt; OnBytes/Plan/PlanListsReq.lean: closedGroup). -/
def rowsOK : Bool :=
  decide (r.g.h = ceilLog2 r.maskBlocks) && decide (r.g.k = max (max (ceilLog2 r.mainBlocks) r.g.h)
      1) &&
    decide (r.g.slots = 2 ^ clog2 (1 + r.keptRows))

/-- The rider is a fresh mask of a fold: mask rows alone, a power of two of them, under the stage's
mask code, and no sample (OnBytes/Iop/Fold.lean: foldMaskNotice). -/
def riderOK : Bool :=
  decide (r.rider.mainRows = 0) && decide (r.rider.answers = 0) && decide (r.rider.maskRows = 2 ^
      ceilLog2 r.rider.maskRows) &&
    decide (cMask r.cs r.rider = (stageOf r.g 0).Z)

/-- **The test.** -/
def ok : Bool :=
  allMeet r.cs r.l && allMeet r.cs r.lo && inJB (stageOf r.g 0) r.rad &&
  (r.lo.all fun x => decide (x.1.mainRows = 0) || r.memberOK x) &&
  decide (r.set.p = Fmt.Fld.two.p) && decide (r.set.degree = 3) && decide (r.set.samples = 1) &&
  decide (r.o.length = r.l.length) && ((r.l.zip r.o).all r.sampleOK) &&
  decide (r.g.rule = .johnson) && decide ((analysisOfM r.set r.g).mainAt.source = .johnson) &&
  decide ((analysisOfM r.set r.g).mainAt.count.bad = false) && upperRadiusTest r.set r.g r.rad &&
  decide (r.l ≠ []) && decide (largestCube r.o = bMax r.cs r.l) &&
  goodB r.set .request (sendSeed r.set r.o 0) && goodB r.set .request (locRound r.set .request r.g 0
      0 0) &&
  (r.kept.all fun i => decide (((r.lo[i]?).map fun x => decide (x.1.mainRows ≠ 0) && decide
      (x.1.maskRows = 0)) = some true)) &&
  decide r.kept.Nodup && r.rowsOK && r.riderOK

/-- The plan's two rounds at the record. -/
def specs : List RoundSpec :=
  [sendSeed r.set r.o r.roots,
    locRound r.set .request r.g (24 * (r.set.samples * r.o.length)) 0 (r.set.samples * r.o.length)]

/-- What the test's yes says, clause by clause. -/
structure OK : Prop where
  meets : allMeet r.cs r.l = true
  front : allMeet r.cs r.lo = true
  john : inJB (stageOf r.g 0) r.rad = true
  member : ∀ x ∈ r.lo, x.1.mainRows ≠ 0 → r.memberOK x = true
  p : r.set.p = Fmt.Fld.two.p
  degree : r.set.degree = 3
  samples : r.set.samples = 1
  len : r.o.length = r.l.length
  sample : ∀ y ∈ r.l.zip r.o, r.sampleOK y = true
  rule : r.g.rule = .johnson
  source : (analysisOfM r.set r.g).mainAt.source = .johnson
  counted : (analysisOfM r.set r.g).mainAt.count.bad = false
  radius : upperRadiusTest r.set r.g r.rad = true
  ne : r.l ≠ []
  cube : largestCube r.o = bMax r.cs r.l
  good1 : goodB r.set .request (sendSeed r.set r.o 0) = true
  good2 : goodB r.set .request (locRound r.set .request r.g 0 0 0) = true
  kept : ∀ i ∈ r.kept, ((r.lo[i]?).map fun x => decide (x.1.mainRows ≠ 0) && decide (x.1.maskRows =
      0)) = some true
  nodup : r.kept.Nodup
  rows : r.rowsOK = true
  rider : r.riderOK = true

theorem ok_says (h : r.ok = true) : r.OK := by
  unfold ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, f1⟩, f2⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
      h13⟩, h14⟩, h15⟩, h16⟩, f3⟩, h17⟩, h18⟩ := h
  exact ⟨h1, f1, f2, fun x hx hm => (h2 x hx).resolve_left hm, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, f3, h17, h18⟩

/-- The members in front: the messages with a main row. -/
def mem (i : Fin r.lo.length) : Prop := (r.lo.get i).1.mainRows ≠ 0

instance : DecidablePred r.mem := fun i => inferInstanceAs (Decidable ((r.lo.get i).1.mainRows ≠ 0))

/-- The kept members. -/
def kp (a : {i // r.mem i}) : Prop := a.1.val ∈ r.kept

instance : DecidablePred r.kp := fun a => inferInstanceAs (Decidable (a.1.val ∈ r.kept))

variable {r}

theorem OK.mem_at (H : r.OK) (i : Fin r.lo.length) (k : r.mem i) : r.memberOK (r.lo.get i) = true :=
  H.member _ (List.get_mem r.lo i) k

theorem OK.hM (H : r.OK) (t₀ : ℕ) : ∀ i, r.mem i → (r.lo.get i).1.mainRows ≠ 0 → cMain r.cs
    (r.lo.get i).1 = (stageOf r.g t₀).C :=
  fun i k _ => by
    have h := H.mem_at i k
    unfold memberOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1

theorem OK.hZ (H : r.OK) (t₀ : ℕ) : ∀ i, r.mem i → (r.lo.get i).1.maskRows ≠ 0 → cMask r.cs
    (r.lo.get i).1 = (stageOf r.g t₀).Z :=
  fun i k => by
    have h := H.mem_at i k
    unfold memberOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2

theorem OK.hA (H : r.OK) (t₀ : ℕ) : ∀ i, r.mem i → aOf r.cs (r.lo.get i).1 ≤ (stageOf r.g t₀).C.a :=
  fun i k => by
    have h := H.mem_at i k
    unfold memberOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2

theorem OK.he (H : r.OK) (t₀ : ℕ) : ∀ i, r.mem i → r.rad ≤ 2 ^ ((stageOf r.g t₀).C.a - aOf r.cs
    (r.lo.get i).1) * (r.lo.get i).2 +
    (2 ^ ((stageOf r.g t₀).C.a - aOf r.cs (r.lo.get i).1) - 1) :=
  fun i k => by
    have h := H.mem_at i k
    unfold memberOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

theorem OK.h0 (H : r.OK) : ∀ a, r.kp a → (r.lo.get a.1).1.maskRows = 0 := fun a k => by
  have h := H.kept a.1.val k
  rw [List.getElem?_eq_getElem a.1.isLt] at h
  simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

end SwRow

open SwRow

section Caller
variable (r : SwRow) (H : r.OK) (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ) (kq : Fin r.lo.length → Prop)

/-- The group's data in front: the members at the stage of the group's sizes. -/
noncomputable abbrev rowsAt : Rows (sigOf r.cs r.lo) :=
  rowsPort r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀)

/-- The choice of kept messages. -/
noncomputable abbrev heldAt : GHeld ((rowsAt r H t₀ oM oZ).keep r.kp).Sh kq :=
  heldPort r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (fun a _ => a.2)
      H.h0 kq

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsAt r H t₀ oM oZ).G.C.J) (Z : Evader GE ((rowsAt r H t₀ oM oZ).G.Row
      B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf r.cs r.lo).sub kq).Msg × Wp))
  (cutN : (sigOf r.cs r.l).Msg → ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).Cf.N.Wit)
  (w₀ : ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).tgt.W)

/-- The caller beneath: the claim on the folded word stated by a state of the fold's output form. -/
noncomputable abbrev callerOf : Cb.Pv.SendLocRide.Size GE :=
  switchOf (heldAt r H t₀ oM oZ kq) Sb sl Z A₀ r.cs r.l cutN (baseCount r.set .request r.g) w₀
      (portCode r.cs r.rider)

/-- **The caller at the record**: the claim stated by its vector. -/
noncomputable abbrev callerAt : Cb.Pv.SendLocRide.Size GE :=
  switchVec (heldAt r H t₀ oM oZ kq) Sb sl Z A₀ r.cs r.l cutN (baseCount r.set .request r.g) w₀
      (portCode r.cs r.rider)

/-- The enumeration of the sent messages by the places of the samples. -/
def idxAt : Fin r.l.length ≃ Fin r.o.length := finCongr H.len.symm

theorem sample_at (i : Fin r.l.length) : r.sampleOK (r.l.get i, r.o.get (idxAt r H i)) = true := by
  refine H.sample _ ?_
  have hi : i.val < (r.l.zip r.o).length := by
    rw [List.length_zip, H.len, Nat.min_self]
    exact i.isLt
  have e : (r.l.zip r.o)[i.val]'hi = (r.l.get i, r.o.get (idxAt r H i)) := by
    rw [List.getElem_zip]
    rfl
  rw [← e]
  exact List.getElem_mem hi

/-- The block's condition, beneath. -/
theorem callerOf_ok : Cb.Pv.SendLocRide.OK (callerOf r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀) :=
  switchKept_ok r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (fun a _ =>
      a.2) H.h0 kq Sb sl Z A₀ r.cs r.l
    cutN _ w₀ (portCode r.cs r.rider) H.meets (H.hA t₀) (H.he t₀)

/-- The conditions on the prices, beneath. -/
theorem callerOf_prices :
    SendLocPrices (callerOf r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀) r.set r.o r.g (idxAt r H) :=
  switchOf_prices (heldAt r H t₀ oM oZ kq) Sb sl Z A₀ r.cs r.l cutN _ w₀ (portCode r.cs r.rider)
      r.set r.o r.g (idxAt r H)
    (OnBytes.Slice.cardE_card_GE r.set H.p H.degree) H.samples
    (fun i => by
      have h := sample_at r H i
      unfold sampleOK at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1)
    (fun i => by
      have h := sample_at r H i
      unfold sampleOK at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2)
    H.rule H.source H.counted H.radius

/-- The conditions on the shape, beneath. -/
theorem callerOf_fits :
    SendLocFits (callerOf r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀) r.set.samples (largestCube r.o)
        (r.set.samples * r.o.length)
      (baseCount r.set .request r.g) r.g.main.logN := by
  rw [H.cube, H.samples, Nat.one_mul, H.len]
  exact ⟨⟨eS r.cs r.l⟩, (member_place r.cs r.l H.ne).map Sum.inr, ⟨eA r.cs r.l⟩, rfl, ⟨Equiv.refl
      _⟩⟩

/-- **The block's condition holds at the caller.** -/
theorem row_ok : Cb.Pv.SendLocRide.OK (callerAt r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀) :=
  switchVec_ok_of _ _ _ _ _ _ _ _ _ _ _ (callerOf_ok r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀)

/-- **The plan's two rounds cover the block's two errors**, round by round. -/
theorem row_covers :
    List.Forall₂ (Cb.Pv.Covered r.set .request)
      ((Err.toList (Cb.Pv.SendLocRide.eps (callerAt r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀))).zip
        (Shape.chalList (Cb.Pv.SendLocRide.R (callerAt r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀)).shape))
      r.specs :=
  covered_of <|
    sendLoc_covers (switchVec_prices _ _ _ _ _ _ _ _ _ _ _ (callerOf_prices r H t₀ oM oZ kq Sb sl Z
        A₀ cutN w₀)) .request r.roots
      (switchVec_fits _ _ _ _ _ _ _ _ _ _ _ (callerOf_fits r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀)) _ _
          _
      (good_of _ _ _ H.good1) (good_of _ _ _ H.good2)

end Caller

/-- **What is promised at a record at which the test has said yes**, for all letters: the block's
condition at the caller made of the record, and the plan's two rounds cover the block's two errors.
-/
def SwRow.Holds (r : SwRow) (H : r.OK) : Prop :=
  ∀ (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ) (kq : Fin r.lo.length → Prop) (_ : DecidablePred kq)
    (B Kc St₀ Wp : Type) (_ : Fintype B) (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) (rowsAt r H t₀ oM oZ).G.C.J) (Z : Evader GE ((rowsAt r H t₀ oM
        oZ).G.Row B))
    (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ (((sigOf r.cs r.lo).sub kq).Msg × Wp))
    (cutN : (sigOf r.cs r.l).Msg → ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).Cf.N.Wit)
    (w₀ : ((heldAt r H t₀ oM oZ kq).foldD Sb sl Z A₀).tgt.W),
    Cb.Pv.SendLocRide.OK (callerAt r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀) ∧
      List.Forall₂ (Cb.Pv.Covered r.set .request)
        ((Err.toList (Cb.Pv.SendLocRide.eps (callerAt r H t₀ oM oZ kq Sb sl Z A₀ cutN w₀))).zip
          (Shape.chalList (Cb.Pv.SendLocRide.R (callerAt r H t₀ oM oZ kq Sb sl Z A₀ cutN
              w₀)).shape))
        r.specs

/-- **The row, as one closed proposition**: at every record at which the test says yes. -/
def K02Condition : Prop := ∀ (r : SwRow) (h : r.ok = true), r.Holds (r.ok_says h)

theorem k02Condition : K02Condition := fun r h t₀ oM oZ kq _ _ _ _ _ _ Sb sl Z _ A₀ cutN w₀ =>
  ⟨row_ok r (r.ok_says h) t₀ oM oZ kq Sb sl Z A₀ cutN w₀, row_covers r (r.ok_says h) t₀ oM oZ kq Sb
      sl Z A₀ cutN w₀⟩

/-- **The same at a list of records**: at each the test says yes, and the promise holds. -/
def K02At (T : List SwRow) : Prop := ∀ r ∈ T, ∃ h : r.ok = true, r.Holds (r.ok_says h)

theorem k02At (T : List SwRow) (hT : (T.all fun r => r.ok) = true) : K02At T := fun r hr =>
  have h : r.ok = true := List.all_eq_true.1 hT r hr
  ⟨h, k02Condition r h⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.row_ok
#print axioms VerifiableInference.Desc.First.K2Caller.row_covers
#print axioms VerifiableInference.Desc.First.K2Caller.k02Condition
#print axioms VerifiableInference.Desc.First.K2Caller.k02At
