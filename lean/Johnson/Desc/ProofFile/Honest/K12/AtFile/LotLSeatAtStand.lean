-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLSeatAtStand.lean

It states no goal. No property of the protocol is claimed.

At a stand of the library's own thread
in front of the first chain's closing proximity test (member 354), each member of the group under test
sits at the seat of the carrying message of the code switch's finish: the public clauses of `SeatAtL`
(not beneath this file) and the premise hcs of `wordsTied_L`, at the finish's own place.

  `finishShapeWritten`, `finishShapeWritten_no`   the closed line at the written finish, and its control
  `finishAtHead`             under the head, at the blank ground: the finish's carrying message has
                             the written shape, and the finish's codes are the written ones
  `ClosingMemberSeat`        what a member of the group is, but for the script's clause
  `closingMemberSeat_at_reach`   at a reached state at which `membersHeld` says yes
  `closingMemberSeat_at_stand`   at a stand of the thread

By what. `closingMemberAtReach` (LotLSeatMember.lean); `places_head`, `finishW`
(AtFullSide/K12/FitsAtHeadL.lean); `find_of_mem` (Johnson/Desc/Means/Layout.lean); `four_at_finish`
(K12/AtProof/FieldsAtFinish.lean); the promise's clause `membersHeld`, read off `Thr`'s form as
`says_head_L` does (ClosingSaysAt.lean).

Hypotheses of `closingMemberSeat_at_stand`. hT: the stand. hr, he: the state is reached and the way in
returns R. hG: the group under test is G. hGd: Gd is the blank ground. hpl: pl is the finish there.

Limits.
- The full size alone, the format's second hash function alone.
- The script's clause (what the witness's message and pad are at tree 76, tenant 0) is not here.
- That a blank ground is there, and that the job's place is this finish, are not shown here
  (`L_found`, AtFullSide/K12/LettersFoundL.lean, names the same finish).
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `closingMemberSeat_at_stand` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- h, hr, he, hG, hGd and hpl speak of the public files, of a reach of the verifier's state, of the
  way in, of a group of the record, of the ground and of the finish: they name no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- There k, s, m and E are the theorem's own binders. The letters s, m and E (the verifier's state,
  the state of the prover's side, the available tables) stand under hT : `Thr … 354 k s m E`: a
  premise of the first kind: it names k; by its text, at fixed s, m and E it can hold at some values
  of the coins and fail at others.
- One clause of the invariant says that the input of m is w and meets Vd, a letter for a predicate
  on the input: what it reads of the input is not fixed here.
- The thread's other letters (H, Q, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp) stand under no
  premise in front that names a coin; the invariant reads them.
- `closingMemberSeat_at_reach`, `finishAtHead` and the closed lines name no coin: they bear none.
- What lifts the bar: for s, m and E the made terms would be those of the honest run at the border,
  as terms of w, k and the challenges, and the lemma would show the premises at them at every value
  of the coins. None is known to this file: the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatMember
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingSaysAt
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.LotL
open OnBytes (Group GroupLayout Statement TreeBook)
open OnBytes.Means (layoutOf)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S membersHeld)
open VerifiableInference.Desc.Sound (MsgT below seatBy noFirst)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K12.AtProof (finishAt finishW shapeL freshShapeL places_head four_at_finish)
open P5J (AtMgA CellsM TS)
open Johnson.G (codesFull2)

/-! ## 1 The finish's place -/

set_option maxRecDepth 1000000 in
/-- **The closed line**: at the written finish the carrying message has the written shape, and the
codes are the written ones. -/
theorem finishShapeWritten :
    finishW.all (fun pl => shapeL pl == H2K12.shL && pl.sizes.codes == codesFull2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: the finish's other message, the fresh table, has another shape. Alone this "false"
could not come of a lacking finish: `Option.all` says yes at none. -/
theorem finishShapeWritten_no :
    finishW.all (fun pl => freshShapeL pl == H2K12.shL && pl.sizes.codes == codesFull2) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, at the blank ground.** -/
theorem finishAtHead {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D₀ r Zp Np cF) {Gd : ProofFile.Ground}
    (hGd : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Gd) {pl : K2.SwitchPlace}
    (hpl : finishAt Zp Gd = some pl) :
    ((K2.switchSent pl.sizes pl.others).getD 0 default).shape = H2K12.shL ∧
      pl.sizes.codes = codesFull2 := by
  have e : finishAt Zp Gd = finishW := by
    unfold finishAt finishW
    rw [places_head h hGd]
  have hw := finishShapeWritten
  rw [← e, hpl] at hw
  simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq] at hw
  exact hw

/-! ## 2 What a member is -/

/-- **What a member of the group under test is, but for the script's clause**: it is message number
185; it sits at tree 76, tenant 0; it has the shape of the finish's carrying message, of degree 3 and
with no mask row; the group's layout finds it; the statement's codes are the finish's. -/
structure ClosingMemberSeat (pl : K2.SwitchPlace) (St : Statement) (book : TreeBook)
    (Ly : GroupLayout) (o : ℕ) : Prop where
  number : o = 185
  seat : seatBy noFirst book o = some (76, 0)
  message : ∃ x, St.oracles[o]? = some x ∧
    x.shape = ((K2.switchSent pl.sizes pl.others).getD 0 default).shape ∧
    x.shape.mainDeg = 3 ∧ x.shape.maskRows = 0
  found : ∃ m, Ly.find o = some m
  codes : St.codes = pl.sizes.codes

/-- **At a reached state at which the promise's test on the members says yes.** -/
theorem closingMemberSeat_at_reach (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r Zp Np cF) {p : ProofFile.InstPub}
    {s : S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s)) (hfail : s.failed = none)
    (hmem : membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true) {G : Group}
    (hG : s.st.groups[25]? = some G) {Gd : ProofFile.Ground}
    (hGd : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Gd) {pl : K2.SwitchPlace}
    (hpl : finishAt Zp Gd = some pl) :
    G.members.toList = [185] ∧
      ∀ o ∈ G.members.toList, ClosingMemberSeat pl s.st s.book (layoutOf s.st G) o := by
  obtain ⟨hone, hseat, ⟨y, hy, hsh⟩, hcodes⟩ := closingMemberAtReach h hr hfail hmem hG
  obtain ⟨hshape, hcs⟩ := finishAtHead h hGd hpl
  refine ⟨hone, fun o ho => ?_⟩
  have e : o = 185 := by
    rw [hone] at ho
    exact List.mem_singleton.1 ho
  have hf : ∃ m, (layoutOf s.st G).find o = some m :=
    OnBytes.Means.find_of_mem (L := layoutOf s.st G) ho
  subst e
  exact ⟨rfl, hseat, ⟨y, hy, hsh.trans hshape.symm, by rw [hsh]; rfl, by rw [hsh]; rfl⟩, hf,
    hcodes.trans hcs.symm⟩

/-! ## 3 At a stand -/

/-- **At a stand of the thread in front of the test.** -/
theorem closingMemberSeat_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 354 k s m E)
    {p : ProofFile.InstPub} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (p, s)) {R : T12}
    (he : enterFinish s = .ok R) {G : Group} (hG : R.st.groups[R.g]? = some G) {Gd : ProofFile.Ground}
    (hGd : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Gd) {pl : K2.SwitchPlace}
    (hpl : finishAt Zp Gd = some pl) :
    R.st = s.st ∧ R.g = 25 ∧ G.members.toList = [185] ∧
      ∀ o ∈ G.members.toList, ClosingMemberSeat pl s.st s.book (layoutOf s.st G) o := by
  obtain ⟨f, -, -, -, e⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s R he
  have est : R.st = s.st := by rw [e]
  have hg : R.g = 25 := (four_at_finish h.toAtMg hr he).2.2.2
  rw [est, hg] at hG
  have h' := hT
  unfold Thr at h'
  obtain ⟨-, -, hF, -, -, -, -⟩ := h'
  obtain ⟨hf, -, hc⟩ := hF
  have hfail : s.failed = none :=
    Option.isNone_iff_eq_none.1 (show s.failed.isNone = true from hf)
  rcases hc with hc | ⟨hb, -, -, -⟩
  · exact absurd hfail hc
  simp only [Bool.and_eq_true] at hb
  have hmem : membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true := hb.1.1.1.2
  exact ⟨est, hg, closingMemberSeat_at_reach h.toAtMg (reach_raw hr) hfail hmem hG hGd hpl⟩

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.finishShapeWritten
#print axioms ProofFile.Honest.K12.LotL.finishShapeWritten_no
#print axioms ProofFile.Honest.K12.LotL.finishAtHead
#print axioms ProofFile.Honest.K12.LotL.closingMemberSeat_at_reach
#print axioms ProofFile.Honest.K12.LotL.closingMemberSeat_at_stand
