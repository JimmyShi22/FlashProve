-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/GuardsAtHead.lean: kind K13, the members' batching: THE PREMISE
"FROM THE THREAD IN FRONT TO THE NINE GUARDS" (`K13Guards`, Debts.lean of this folder) SHOWN, AS FAR
AS IT CAN BE, AT THE FRAME's OWN LAYING OF THE FIRST CHAIN's THREAD (`FirstThread.lettersHead`,
Honest/Thread/FirstHead.lean), AT ALL ITS ARGUMENTS, AT NUMBER 355; stated from the thread and what
is said (`ThrS`, Honest/Thread/Said.lean), Said a variable. Statements with their proofs: calls of
GuardsAtM3.lean, GuardsLeft.lean and IndexShapeAtM3.lean of this folder, whose statements at
`lettersAt` hold at all its arguments, and unfoldings. THE FULL SIZE ALONE, AT THE HASH
`OnBytes.secondHashFunction` ALONE.

THE ROAD OF EACH GUARD (the four roads: the public form · the library's facts at reached states ·
one step back · a clause of `rides`):
  fin     the public form: where the chain stands (`k13_form_front`).
  waits   the public form: the same clause.
  reply   a clause of `rides`: `lettersHead` lays it from b₀ on (`head_reply`): LEFT: b₀ ≤ 355.
  taken   the library's fact at reached states on the index masks' ledger (`P1L20.room_at_reach`),
          with the written numbers: nothing left.
  lin     the library's fact at reached states on the codes (`Meaning.K2.recAll_all`), with the
          written numbers: nothing left.
  msg     the plan alone: the written numbers: nothing left.
  count   the library's reached states, with the law on the pile's length along the first chain
          (`pile_length_reach`, PileLengthReach.lean of this folder) and the written numbers
          (`k13_count_at`, CountAtM3.lean): nothing left. A SECOND ROAD, which nothing here calls: a
          clause of `rides` (`k13_count_at_head`): it leaves: that `riderPile` is among the thread's
          clauses, in force at 355, with the number 13 there. (The filler's pile does not give it: a
          filler may yield no row where the challenges are too few, and that it yields one at the
          thread's challenges is had FROM count.)
  form by the filler's pile (the filler: the parameter `pile`: the honest side's own account of the
          rows on the pile) (`k13_guardsLeft_at_head`): LEFT: b₀ ≤ 355 (it gives `ReplyRides`,
          without which `RowsTie` gives nothing); `RowsTie`; the test `pileFits` at the filler's
          pile where it yields a row.
  fit     its clauses on weights and column points: by the filler's pile: the same three. Its clause
          on the rows' mask entries: the library's fact at reached states (`LPFK9.masks_reached`):
          nothing left. Its clause on the index masks' message's shape: WHICH message: the public
          form (the item tied to the open pin); its shape: the library's fact at reached states
          (`IM.msgShapes_field`), with the written numbers (`k13_indexShape_at`,
          IndexShapeAtM3.lean): nothing left.
Main names:
  `k13_replyRides_head`: the thread gives the reply at 355, where b₀ ≤ 355.
  `k13_guards_stand_head`, `k13_guards_at_head`: **the nine**, from what is left of them.
  `k13_guardsLeft_at_head`: **what is left.** `k13_count_at_head`: count by the second road.
  `k13_guards_whole_at_head`: **the nine: from h, b₀ ≤ 355, `RowsTie` and the test at the filler's
    pile**: no premise that speaks of the state ALONE is left (`RowsTie` speaks of the state's pile,
    beside the filler's).
  `k13_accepted_at_head`: **`AcceptedS` at 355, at every `fall`**: from h, hb (b₀ ≤ 355), hH (the
    half found in the prover's first chain at the member's place is the kind's), hW (`RowsTie`) and
    hfill (the test at the filler's pile).

What is not claimed. That the hypothesis h can be met. That the thread holds at any run. Any of the
premises named as left. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.IndexShapeAtM3
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Riders
import Johnson.Desc.ProofFile.Honest.K13.SeatedPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.K13.Honest (rowReads)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead head_reply Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The thread gives the reply at border 355**, where its clause on the reply has begun. -/
theorem k13_replyRides_head (hb : b₀ ≤ 355) :
    ReplyRides (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 ProofFile.Inst.asked :=
  replyRides_of_rides _ fun _ _ hr =>
    head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hr

/-- **THE NINE GUARDS AT ONE STAND**, from h, b₀ ≤ 355, the thread, and what is left of the nine at
that stand: `k13_guards_stand_at` (GuardsAtM3.lean) with the guard "reply" shown. -/
theorem k13_guards_stand_head (hb : b₀ ≤ 355) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 355 k s m En)
    (hl : K13GuardsLeft h.𝔇.P13 s) : K13Guards h.𝔇.P13 s :=
  k13_guards_stand_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hT
    (k13_guard_reply _ (k13_replyRides_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb) _ hT) hl

/-- **THE NINE GUARDS FROM THE THREAD AND WHAT IS SAID, at border 355**: Said a variable; what is
left is asked from the same pair. -/
theorem k13_guards_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hb : b₀ ≤ 355)
    (hLeft : ∀ k s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355 k s m
        En → K13GuardsLeft h.𝔇.P13 s) :
    ∀ k s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355 k s m
        En → K13Guards h.𝔇.P13 s :=
  fun k s m En hS =>
    k13_guards_stand_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hS.1
      (hLeft k s m En hS)

/-- **WHAT IS LEFT OF THE NINE**: count from h and the thread (`k13_count_at`, CountAtM3.lean); fit
and form by the filler's pile: from hb (b₀ ≤ 355: it gives `ReplyRides`), its tie to the state's
(hW) and the test with code WHERE THE FILLER YIELDS A ROW (hfill). -/
theorem k13_guardsLeft_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {pile : PileOf ProofFile.Inst} (hb : b₀ ≤ 355)
    (hW : RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 pile
      ProofFile.Inst.asked)
    (hfill : ∀ x heard, pile x heard ≠ [] →
      pileFits h.𝔇.P13 ((pile x heard).map rowReads) = true) :
    ∀ k s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355 k s m
        En → K13GuardsLeft h.𝔇.P13 s :=
  fun k s m En hS =>
    k13_guardsLeft_whole_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hW
      (k13_replyRides_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb) hfill k s m En hS.1

/-- **THE NINE GUARDS**: from h, b₀ ≤ 355, the tie of the filler's pile to the state's, and the test
at the filler's pile where it yields a row. -/
theorem k13_guards_whole_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {pile : PileOf ProofFile.Inst} (hb : b₀ ≤ 355)
    (hW : RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 pile
      ProofFile.Inst.asked)
    (hfill : ∀ x heard, pile x heard ≠ [] →
      pileFits h.𝔇.P13 ((pile x heard).map rowReads) = true) :
    ∀ k s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 355 k s m
        En → K13Guards h.𝔇.P13 s :=
  k13_guards_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb
    (k13_guardsLeft_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb hW hfill)

/-- THE GUARD "count" BY A SECOND ROAD, which nothing here calls: where the thread's other clauses
are a list that holds the clause on the pile's length (`riderPile`, Honest/Thread/Riders.lean), in
force at 355, with the plan's number there. -/
theorem k13_count_at_head
    (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS)) {lo hi : Nat} {n : Nat → Nat}
    (hc : riderPile lo hi n ∈ cs) (hlo : lo ≤ 355) (hhi : 355 ≤ hi) (hn : n 355 = 13)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w).thread 355 k s m
      En) :
    s.out.pending.length = h.𝔇.P13.rows := by
  have hr : ridersOf cs 355 m.st.input s := hT.2.2.2.2.2.1.2
  have q : s.out.pending.length = n 355 := hr _ hc hlo hhi
  rw [q, hn, m3_rows h]

/-- **THE MEMBER IS ACCEPTED, at every `fall`, from the thread and what is said**: from h, hb, hH,
hW and hfill: by the kind's law that takes the guards from that pair (`k13_thread_acceptedS`), at
`k13_guards_whole_at_head`. -/
theorem k13_accepted_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} {pile : PileOf ProofFile.Inst} (hb : b₀ ≤ 355)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) = some (proverSideOfClaimCombination weights pile h.𝔇.P13))
    (hW : RowsTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 355 pile
      ProofFile.Inst.asked)
    (hfill : ∀ x heard, pile x heard ≠ [] →
      pileFits h.𝔇.P13 ((pile x heard).map rowReads) = true)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 :=
  k13_thread_acceptedS (Cl' := Unit) Said
    (k13_atK13_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hH)
    (fun blk hb' _ s _ _ hS rs gs t' q =>
      (k13_memberIs_at h).forth blk hb' s rs gs t'
        (k13_guard_form_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ hS.1).1 q)
    (k13_guards_whole_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb hW hfill) fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_replyRides_head
#print axioms ProofFile.Honest.K13.k13_guards_stand_head
#print axioms ProofFile.Honest.K13.k13_guards_at_head
#print axioms ProofFile.Honest.K13.k13_guardsLeft_at_head
#print axioms ProofFile.Honest.K13.k13_guards_whole_at_head
#print axioms ProofFile.Honest.K13.k13_count_at_head
#print axioms ProofFile.Honest.K13.k13_accepted_at_head
