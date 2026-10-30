-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/IndexShapeAtM3.lean: kind K13, the members' batching: A CLAUSE OF
THE NINE GUARDS THAT SPEAKS OF THE STATE ITSELF: the index masks' message's shape (`indexShapeFits`,
GuardsLeft.lean of this folder), UNDER THE THREAD AT BORDER 355, AT THE LIBRARY's OWN PARAMETERS
(`FirstThread.lettersAt`, Honest/Thread/FirstAt.lean). Statements with their proofs. THE FULL SIZE
ALONE, AT THE HASH `OnBytes.secondHashFunction` ALONE.

The road. (1) WHICH message: the public form holds, beside the public items that are open at a
border, those that are tied to an open item (`pubHeld`, `pubOfItems`,
Johnson/Desc/First/Borders.lean); the index masks' pin is open at 355, and the item "the state's
number of the index masks' message is the plan's" is tied to it (`m3_indexIs_tied`, by Lean's
kernel); the plan's number is 4 (`K11.indexNo_four`, Johnson/K11R/CondOfTwo.lean): `k13_index_at`.
(2) ITS SHAPE: at every reached state without a mark the statement's messages have the listed shapes
(`IM.msgShapes_field`, Johnson/IMR/SeatsField.lean); its premise on the planner's sendings holds
under h (`P5J.sendsB_of_madeRow`, `P5J.madeRow_at_head`): `k13_msgShapes_at`. (3) In scope the list
is the written one, and the written shape number 4 passes the four clauses (`shapeI_written`, by
Lean's kernel; `shapeI_rejects`: number 5 does not).
Main names:
  `k13_index_at`, `k13_msgShapes_at`: (1) and (2).
  `k13_indexShape_at`: **the clause.**
  `k13_guardsLeft_whole_at`: **`K13GuardsLeft` under the thread, from `RowsTie`, `ReplyRides` and
    the test `pileFits` at the filler's pile where it yields a row: no premise that speaks of the
    state ALONE is left** (the guard count: `k13_count_at`, CountAtM3.lean). (The filler: the
    parameter `pile`: the honest side's own account of the rows on the pile: GuardsLeft.lean's
    head.)

What is not claimed. That the hypothesis h can be met. That the thread holds at any run. `RowsTie`,
`ReplyRides`, or that a filler's pile passes the test. The guard count is not shown in this file:
CountAtM3.lean of this folder shows it, under h and the thread. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.GuardsLeft
import Johnson.Desc.ProofFile.Honest.K13.CountAtM3
import Johnson.Desc.ProofFile.Honest.K13.BehindAtM3At
import Johnson.IMR.SeatsField
import Johnson.IMR.AtReachFits
import Johnson.P5J.FoldJ3
import Johnson.P5J.AtMgRAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (S Pub onAt openSets pubSets pubHeld pubOfItems start)
open VerifiableInference.Desc.K12.Door (msgsOfChain atFirstShapes msgShape_at)
open VerifiableInference.Desc.K13.Own (masksMessageFits)
open VerifiableInference.Desc.K13.Law (MFull msgs_at)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open Johnson.Desc.First.Walk.Tied (Reach leftIsB_iff)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS mgAtAll)
open ProofFile.Honest.FirstThread (lettersAt Script WtF noStrs)

set_option maxRecDepth 1000000 in
/-- At the written lists the public item "the index masks' number" is tied to an item that is open
at border 355. -/
theorem m3_indexIs_tied : Pub.indexIs ∈
    pubOfItems (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[355]?).getD []) := by
  decide +kernel

/-- The written shape of the message number 4 passes the library's test on the index masks' message
(`K13.Own.masksMessageFits`, Johnson/Desc/K13/Own.lean), at the written shape of the test on the
table. -/
theorem shapeI_written : (MFull[4]?).map (fun o =>
    masksMessageFits o proofSizedFull.batch.shape) = some true := by
  decide +kernel

/-- A negative test: the written shape of the message number 5 does not. -/
theorem shapeI_rejects : (MFull[5]?).map (fun o =>
    masksMessageFits o proofSizedFull.batch.shape) = some false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **Under the thread at border 355 the state's number of the index masks' message is 4**: out of
the public form: the public item that is tied to the open pin. -/
theorem k13_index_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    s.out.indexMasks = 4 := by
  obtain ⟨hf, hP⟩ := hT.2.2.1
  have hf' : s.failed.isNone = true := hf
  have hP' : onAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).N
      (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).mgP P5J.At.links
      P5J.At.ps[355]? (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[355]?).getD [])
      (((pubSets (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).mgP.more
        P5J.At.links P5J.At.ps)[355]?).getD []) (m.st.input.x.pub, s) noStrs := hP
  obtain ⟨-, hor⟩ := hP'
  rcases hor with hbad | ⟨hB, -⟩
  · exact absurd (Option.isNone_iff_eq_none.1 hf') hbad
  · simp only [Bool.and_eq_true] at hB
    have hp := hB.1.2
    unfold pubHeld at hp
    have q := List.all_eq_true.1 hp Pub.indexIs (List.mem_append_right _ m3_indexIs_tied)
    have q' : (mgAtAll h).pub Pub.indexIs (m.st.input.x.pub, s) = true := q
    rw [(pubM3_at h).indexIs] at q'
    have e : s.out.indexMasks = h.𝔇.N.indexNo := eq_of_beq q'
    rw [e]
    exact K11.indexNo_four h

/-- **There the statement's messages have the listed shapes**: the library's fact at reached states;
its premise on the planner's sendings holds under h. -/
theorem k13_msgShapes_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    atFirstShapes (msgsOfChain Zp.made.proof.1) s = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact IM.msgShapes_field h.scope h.reads O
    (fun k (a : ProofFile.InstPub × TS) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) id
    (Meaning.K2.fold_of_rch fun _ _ hr => hr) h.laid.planOk
    (P5J.sends_at O (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))) 355
    (m.st.input.x.pub, s)
    (k13_reach_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
    (k13_guard_form_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT).1

/-- **THE CLAUSE ON THE INDEX MASKS' MESSAGE's SHAPE, under the thread at border 355.** -/
theorem k13_indexShape_at {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
      m En) :
    indexShapeFits s.st h.𝔇.P13.lin s.out.indexMasks = true := by
  have hi := k13_index_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT
  have hm := k13_msgShapes_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT
  obtain ⟨l, hl, -, -⟩ := leftIsB_iff.1
    (k13_left_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
  have hl' : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l := hl
  rw [hi] at hl' ⊢
  cases hx : s.st.oracles[4]? with
  | none =>
    rw [hx] at hl'
    cases hl'
  | some y =>
    have h4 : 4 < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
    have e := msgShape_at hm 4 h4
    rw [hx, msgs_at (congrArg Prod.fst
      (sends_in_scope h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1))] at e
    have w := shapeI_written
    rw [← e] at w
    unfold indexShapeFits
    rw [hx]
    show masksMessageFits y.shape Zp.first.lin = true
    rw [(m3_written h).2.1]
    exact Option.some.inj w

/-- **SO NO PREMISE THAT SPEAKS OF THE STATE ALONE IS LEFT FOR THE THREE** (`RowsTie` speaks of the
state's pile, beside the filler's): from the tie of the filler's pile to the state's, that the
thread gives the reply, and the test at the filler's pile where it yields a row. The guard "count":
`k13_count_at` (CountAtM3.lean of this folder). -/
theorem k13_guardsLeft_whole_at {pile : PileOf ProofFile.Inst} {asked : ProofFile.Inst → E}
    (hW : RowsTie (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355 pile
      asked)
    (hY : ReplyRides (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) 355
      asked)
    (hfill : ∀ x heard, pile x heard ≠ [] →
      pileFits h.𝔇.P13 ((pile x heard).map VerifiableInference.Desc.K13.Honest.rowReads) = true) :
    ∀ k s m En,
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 355 k s
        m En → K13GuardsLeft h.𝔇.P13 s :=
  k13_guardsLeft_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hW hY hfill
    (fun _ _ _ _ hT => k13_count_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT)
    fun _ _ _ _ hT =>
      k13_indexShape_at h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hT

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m3_indexIs_tied
#print axioms ProofFile.Honest.K13.shapeI_written
#print axioms ProofFile.Honest.K13.shapeI_rejects
#print axioms ProofFile.Honest.K13.k13_index_at
#print axioms ProofFile.Honest.K13.k13_msgShapes_at
#print axioms ProofFile.Honest.K13.k13_indexShape_at
#print axioms ProofFile.Honest.K13.k13_guardsLeft_whole_at
