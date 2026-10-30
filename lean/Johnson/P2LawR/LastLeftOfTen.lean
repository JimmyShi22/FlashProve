-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/LastLeftOfTen.lean: THE JOIN lastLeft_at_head IN ITS FORM WITH TEN FIELDS
(lastLeft_of_ten): `AtMgA.LastLeftAt` (Johnson/P5J/L0/LastLeftAt.lean: what is left
of the last chain's field at the value, no letter) FROM THE HEAD AT o := OnBytes.secondHashFunction AND TEN
CLOSED FIELDS BY NAME (structure AtMgA.LastRestTen). One structure, one theorem: calls.


THREE FURTHER FIELDS FALL: madePinned follows
from madeRow (pinnedAt_of_row, Desc/Ok/PlanWritten/MadeTestLaws.lean) · tests: Sh.tests_at_head,
from the head and madePinnedAt · laid: ld_at_head, from the same.
HOW EACH FIELD OF LastLeft IS HAD: row0B · hB3 · hP: Johnson/P2LawR/LastLeftOfTwo.lean · hT :=
Sh.tests_at_head · hRc := hRc_at_left_gen (general in the first table's meaning,
so that it stands over the newer tower) at Mg₁ := h.toAtMg.mq h.𝔇, L := L0.ldAt Zp and K := the
second half of h.toAtMg.rc; its premise hII (that meaning's test at the item indexIs) is had in four
lines from mgAll_indexIs (Johnson/Desc/Last/IndexAtEndAll.lean), mgAt_is_mq (P5J/RowsAtMg.lean)
and the field indexNo: a lemma of the like, mq_indexIs, lies in a file
(Johnson/Desc/Last/OwnAtHead.lean) that stands over the elder tower alone · hS := hS_at_left.
THE STRETCH IS NOT EMPTY: it comes by hP's own call: planOk₃_at_join gives ∃ dB dt, PlanOk₃ … dB dt
…, and PlanOk₃'s own field stretch says that L0.l3At … = dB :: dt: so LastLeftAt's match opens at
that pair, never at []. (The field core says it too: its arm at [] is False; the head alone gives it
as well: stretch_at_head.) A RAISED LIMIT stands in this file (maxRecDepth 40000),
as in the files that it calls. NO FACT ON STATES IS AMONG THE TEN. ONE IS A LAW IN A FIELD's PLACE:
the closed sentence k2told, a theorem (k2Told_paid). THE OTHER NINE ARE CLOSED AND
CAN BE EVALUATED: three comparisons and a closed test with two memberships (the three ends at
the head) · one closed test of fifteen conjuncts, at the stretch's own head and tail (core) · one
closed test of five and two closed equations (sits, indexNo, msgs) · two pins (cutRow, madeRow).
WHICH DOOR. The theorem itself asks nothing of the door: the two pins are fields. They come off
h.laid.asks as rows of the door's asksAt2 (thirteen rows); asksAt1 has eight rows,
neither pin.
Where this and lean/THEOREM.md differ, the page holds. The three ends
(twoTrees, elder, endTests) lean on asksAt2 likewise.
IS IT EMPTY? NO MEMBER: that the head and the ten can be met together at the real files is shown by
nobody. madeRow is reported true at the full size's stored files (not shown here); of the
other eight closed fields no evaluation at these very terms is known here. k2told is a
closed sentence: if false, the theorem says nothing. k2told is a theorem
(Meaning.Carry.k2Told_paid, Johnson/IMR/ToldPaid.lean), and the join is had from the head without
the ten fields (Johnson/P2LawR/LastLeftAlone.lean). The full size alone (the tests
Sh.Tests are reported false at the small size; not shown here). Nothing on soundness.
-/
import Johnson.P2LawR.LastLeftOfTwo
import Johnson.P2LawR.HSAtLeft
import Johnson.P2LawR.LdAtLeft
import Johnson.Desc.K14.Law.SharedConstChainOkAtHead
import Johnson.ToldDescR.HRcAtLeftGen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers openSets sampledIn start)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE HEAD, BY NAME.** Ten fields. No fact on states;
nothing "at every opening". -/
structure AtMgA.LastRestTen (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) : Prop where
  /-- A CLOSED SENTENCE on the texts, without a letter of the files (Johnson/IMR/MsgsSwitch.lean): A
  LAW IN A FIELD's PLACE: no evaluation can show it: true or false once and for all. SPENT BY: hB3
  (three_at_head). WHOSE: k2Told_paid (IMR/ToldPaid.lean), a call of told_tenants
  (K2C/ToldTenants.lean).
  Where this and lean/THEOREM.md differ,
  the page holds. -/
  k2told : _root_.Meaning.Carry.K2Told
  /-- A COMPARISON of two numbers of the data. SPENT BY: hP. WHOSE:
  AtMg.trees_at (Johnson/HB/LLHARD/HeadFacts.lean). -/
  twoTrees : 1 < (D.at frS.P.T.a).t₂
  /-- TWO COMPARISONS. SPENT BY: hP. WHOSE: AtMg.elderBelow_at. -/
  elder : (At.N Zp cF).index.1 < (D.at frS.P.T.a).t₁ ∧ (At.N Zp cF).w.1 < (D.at frS.P.T.a).t₁
  /-- A CLOSED TEST AND TWO MEMBERSHIPS in a closed list. SPENT BY: hP. WHOSE:
  AtMg.endTests_at (Johnson/HB/LLHARD/PlanOk3AtHead.lean). -/
  endTests : sampledBelow ((D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂) (At.N Zp cF) ((openSets
    fullLinks (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true
    fullLinks true).length]?.getD []) = true ∧ (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets
    fullLinks (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true
    fullLinks true).length]?.getD []) ∧ (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets
    fullLinks (First.flatPlaces true fullLinks true) (start fullLinks))[(First.flatPlaces true
    fullLinks true).length]?.getD [])
  /-- ONE CLOSED TEST, fifteen conjuncts (coreB), at the head and the tail of the
  third piece's stretch itself (L0.l3At): no letter is bound: a file of evaluations can evaluate
  it. SPENT BY: hP (planOk₃_at_join over coreB_law). EVALUATED: by nobody at
  these terms. -/
  core : match L0.l3At OnBytes.secondHashFunction D Zp Np cF with
    | [] => False
    | dB :: dt => P2Law.PlanLeft.coreB OnBytes.secondHashFunction ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a)
        (F0T OnBytes.secondHashFunction Zp Np cF) (At.arr Zp) dB dt (At.ms Zp Z.lay)
        (L0.ms2J (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) (At.N Zp cF)
        (L0.nsJ (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) H2K.Member.rWFull
        ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) (L0.ldAt Zp) = true
  /-- A CLOSED TEST: five tests on the plan as one test with code
  (Johnson/ToldDescR/OwnSitsBools.lean: 4 < 197; the laying's places number 4 and 197 are the two
  elder seats; the chain's messages number 4 and 197 have their shapes). SPENT BY: hRc, through
  planSits_iff. -/
  sits : ToldDesc.planSitsB (L0.ldAt Zp) (VerifiableInference.Desc.K12.Door.msgsOfChain
    Zp.made.proof.1) (vAt Zp (At.N Zp cF)) 4 197 = true
  /-- A CLOSED EQUATION. SPENT BY: hRc (through its premise on the meaning's test at the item
  indexIs). -/
  indexNo : (At.N Zp cF).indexNo = 4
  /-- A CLOSED EQUATION. SPENT BY: hRc. -/
  msgs : (At.N Zp cF).msgsAt none = 197 + VerifiableInference.Desc.Last.wMsgs Zp
  /-- A PIN: a row of the door's asksAt2. SPENT BY: hRc. WHOSE: off h.laid.asks
  (asks_pins, Johnson/Desc/Laid/ProofAsksLaw2.lean). -/
  cutRow : VerifiableInference.PlanWritten.cutRow (F0T OnBytes.secondHashFunction Zp Np cF) Zp = true
  /-- A PIN: a row of the door's asksAt2. SPENT BY: hRc; AND, through madePinnedAt (which follows
  from it: pinnedAt_of_row): hT (Sh.tests_at_head), hS
  (hS_at_left) and the one laying Ld (ld_at_head). WHOSE: off h.laid.asks
  (asks_pins). EVALUATED: reported true at the full size's stored
  files; not shown here. -/
  madeRow : VerifiableInference.PlanWritten.madeRow Zp = true

/-- **THE LAST CHAIN's FIELD AT THE VALUE: WHAT IS LEFT OF IT, FROM THE HEAD AND LastRestTen.** -/
theorem AtMgA.lastLeft_of_ten (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) (R : h.LastRestTen) :
    h.LastLeftAt := by
  have hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true :=
    VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [R.madeRow, Bool.or_true])
  have hII : ∀ a, (h.toAtMg.mq h.𝔇).pub .indexIs a = K13.indexIsC 4 a.2 := by
    intro a
    have k : (mgAt h.toAtMg h.𝔇).pub .indexIs a = K13.indexIsC (At.N Zp cF).indexNo a.2 :=
      VerifiableInference.Desc.Last.mgAll_indexIs (h.toAtMg.𝔇 h.𝔇) mgBase a
    rw [R.indexNo, mgAt_is_mq h.toAtMg h.𝔇] at k
    exact k
  exact h.lastLeft_of_two
    ⟨R.k2told, Sh.tests_at_head h hy _, R.twoTrees, R.elder, R.endTests, R.core⟩
    (fun q y ho hr hm => ToldDesc.hRc_at_left_gen h.toAtMg (h.toAtMg.mq h.𝔇) hII
      (P2Law.Left.ld_at_head h.toAtMg hy) (fun q => h.toAtMg.typed q.1)
      ((ToldDesc.planSits_iff _ _ _ _ _).1 R.sits) R.msgs R.cutRow R.madeRow q y ho hr hm)
    (P2Law.Left.hS_at_left h hy)

end P5J

#print axioms P5J.AtMgA.lastLeft_of_ten
