-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5LeftOfCond.lean: kind K5: **What is truly left of the kind's law at the composed meaning's closed constant, as one structure of named conditions on public and closed data**: K5LeftAllFull
(Door/Law/K05LawOfLeftFull.lean: a pick of 28 letters and 20 fields) from K5CondAt h L, every other field being a theorem from the one head AtMgA: the equations on the filling and the data (K5MgIsAll.lean · K5AtConstant.lean) · the
piece, the plan and the book (K5PieceAll.lean) · K5Rest's 41 fields from what is kept here (rest_of_left, K5RestLeft.lean) · "below the base" from one test (low_all, K5LowAll.lean) · memAt from one test and someMem (memAt_field, K5MemOfSome.lean) · the pick itself (k5PickAll, K5PickAll.lean).
What is once per head stands in front of the groups; the reading of the witness is a term; the law over
witnesses (cells) is three conditions on public data; the identities' field is a theorem.
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)



Main names:
  K5CondsHead h: once per head: fence (every sampled tenant of an open pin sits in a tree that the sub-protocols in front have sent: one test on the table's numbers and the written lists) · pads (every place that a segment's seats
    name is off the pad of the segment's own copy) · oneShape (in the composed meaning's list of members, h.𝔇.ms, one seat bears one shape: with someMem it gives memAt: memAt_field, K5MemOfSome.lean).
  K5Tests …: the 4 fields of K5RestLeft (K5RestLeft.lean) that are neither a comparison with the base nor memAt, lifted by program, text for text: seatsPlan · shapesPlan · sent · someMem.
  K5CondsAt h L g a x₁: per group: cells (there is an inverse idx of the numbering with two tests of the lookup argument's own ledger) · tests (K5Tests at the closed letters).
  **K5CondAt h L**: K5's named condition at one head: head · each (for each g < 12, at whichever plan a and place x₁ the public parameters give). It reads no 𝔏, no piece and no witness.
  k5LeftAllFull_of_cond: K5CondAt h L → (the three flat lists' heads; g < 12; the row's piece at 14 (2 g + 1) + 4 is q) → K5LeftAllFull h L g q.
  K05Cond: the condition over all heads. **k05LawR_of_cond**: K05Cond → K05LawR.
Is it empty here? Implications. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). No member of K5CondAt is shown: none of its tests has run at its closed term. K05LawR is not proved.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05LawOfLeftFull
import Johnson.Desc.First.Att.Door.Law.K5PieceAll
import Johnson.Desc.First.Att.Door.Law.K5PickAll
import Johnson.Desc.First.Att.Door.Law.K5LowAll
import Johnson.Desc.First.Att.Door.Law.K5MemOfSome

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker OnBytes.Flat OnBytes.Slice Johnson.Pack KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent lookAt sigListCalls keptAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_in)
open Johnson.Desc.First.Walk.Tied (RchPub)
open P5J (AtMg AtMgA mgAtAll F0T TS Free)

section
variable (D : PubData) (Dn : Sent) (ms : List Mem) (Ld : Laid) (Ms : List OracleShape)
  (g : ℕ) (a : Attention.Plan) (x : Look.Place) (pl : VerifiableInference.Desc.Place) (rad : OracleShape → Nat)
  (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)

/-- **The fields of K5RestLeft that are neither a comparison with the base nor memAt.** Text for text, by program. -/
structure K5Tests : Prop where
  /-- [C] TWO TESTS ON PUBLIC DATA (the kind's own; STATED AT THE COMPOSED DATA's dS: RUN NOWHERE AT THAT TERM): the seats. -/
  seatsPlan : seatsPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ld
    (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (D.N.sent x.link 0) (D.N.msgsAt (some pl)) = true
  /-- [C] The shapes. -/
  shapesPlan : shapesPlanB D.dS (2 * g + 1) (keptAt Dn x.link).length Ms
    (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) (D.N.msgsAt (some pl)) = true
  /-- [C] THE COMPOSED MEANING's numbers: the seats lie in the segment's first sending. -/
  sent : ∀ i, seat i ∈ D.N.sent (2 * g + 1) 0
  /-- [C] The composed meaning's list of members (someB | listSits_some, Johnson/P5J/Rad3Seat3At.lean; tests evaluated, not proved: Rad3Seat3Tests.lean): for each member of the caller's list some member of ms is alike: one entry (shape and radius), one seat. (The caller's list itself is no sending of ms.) -/
  someMem : ∀ i, ∃ y ∈ ms, Alike y (⟨⟨sigListCalls Dn rad x.link, seat⟩, i⟩ : Mem)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **Once per head.** -/
structure K5CondsHead : Prop where
  /-- a test on the table's numbers and the written lists -/
  fence : fenceFit (P5J.At.N Zp cF) P5J.At.links P5J.At.ps = true
  /-- on the seats' places and the pads -/
  pads : PadsAll h
  /-- a test on the composed meaning's list of members: one seat bears one shape -/
  oneShape : oneShapeB h.𝔇.ms = true

/-- **Per group.** -/
structure K5CondsAt (L : Laid) (g : ℕ) (a : Attention.Plan) (x₁ : Look.Place) : Prop where
  /-- two tests of the lookup argument's own ledger, at an inverse of the numbering -/
  cells : ∃ idx, K5CellsCond h a x₁ idx
  /-- the tests at the composed meaning's closed data -/
  tests : K5Tests h.𝔇.pubD h.𝔇.sent h.𝔇.ms L (P5J.At.d12 Zp L).M g a x₁ ⟨1, some (2 * g + 1), 3, .K5⟩ h.𝔇.l3.rad (seatAll h x₁)

/-- **K5's NAMED CONDITION AT ONE HEAD.** -/
structure K5CondAt (L : Laid) : Prop where
  head : K5CondsHead h
  each : ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
    lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → K5CondsAt h L g a x₁

variable {h}

/-- **What is left, the tests on the lists paid, from the named condition.** -/
theorem k5LeftAllFull_of_cond (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) {L : Laid} (U : K5CondAt h L) {g : ℕ} (hg : g < 12)
    {q : Piece (ckP .two) (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (ProofFile.InstPub × TS) ProofFile.Cl
      (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)}
    (hq : (h.toAtMg.row 𝔏)[14 * (2 * g + 1) + 4]? = some q) : K5LeftAllFull h L g q := by
  obtain ⟨blk, E, a, x₁, xd, hP, h4, ea, hx, hxd, Pn, hat, -, -, hback, herr, hds, hSe, hb, Bk, -⟩ := k5_piece_all h 𝔏 q₁ q₂ q₃ hg hq
  obtain ⟨Lk, hLk⟩ := lkAt_all h hg
  have T := U.each g hg a x₁ ea hx
  have lo := low_all h U.head.fence hg (atRow_more h.toAtMg 𝔏 q₁ q₂ q₃ _ q hq (atRow_in h.toAtMg _ (by omega))).1
  have U' : K5RestLeftAll h L (P5J.At.d12 Zp L).M q.base g a x₁ ⟨1, some (2 * g + 1), 3, .K5⟩
      ((openSets LFullK PFullK (start LFullK))[14 * (2 * g + 1) + 4]?.getD []) :=
    { low := lo.1
      lowI := lo.2.1
      low0 := lo.2.2
      seatsPlan := T.tests.seatsPlan
      shapesPlan := T.tests.shapesPlan
      memAt := fun _ j _ => memAt_field U.head.oneShape _ _ T.tests.someMem j
      sent := T.tests.sent
      someMem := T.tests.someMem }
  exact ⟨k5PickAll h g a x₁ xd Lk blk E a.seam.tl.f9 (slotsOf (script a.own) + Forest.elems a.seam.tl.f9),
    { mgIs := mgIs_all h _ _
      mgGains := mgGainsPlus_all h h4 ea hx _ _
      dataIs := dataIs_all h _
      dataSent := dataSent_all h
      pubIs := hpubPlus_all h
      back := hback
      err := herr
      rounds := hds
      seatOf := hSe
      runs := hb
      planIs := hP
      p4 := h4
      planAt := ea
      lookC := hx
      lookD := hxd
      plan := Pn
      book := Bk
      moreBase := hM0_all
      moreIs := hm_all h
      rest := rest_of_left h hg ea hx hLk hat (twenty_full hg) U.head.pads T.cells U' }⟩

end

/-- **The condition over all heads**, under the listed seats and K5Along at the picked condition. -/
def K05Cond : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (L : Laid) (_ : P5J.At.laid? Zp = some L)
    (_ : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) (RchPub (F0T OnBytes.secondHashFunction Zp Np cF) typedPub) L
      (P5J.At.d12 Zp L).M h.𝔇.sent), K5CondAt h L

/-- **THE KIND's LAW IN THE COUNTED FORM, FROM THE NAMED CONDITION.** -/
theorem k05LawR_of_cond (H : K05Cond) : K05LawR :=
  k05LawR_of_leftFull fun Z D r Zp Np cF x h 𝔏 q₁ q₂ q₃ L hL A _ hg _ hq =>
    k5LeftAllFull_of_cond 𝔏 q₁ q₂ q₃ (H Z D r Zp Np cF x h L hL A) hg hq

end H2K5.Door

#print axioms H2K5.Door.k5LeftAllFull_of_cond
#print axioms H2K5.Door.k05LawR_of_cond
