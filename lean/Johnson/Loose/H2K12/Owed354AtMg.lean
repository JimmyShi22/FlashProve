-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12KindAtMg
import Johnson.Loose.H2K12.Tuple354
import Johnson.Loose.H2K12.PublicAt354
import Johnson.Loose.H2K12.SpentOfFacts
import Johnson.Loose.H2K12.AcrossOfSits
import Johnson.Loose.H2K12.Hands354AtSeat
import Johnson.Loose.H2K12.SeedAt354
/-
Johnson/Loose/H2K12/Owed354AtMg.lean: THE LAW OF THE PROXIMITY
TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN, sub-protocol number 354 of the table's written
list: THE ASSEMBLY: what is left of the kind's law in its counted form (Owed354, K12KindAtMg.lean)
FROM WHAT K12's FILES HAVE ON THE TIES, at the composed meaning's letters (MgAtAll.lean), UNDER ONE
NAMED LIST OF DEBTS. One Lean structure, one lemma on letters, two theorems: calls.
  K12Left h 𝔏 d   EVERY PREMISE THAT IS STILL LEFT, a field a debt: FIFTEEN. Each field's docstring
                   says what it is (facts on reached states; a closed fact or test; an equation on a
                   letter), who is to pay it, and whether it has run at the stored full-size files.
                   NO FIELD IS A LAW ANY MORE. d: the public numbers that the facts on reached
                   states read (First.FoldData): a letter, tied by three of the fields
  smp_listed       the reader of samples smpNamed (Johnson/Desc/Sound/SmpNamed.lean)
                   at a message that is listed at a member's seat is the kind K1's own
                   reading at that message's number
  owed354_of_left  K12Left → LastTypedAt → Owed354, at mem := memOf of the list of members and the
                   list of places: the second tie is hands_354 (H2K12/Hands354AtSeat.lean); the
                   fourth tie's first half is tuple_354_memOf (H2K12/Tuple354.lean), its second half
                   witness_memOf (H2K12/SpentOfFacts.lean); the fifth tie is rides_of_facts
                   (H2K12/AcrossOfSits.lean); the two facts on reached states that the structure
                   FoldFacts lacks are factsK12_of_reach's (H2K12/SeedAt354.lean)
  k12_kind_of_left K12Left → LastTypedAt → h.Kind 𝔏 K12
WHAT FALLS AT THE LETTERS, AND SO IS NO FIELD: the equations on the meaning's fields pin, noColl,
shown, held, pinW, decodes, row, pile and on its two public tests on the index masks' message: by
unfolding; that its test inOrder reads the public part alone: by unfolding; "the groups are seated"
and "the seats fit": the head's named tests on the list of rounds; "the decoder reads the public
part alone": by unfolding; the reader of samples: smp_listed; what is in hand of the piece: Seat354
(H2K12/TieAt354.lean); "the masks come early" and "one answer a sample": the sub-protocol's own test
on the list of rounds; the tests on the table's written lists: decided by the kernel in the files
named above.
WHAT IT IS NOT. A LIST OF DEBTS AND A JOINING: IT PAYS NO LAW. No example shows that the fifteen
fields can be met together; where one of them is false at the files the two theorems say nothing.
THE FIELD indexListed IS FALSE AT A SIBLING OF THE TABLE's NUMBERS AND HAS RUN TRUE AT THEM; see its
docstring. The field fold is the whole structure of facts on reached states (FoldFacts.lean),
unpaid. The full size alone.
WHERE A DOCSTRING SAYS "HAS RUN": an evaluation at the stored full-size files, at the evaluating
file's own terms for the numbers, the lists and the codes; that those terms are this file's letters
is by reading alone, for all fields alike. An evaluation is no proof.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12

open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.Sound
open P5J (AtMgA mgAtAll F0T TS Free fullLinks)

/-- **The reader of samples at a listed message.** -/
theorem smp_listed {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (hn : seats.Nodup)
    (a : P × VerifiableInference.Desc.First.S) (o : ℕ) (x : Mem)
    (h : seats[o]? = some (seatOf x)) :
    smpNamed cs seats a x.1 x.2 =
      VerifiableInference.Desc.K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o := by
  obtain ⟨ho, e⟩ := List.getElem?_eq_some_iff.1 h
  have hq : seatOf x ∈ seats := e ▸ List.getElem_mem ho
  have hi : seats.idxOf (seatOf x) = o := by
    rw [← e]
    exact hn.idxOf_getElem o ho
  rw [smpNamed_at cs seats a x.1 x.2 hq]
  show VerifiableInference.Desc.K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st
    (seats.idxOf (seatOf x)) = _
  rw [hi]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **EVERY PREMISE THAT IS STILL LEFT OF THE KIND's LAW AT 354.** -/
structure K12Left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (d : VerifiableInference.Desc.First.FoldData) : Prop where
  /-- AN EQUATION ON A LETTER: 𝔏's first two sub-protocols' letters are the first flat list's head
  and rest. To be paid by whoever lays 𝔏: true by the make of a chain's flat list at the right 𝔏. -/
  heads : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁
  /-- AN EQUATION ON A LETTER: the first chain's first tree has the number 0. To be paid by the
  field first of AtMgR (Johnson/P5J/AtMgR.lean). -/
  first : d.ft = 0
  /-- AN EQUATION ON A LETTER: d's codes are the first chain's. To be paid by AtMgR's field sent. -/
  codes : d.sent.codes = h.𝔇.cs
  /-- AN EQUATION ON A LETTER: d's list of the oracle messages' places is the list of seats off the
  list of rounds. To be paid from AtMgR's field listed and a closed fact on the laying of that list.
  It has run true at the stored full-size files. That there is a d with this field and the two above
  hangs on that laying's return. -/
  places : d.L.places = P5J.At.seats Zp
  /-- FACTS ON REACHED STATES: the one structure of such facts, at the condition of the
  counted form. This file spends seven of its fields: bookInOrder, seatsCarried, tidy, codes,
  bookFits, msgShapes, pileMasks. To be paid by the induction along the run, which is other files'
  to show. Its tests with code ran true on an honest run's states, by report. -/
  fold : VerifiableInference.Desc.First.FoldFacts h.toAtMg.rch (fun a => a.1) d P5J.At.reqW
    P5J.At.links P5J.At.ps
  /-- A CLOSED FACT ON THE IOP AS WRITTEN IN LEAN: sub-protocol number 353 of the first flat list
  sits at the place of the last code switch (SeatF1, H2K12/GroupAt354.lean), with numbers whose
  group is the table's number of the last group. To be paid by seatF1_open (H2K12/SeatF1AtOpen.lean)
  and two lemmas of the code switch's files on that number. The equation
  itself has not run. What has run: at the state at 354 of the one honest run that was walked, the
  finish's own frame's group and the list of rounds' number of the last group are both 25; the
  switch's own decision tests that frame's group against p.grp. -/
  seat353 : ∃ B p, cF.blocksInOrder[353]? = some B ∧ SeatF1 B p ∧
    p.grp = (P5J.At.N Zp cF).groupAt fullLinks.length
  /-- A CLOSED TEST: the list of shapes has, at a listed member's number, that member's shape.
  Nobody is named to pay it. It has run true at all 167 members at the stored full-size files;
  against the list shifted by one it fails. -/
  shapesListed : ∀ o y, ListedAt h.𝔇.ms d.L.places o y → d.M[o]? = some (y.1.l.get y.2).1
  /-- A CLOSED TEST: the kind K1's four tests on a shape (one answer; the codes' lengths; the
  shape's and the pad's tests) at every member of the list. More than is spent: one member is under
  test. Nobody is named to pay it. It has run true at all 167 members; at a shape with two answers
  it fails. -/
  tieAll : ∀ y ∈ h.𝔇.ms, VerifiableInference.Desc.K1.Tie h.𝔇.cs (y.1.l.get y.2).1
  /-- SIX CLOSED TESTS on the list of members, the list of places and the codes (PublicLeft354,
  H2K12/PublicAt354.lean). To be paid from the pins on the written sendings, and one of them (told)
  with the code switch's files. All six have run true at the stored full-size files, each with
  a negative test that fails. -/
  publicLeft : PublicLeft354 h.𝔇.cs h.𝔇.G d (P5J.At.N Zp cF) fullLinks.length O354 h.𝔇.ms
  /-- A CLOSED TEST of the table on its numbers: no two of the components that a row lays are one.
  Nobody is named to pay it. It has run true at the stored full-size files. -/
  laysOnce : VerifiableInference.Desc.First.laysNodup h.𝔇.arr (P5J.At.N Zp cF) fullLinks P5J.At.ps =
    true
  /-- A CLOSED TEST on the table's numbers: what the row at 354 lays is none of the three components
  that the riders read. Nobody is named to pay it. It has run true at a sibling of these numbers
  (without what the sub-protocols tell), with two negative tests that fail; at these numbers it has
  not run. -/
  clear : Rid354.clearB h.𝔇.arr (P5J.At.N Zp cF) fullLinks P5J.At.ps 354 = true
  /-- A CLOSED TEST: the list of places has the index masks' message at its seat. Nobody is named to
  pay it. AT THESE NUMBERS IT HAS RUN TRUE, at the list that laidOfChain lays, in a file of
  evaluations (Johnson/RunOne/SheetIndexNo.lean [not in this library]): the message's number is 4
  there, off what the first tree tells; with that tree's telling dropped the number is another. AT A
  SIBLING OF THESE NUMBERS (without what the sub-protocols tell, where the number is 0 by default)
  IT IS FALSE: the list has that seat at number 4. -/
  indexListed : d.L.places[(P5J.At.N Zp cF).indexNo]? = some (P5J.At.N Zp cF).index
  /-- A CLOSED TEST: the index masks' tree is sent in front of the piece at 354. Nobody is named to
  pay it. At a sibling of these numbers that tree's number is 1, and 77 trees stand in front at the
  one honest run that was walked; the test as it stands here has not run. -/
  fence : (P5J.At.N Zp cF).index.1 <
    VerifiableInference.Desc.Sound.nTrees ((D.at frS.P.T.a).ds₁.take 48237)
  /-- A CLOSED TEST on the meaning's list of extra public tests: none is asked at border 355. To be
  paid by the kernel at the composed meaning's closed list of such tests, which this list is by the
  lemma (mgAll_more_base, Johnson/Desc/Sound/MgBase.lean). At that closed list
  it has run: none at 355; one at 356. -/
  pubsNone : (VerifiableInference.Desc.First.pubSets (mgAtAll h).more fullLinks
    P5J.At.ps)[354 + 1]?.getD [] = []
  /-- A CLOSED TEST (goOnB, Johnson/Desc/K12/Coin/): the table's numbers at the two
  places, the test's own numbers, the listed trees and the codes fit, so that the promise's tests
  with code go on over an accept. Nobody is named to pay it. It has run true at sibling terms alone.
  -/
  goOn : VerifiableInference.Desc.K12.Coin.goOnB (P5J.At.N Zp cF) ⟨1, none, 2, .K12⟩
    ⟨1, none, 3, .K13⟩ (H2K.JointK.pL Np) (VerifiableInference.Desc.K12.Door.toTree d.L)
    d.sent.codes = true

set_option maxHeartbeats 4000000 in
/-- **WHAT IS LEFT OF THE KIND's LAW IN ITS COUNTED FORM, FROM THE LIST OF DEBTS.** -/
theorem owed354_of_left {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok}
    {d : VerifiableInference.Desc.First.FoldData} (L : K12Left h 𝔏 d) (rdN : ℕ → ℕ)
    (hT : LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL) :
    Owed354 h 𝔏 (fun _ => memOf h.𝔇.ms d.L.places) rdN := by
  intro q hq hs
  have hsmp : ∀ (a : ProofFile.InstPub × VerifiableInference.Desc.First.S) o y,
      ListedAt h.𝔇.ms d.L.places o y → h.𝔇.smp a y.1 y.2 =
        VerifiableInference.Desc.K1.smpAt h.𝔇.cs (y.1.l.get y.2).1 (y.1.l.get y.2).2 a.2.st o :=
    fun a o y hl => smp_listed h.𝔇.cs (P5J.At.seats Zp) (L.places ▸ L.publicLeft.placesOnce) a o y
      (L.places ▸ hl.2)
  obtain ⟨B₀, p₀, hB₀, hK₀, hg₀⟩ := L.seat353
  have hF : ∀ a, h.toAtMg.rch 354 a → a.1.2.failed = none →
      FactsK12 d (P5J.At.N Zp cF) fullLinks.length h.𝔇.cs h.𝔇.ms a.1.2 :=
    fun a hr hm => factsK12_of_reach cF.blocksInOrder (F0T OnBytes.secondHashFunction Zp Np cF).start₁ 353 B₀ hB₀ p₀ hK₀
      (P5J.At.N Zp cF) fullLinks.length hg₀ h.𝔇.cs h.𝔇.ms d L.codes h.toAtMg.rch
      (fun _ _ hr' => hr'.1) L.fold L.shapesListed L.tieAll a hr hm
  have t2 : T2At
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.toAtMg.rch 354 q :=
    hands_354
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h.𝔇.cs h.𝔇.G d h.𝔇.smp h.𝔇.ms (P5J.At.N Zp cF) (mgAtAll h) Zp Np (D.at frS.P.T.a) q hs
      (fun _ => rfl) (fun _ => rfl) rfl L.indexListed L.first hsmp L.pubsNone L.goOn h.𝔇.decT rfl
      (fun y a a' e => by
        obtain ⟨z, s⟩ := a
        obtain ⟨z', s'⟩ := a'
        obtain rfl : z' = z := e
        rfl)
      (fun a a' e ha => by
        obtain ⟨z, s⟩ := a
        obtain ⟨z', s'⟩ := a'
        obtain rfl : z' = z := e
        exact ha)
      rfl rfl L.fence h.toAtMg.rch
      (fun a _ hr hm => ⟨factsF_of_fold L.fold 354 a hr (not_not.1 hm),
        L.fold.codes 354 a hr (not_not.1 hm)⟩)
  obtain ⟨pre, J, leave, _, hb, h0, hbase, hout, hSits, hPub⟩ := hs
  obtain ⟨_, _, rfl⟩ := hout
  have hplan := hPub.2.1.plan
  have hfitS : SeatsFit h.𝔇.cs h.𝔇.G h.𝔇.ms :=
    seatsFit_of_B (F0T OnBytes.secondHashFunction Zp Np cF) (P5J.At.cs Zp) (P5J.At.members Zp Z.lay)
      ((P5T.seatsFitB_R _ _ _ _ _ (fun p hp _ => P5T.planSeats_send_lt Zp Zp.D.1 p hp)).trans
        h.plan.fit)
  have hP : PublicK12 h.𝔇.cs h.𝔇.G
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      (H2K.JointK.pL Np) H2K.Member.rLFull d (P5J.At.N Zp cF) fullLinks.length O354 h.𝔇.ms :=
    publicK12_at h.scope h.laid.pub h.laid.places hT hPub h.𝔇.cs h.𝔇.G "proof file"
      (D.at frS.P.T.a) h.laid.planOk
      (by rw [P5J.LaidAt.atDepth h.scope h.laid]; exact h.laid.data) d (P5J.At.N Zp cF)
      fullLinks.length O354 h.𝔇.ms hfitS L.first L.codes rowOpen_354 L.publicLeft
  refine ⟨t2, ?_, ?_, ?_⟩
  · exact tuple_354_memOf
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h.𝔇.cs h.𝔇.G (H2K.JointK.pL Np) H2K.Member.rLFull rdN d h.𝔇.smp h.𝔇.ms
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.toAtMg.rch 354 q _ _ hb h0 hSits hP rfl
      hsmp hF
  · exact witness_memOf
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT 𝔏.c₀ P5J.At.tokOf
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps 354 Wit354.place_full Wit354.openFit_full
      rfl rfl rfl rfl h.plan.hG L.laysOnce L.publicLeft.seatsOnce h.toAtMg.rch q d L.first L.codes
      (fun a _ hr hm => ⟨hF a hr (not_not.1 hm), L.fold.bookFits 354 a hr (not_not.1 hm)⟩)
  · exact rides_of_facts
      (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
      h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT 𝔏.c₀ P5J.At.tokOf
      (P5J.At.N Zp cF) (mgAtAll h) fullLinks P5J.At.ps h.𝔇.mat13 354 Rid354.place_written
      Rid354.riders_full Rid354.readsOpen_written Rid354.rowsApart_written pinI_open_written
      L.clear rfl rfl rfl (fun _ _ _ _ => rfl) h.toAtMg.rch q
      (by rw [hbase, Nat.zero_add]; exact L.fence)
      (H2K.JointK.pL Np) d _ _ hb h0 hSits (laysOnly_outCore ProofFile.sameReply)
      (H2K.JointK.early_of_planOk _ hplan) (H2K.JointK.answers_of_planOk _ hplan)
      (fun _ => rfl) (fun _ => rfl) rfl L.indexListed L.first hsmp
      (fun a _ hr hm => factsF_of_fold L.fold 354 a hr (not_not.1 hm))

/-- **THE KIND's LAW IN THE COUNTED FORM, FROM THE LIST OF DEBTS.** -/
theorem k12_kind_of_left {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok}
    {d : VerifiableInference.Desc.First.FoldData} (L : K12Left h 𝔏 d) :
    LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL → h.Kind 𝔏 KindName.K12 := fun hT =>
  k12_kind_at_mg h 𝔏 L.heads _ (fun _ => 0) (owed354_of_left L _ hT) hT

end H2K12

#print axioms H2K12.smp_listed
#print axioms H2K12.owed354_of_left
#print axioms H2K12.k12_kind_of_left
