-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/BookAtSwitches.lean: the kind "the code switch" (K2): THE FIELD book OF THE PREMISES
`FreshAsks` (Johnson/Desc/ProofFile/Honest/K2/Fresh.lean), IN ITS OWN TEXT, UNDER THE LIBRARY's HEAD
AND THE OPENING, AT WHATEVER BOOK bookWhole RETURNS AT F0T AND AT THAT DESCRIPTION's OWN ORDER OF
PLACES, AT THE ELEVEN SWITCHES AT THE LINKS 2, 4, …, 22: for every address q the kind's public test
`bookFits` says yes at what q spends of the switch's coins and at what is known. AND WITH IT, AT
THESE ELEVEN: ALL EIGHT PREMISES, AND THE STATEMENT's END `FreshOf`: the copy, letter for letter, of
the field fresh of the frame's `Good`. It lies in the side library because it imports files of it.
No definition; nothing is evaluated here: the closed facts stand in AtFullSide/K2/OwnerTest.lean and
OwnerTest/G01.lean … G11.lean, one owner a file; lemmas: calls.

  `ownerTest_written`   the public test `ownerTest` says yes at each written place whose link is one
                    of 2, 4, …, 22: the eleven closed facts joined
  `book_at_switch`  THE FIELD book
  `freshAsks_at_switch`, `freshOf_at_switch`   all eight premises; the statement's end

By, of other authors, none sealed: `owned_written`, `ownedListW`, `ownerAt`
(AtFullSide/K1/OwnerEntriesAtSwitches.lean, RowTakers/AllDefs.lean, RowTakers/Defs.lean): the walk
of the written book's entries, owner by owner. Sealed, of another group of authors: `posW`
(AtFullSide/K14/RawTwinKit.lean); of the frame's: `placedAt`, `beforeG`
(Honest/BookLinear/Positions.lean). Ours, none sealed: `evenLink`, `ownerTest`, `ownerTestW01` …
`ownerTestW11` (AtFullSide/K2/OwnerTest.lean, OwnerTest/G01.lean … G11.lean; that the test can say
no: OwnerTest/Bent.lean, not imported) · `book_at_owner` (AtFullSide/K2/BookBridge.lean) · `ownerOk`
(Honest/K2/Law/BookByRuns.lean) · `freshAsks_of_book`, `freshOf_of_book`
(Honest/K2/Law/FreshOfBook.lean). Sealed, ours: `places_at_head` (Honest/K2/Law/PlacesWritten.lean).

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM TOGETHER EVERY LAW HERE HOLDS EMPTILY: "no premise is left on the book" IS NOT "had". The
book's return, hB, is no third such: under the head bookWhole returns at F0T
(`bookWhole_returns_at_head_ahead`, AtFullSide/K14/WholeAheadAtHead.lean, not imported); at the two
named sets of public files the head has a member at which the opening holds too, at some Bs and base
(`headJoins_named`, AtFullSide/Top/HeadJoins.lean; not imported). THE
WRITTEN LIST IS A LISTING: its authors printed it off the written book's own entries and the kernel
holds it against these: no second source; the twins show that the tests can fail, not that the book
is right. THE MERGES ARE mergesByName's, which the frame's own text calls a guess. THAT A THREAD's
BOOK IS WHAT bookWhole RETURNS AT F0T IS NOT SAID. AT ELEVEN OF THE 25 SWITCHES ALONE HERE: the
field book at all 25, under the same h, O and hB: `book_at_place` (AtFullSide/K2/BookAtPlace.lean,
which imports this file). THE ELEVEN
CLOSED FACTS BENEATH ARE LEAN's KERNEL's ALONE: REPLAYED BY NO INDEPENDENT CHECKER. THE LAST END IS
A LAW OVER COINS: an equation of two laws of chance over the part's uniform coins; what
Honest/K2/Law/FreshOfBook.lean's limits say of it holds here. `bookFits` reads the book's numbers:
that a part lays, spends or carries what these say is not said. D, readers, ok, fs stay free
letters. The full size and the format's second hash function alone. Nothing here says what the statements
would mean for any property.
-/
import AtFullSide.K1.OwnerEntriesAtSwitches
import AtFullSide.K2.OwnerTest.G01
import AtFullSide.K2.OwnerTest.G02
import AtFullSide.K2.OwnerTest.G03
import AtFullSide.K2.OwnerTest.G04
import AtFullSide.K2.OwnerTest.G05
import AtFullSide.K2.OwnerTest.G06
import AtFullSide.K2.OwnerTest.G07
import AtFullSide.K2.OwnerTest.G08
import AtFullSide.K2.OwnerTest.G09
import AtFullSide.K2.OwnerTest.G10
import AtFullSide.K2.OwnerTest.G11
import AtFullSide.K2.BookBridge
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Chain Block)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law (placesW places_at_head ownerOk entryTuple freshAsks_of_book
  freshOf_of_book)
open AtFullSide.K14 (posW rawAheadW)
open AtFullSide.K1 (ownerAt ownedIn ownedListW owned_written)

/-- **The test says yes at each written place whose link is one of 2, 4, …, 22.** -/
theorem ownerTest_written {p : SwitchPlace} (hpW : p ∈ placesW) (he : evenLink p = true) :
    ownerTest p = true := by
  unfold evenLink at he
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at he
  have h0 : p.link % 2 = 0 := beq_iff_eq.1 he.1.1
  have hl : p.link = 2 ∨ p.link = 4 ∨ p.link = 6 ∨ p.link = 8 ∨ p.link = 10 ∨ p.link = 12 ∨
      p.link = 14 ∨ p.link = 16 ∨ p.link = 18 ∨ p.link = 20 ∨ p.link = 22 := by omega
  rcases hl with e | e | e | e | e | e | e | e | e | e | e
  · exact List.all_eq_true.1 ownerTestW01 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW02 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW03 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW04 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW05 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW06 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW07 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW08 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW09 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW10 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)
  · exact List.all_eq_true.1 ownerTestW11 p (List.mem_filter.2 ⟨hpW, beq_iff_eq.2 e⟩)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}

/-- **THE FIELD book, IN ITS OWN TEXT, AT A SWITCH AT ONE OF THE LINKS 2, 4, …, 22.** -/
theorem book_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hp : p ∈ switchPlaces Zp Bs.G₀) (he : evenLink p = true) :
    ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
      (K2.switchFresh p.sizes p.others p.foldVars) (B.spentBy ⟨p.place, 0⟩ q)
      (B.knownBy (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) ⟨p.place, 0⟩ q) = true := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have t := ownerTest_written hpW he
  unfold ownerTest ownerTestAt at t
  rw [Bool.and_eq_true, Bool.and_eq_true] at t
  obtain ⟨⟨t1, t2⟩, t3⟩ := t
  unfold evenLink at he
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at he
  have ho : (⟨p.place, 0⟩ : Addr) = ownerAt (p.link / 2) := by
    rw [beq_iff_eq.1 t1]
    rfl
  have hL : (rawAheadW.filter fun e => e.owner == ownerAt (p.link / 2)).map entryTuple =
      ownedListW (p.link / 2) := by
    have e := owned_written (g := p.link / 2) (by omega) (by omega)
    unfold ownedIn at e
    have hf : entryTuple = fun e : Ahead => (e.spender, e.start, e.count, e.once) := rfl
    rw [hf]
    exact e
  rw [ho]
  exact book_at_owner h hB (o := ownerAt (p.link / 2)) (L := ownedListW (p.link / 2)) hL t2 t3

variable {W₀ Rc Xi Tr X : Type}

/-- **ALL EIGHT PREMISES AT SUCH A SWITCH**, at the letters at which the kind's lot of rows lays its
row, at the book and the description's own order. -/
theorem freshAsks_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hp : p ∈ switchPlaces Zp Bs.G₀) (he : evenLink p = true) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (ok : Xi → Bool) (fs : List (Fall TS)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      FreshAsks (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p ok
        (roundsAt Zp Bs.G₀ p.place) cF.blocksInOrder fs σ B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) :=
  freshAsks_of_book h O hp D readers ok fs (book_at_switch h O hB hp he)

/-- **THE STATEMENT's END AT SUCH A SWITCH**, at the side that `Side.seated` lays at the place. A
law over coins. -/
theorem freshOf_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hp : p ∈ switchPlaces Zp Bs.G₀) (he : evenLink p = true) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (ok : Xi → Bool) (fs : List (Fall TS)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      Side.seated cF.blocksInOrder p.place (switchRow (coreSender freshTable) D readers
                 (lotClosing Zp Bs.G₀) p ok (roundsAt Zp Bs.G₀ p.place)) fs = some σ ∧
      FreshOf σ B (orderOf (F0T OnBytes.secondHashFunction Zp Np cF)) (switchBud p) :=
  freshOf_of_book h O hp D readers ok fs (book_at_switch h O hB hp he)

end AtFullSide.K2

#print axioms AtFullSide.K2.ownerTest_written
#print axioms AtFullSide.K2.book_at_switch
#print axioms AtFullSide.K2.freshAsks_at_switch
#print axioms AtFullSide.K2.freshOf_at_switch
