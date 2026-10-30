-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/CopyBookAtPair.lean: the kind "the code switch" (K2): THE BOOK's FIVE PREMISES OF THE
TIE AT A KEPT COPY, PAID: `ownMsgs_copy_at_pair`
(Johnson/Desc/ProofFile/Honest/K2/Law/OwnMsgsAtPair.lean) asks of the book, at a written pair (p₀,
p, S) and a kept copy i of p: hT: what p₀ carries, p carries too, place by place, from the same
owner, start and count · he, t1, t2, t3: at a named place of what p carries stands an entry whose
owner is p₀, whose start is the count of p₀'s messages in front of message n, and whose count is
that message's own. HERE: AT WHATEVER BOOK bookWhole RETURNS AT F0T, UNDER THE LIBRARY's HEAD, ALL
FIVE HOLD; and two public premises of that law beside them: hc (one list of codes) and hw (every
message of p with a main row is sampled). It lies in the side library because it imports files of
it. Four definitions: a list of public entries and three public tests; two closed facts by
evaluation in Lean's kernel, the first with a control; lemmas. ONE OPTION IS RAISED: maxHeartbeats 0
at `copyPairsOkW`, for the rewriting of the labels' reader in front of the kernel's evaluation.

  `carW`            what the maker's second text `segmentCarriesAt` (Honest/BookCarryKit.lean, of
                    other authors) lays for a switch's first part to carry, at the written
                    description and its written messages
  `alikeFront`, `alikeFront_gives`   A PUBLIC TEST on two lists of entries: the first is, place by
                    place, the front of the second, by owner, start and count; what a yes gives
  `copyEntryOk`     A PUBLIC TEST at a pair and a kept copy: the entry that he, t1, t2, t3 ask for
  `copyPairOk`, `copyPairsOkW`   the two tests, hc and hw at a pair; BY LEAN's KERNEL: they pass at
                    every written pair; A CONTROL: with the two switches of each pair swapped they
                    pass at none
  `switchThereW`    BY LEAN's KERNEL: each written place stands in the written first chain
  `carry_at_book`   UNDER THE HEAD, AT THE BOOK: what a written switch's first part carries is
                    `carW`
  `book_five_at_pair`   THE END: the five, hc and hw, in the law's own forms

By, of other authors, sealed: `bookWhole_carries` (Honest/BookCarryKit.lean) ·
`sentIn_first_written` (Honest/BookWritten/SentFirst.lean) · `wp_placesOk`
(Johnson/AtFull/ProofPlan/At/PlacesOk.lean) · `bookRaw_returns_written`, `bookWhole_returns_raw`,
`rawBook_same` (AtFullSide/K14/) · the way of evaluating over labels: the library's `splitOn_eq`,
`slice_toNat?_eq` (Johnson/Unfolds/). Ours: `copyPairs_mem` (Honest/K2/Law/CopyPairsMem.lean) ·
`noWord_yes` (Honest/K2/Law/Counts.lean).

Limits. PUBLIC DATA ALONE: owners, starts, counts: WHOSE COINS AND FROM WHICH COIN ON, not what a
coin is for. Nothing on a run, a Script or a tie: `ownMsgs_copy_at_pair` is not called here, and its
hm₀, hNN, hrun and hSz stay unpaid. ONE STEP BACK. The two copies at link 1 stand at no pair. THE
MERGES ARE mergesByName's, which the frame's own text calls a guess. That a thread's book is what
bookWhole returns at F0T is not said. The full size and the format's second hash function alone. The head
and the book are premises; that they can be met is not said. Nothing on any property.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawAtTheBookAtHead
import Johnson.Desc.ProofFile.Honest.BookCarryKit
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import Johnson.AtFull.ProofPlan.At.PlacesOk
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyPairsMem
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (keptNo)
open P2Law.ProofPlan (WP wp_placesOk)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K2 (SwitchPlace SegmentPub switchSent switchFresh messageDue foldAt dueBefore
  NoWord noWord noWord_yes)
open ProofFile.Honest.K2.Law (placesW segsW copyPairs copyPairs_mem membersOfSeg)
open AtFullSide.K14 (bookRaw_returns_written bookWhole_returns_raw rawBook_same)

/-- What `segmentCarriesAt` lays for a switch's first part to carry, at the written description and
its written messages. -/
def carW (p : SwitchPlace) : List Ahead :=
  segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW ⟨p.place, 0⟩

/-- **A PUBLIC TEST**: the first list is, place by place, the front of the second, by owner, start
and count. -/
def alikeFront : List Ahead → List Ahead → Bool
  | [], _ => true
  | _ :: _, [] => false
  | e₀ :: l₀, e :: l =>
    (e.owner == e₀.owner && e.start == e₀.start && e.count == e₀.count) && alikeFront l₀ l

/-- What a yes gives. -/
theorem alikeFront_gives : ∀ (l₀ l : List Ahead), alikeFront l₀ l = true →
    ∀ (a : Nat) (e₀ : Ahead), l₀[a]? = some e₀ →
      ∃ e, l[a]? = some e ∧ e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count
  | [], _, _, a, e₀, h0 => by simp at h0
  | _ :: _, [], h, _, _, _ => by cases h
  | x₀ :: l₀, x :: l, h, 0, e₀, h0 => by
    unfold alikeFront at h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    rw [List.getElem?_cons_zero] at h0
    obtain rfl := Option.some.inj h0
    exact ⟨x, List.getElem?_cons_zero, beq_iff_eq.1 h.1.1.1, beq_iff_eq.1 h.1.1.2,
      beq_iff_eq.1 h.1.2⟩
  | x₀ :: l₀, x :: l, h, a + 1, e₀, h0 => by
    unfold alikeFront at h
    rw [Bool.and_eq_true] at h
    rw [List.getElem?_cons_succ] at h0
    obtain ⟨e, h1, h2⟩ := alikeFront_gives l₀ l h.2 a e₀ h0
    exact ⟨e, by rw [List.getElem?_cons_succ]; exact h1, h2⟩

/-- **A PUBLIC TEST** at a pair and a kept copy i of its second switch: at the place that the law
names, what the second switch carries has an entry whose owner is the first switch, whose start is
the count of that switch's messages in front of message n, and whose count is that message's. -/
def copyEntryOk (x : SwitchPlace × SwitchPlace × SegmentPub) (i : Nat) : Bool :=
  match (carW x.2.1)[0 + ((segsW.take x.1.link).map (·.messages)).sum +
      keptNo (membersOfSeg x.2.2 true) i]? with
  | some e =>
    e.owner == ⟨x.1.place, 0⟩ &&
      e.start == dueBefore x.1.sizes.codes (switchSent x.1.sizes x.1.others)
        (switchFresh x.1.sizes x.1.others x.1.foldVars) (keptNo (membersOfSeg x.2.2 true) i) &&
      e.count == messageDue x.1.sizes.codes
        ((switchSent x.1.sizes x.1.others).getD (keptNo (membersOfSeg x.2.2 true) i) default).shape
        (foldAt (switchFresh x.1.sizes x.1.others x.1.foldVars)
          (keptNo (membersOfSeg x.2.2 true) i))
  | none => false

/-- **A PUBLIC TEST** at a pair: the two tests above, one list of codes, and every message of the
second switch with a main row is sampled. -/
def copyPairOk (x : SwitchPlace × SwitchPlace × SegmentPub) : Bool :=
  alikeFront (carW x.1) (carW x.2.1) &&
    (List.range x.2.1.sizes.kept.length).all (copyEntryOk x) &&
    decide (x.1.sizes.codes = x.2.1.sizes.codes) &&
    noWord (switchSent x.2.1.sizes x.2.1.others)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At every written pair the test passes**; a control: with the two switches of each pair swapped
it passes at none. -/
theorem copyPairsOkW :
    copyPairs.all copyPairOk = true ∧
      (copyPairs.any fun x => copyPairOk (x.2.1, x.1, x.2.2)) = false := by
  unfold copyPairOk copyEntryOk carW segmentCarriesAt linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each written place stands in the written first chain. -/
theorem switchThereW :
    (placesW.all fun p => (WP.first.blocksInOrder.map (·.place)).contains p.place) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts}

/-- **UNDER THE HEAD, AT THE BOOK: WHAT A WRITTEN SWITCH's FIRST PART CARRIES IS `carW`.** -/
theorem carry_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {p : SwitchPlace} (hp : p ∈ placesW) :
    ((B.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once)) = carW p := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  have hWP := bookWhole_returns_raw W hW
  obtain rfl : B = W := rawBook_same h.scope h.laid hWP hB
  obtain ⟨m0, hm, e⟩ := bookWhole_carries hWP wp_placesOk (a := ⟨p.place, 0⟩)
    (List.contains_iff_mem.1 (List.all_eq_true.1 switchThereW p hp))
  obtain rfl : sentFirstW = m0 := Except.ok.inj (sentIn_first_written.symm.trans hm)
  exact e

/-- **THE END: UNDER THE HEAD, AT THE BOOK, AT A WRITTEN PAIR AND A KEPT COPY: THE BOOK's FIVE, AND
hc AND hw**, in the forms in which `ownMsgs_copy_at_pair` asks them. PUBLIC DATA ALONE: owners,
starts and counts. -/
theorem book_five_at_pair (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {p₀ p : SwitchPlace} {S : SegmentPub} (hx : (p₀, p, S) ∈ copyPairs) {i n : Nat}
    (hi : i < p.sizes.kept.length) (hnn : n = keptNo (membersOfSeg S true) i) :
    (∀ (a : Nat) (e₀ : Ahead),
      ((B.ahead.filter fun x => x.spender == ⟨p₀.place, 0⟩).filter (!·.once))[a]? = some e₀ →
      ∃ e, ((B.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[a]? = some e ∧
        e.owner = e₀.owner ∧ e.start = e₀.start ∧ e.count = e₀.count) ∧
      (∃ e, ((B.ahead.filter fun x => x.spender == ⟨p.place, 0⟩).filter (!·.once))[
          0 + ((segsW.take p₀.link).map (·.messages)).sum + n]? = some e ∧
        e.owner = ⟨p₀.place, 0⟩ ∧
        e.start = dueBefore p₀.sizes.codes (switchSent p₀.sizes p₀.others)
          (switchFresh p₀.sizes p₀.others p₀.foldVars) n ∧
        e.count = messageDue p₀.sizes.codes
          ((switchSent p₀.sizes p₀.others).getD n default).shape
          (foldAt (switchFresh p₀.sizes p₀.others p₀.foldVars) n)) ∧
      p₀.sizes.codes = p.sizes.codes ∧ NoWord (switchSent p.sizes p.others) := by
  obtain ⟨m1, m2, -, -⟩ := copyPairs_mem hx
  have t := List.all_eq_true.1 copyPairsOkW.1 _ hx
  unfold copyPairOk at t
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at t
  obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := t
  rw [carry_at_book h hB m1, carry_at_book h hB m2]
  refine ⟨alikeFront_gives _ _ t1, ?_, of_decide_eq_true t3, noWord_yes t4⟩
  have u := List.all_eq_true.1 t2 i (List.mem_range.2 hi)
  unfold copyEntryOk at u
  subst hnn
  split at u
  · rename_i e he
    rw [Bool.and_eq_true, Bool.and_eq_true] at u
    exact ⟨e, he, beq_iff_eq.1 u.1.1, beq_iff_eq.1 u.1.2, beq_iff_eq.1 u.2⟩
  · cases u

end AtFullSide.K2

#print axioms AtFullSide.K2.carW
#print axioms AtFullSide.K2.alikeFront
#print axioms AtFullSide.K2.alikeFront_gives
#print axioms AtFullSide.K2.copyEntryOk
#print axioms AtFullSide.K2.copyPairOk
#print axioms AtFullSide.K2.copyPairsOkW
#print axioms AtFullSide.K2.switchThereW
#print axioms AtFullSide.K2.carry_at_book
#print axioms AtFullSide.K2.book_five_at_pair
