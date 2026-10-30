-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/CarriedAtTheBook.lean: UNDER THE LIBRARY's HEAD AND THE OPENING: AT WHATEVER BOOK
bookWhole (Johnson/Desc/ProofFile/Honest/BookWhole.lean) RETURNS AT F0T: AT EVERY SWITCH OF THE
PLAN, THE FIRST ENTRIES THAT THE BOOK CARRIES TO THE SWITCH's PART ARE THE OPENING's SENDING's
MESSAGES OF THE FIRST SEGMENT, NUMBER BY NUMBER: EACH NAMES THE OPENING's SENDER AS ITS OWNER, THE
START OF THAT MESSAGE's COINS AMONG THE SENDER's, AND THEIR COUNT: the public test `entryRunIs`
(Honest/Small/EntryRunIs.lean) says yes. By the writers of the merge of the claims on the weights
(sub-protocol K11), for the authors of K2's honest side. PUBLIC DATA ALONE: a book's entries,
addresses and counts. Three definitions: an address, a public test, and the written book's entries
carried to a place (for the controls). Lemmas; none of the library's goals. It lies in the side
library because it imports files of it.

Why. Two laws of K2's authors (`copyShared_first_by_test`, `copyShared_mask_by_test`,
Honest/K2/Law/CopySharedByTest.lean; this library may not hold it) take that test as a premise, ht,
at a book that is a letter: it was shown at no book. THEIR THIRD, `copyShared_later_by_test`, TAKES
ht AT A LATER SENDING's ENTRY: IT IS NOT SERVED HERE.

  `openingAddr`
      ⟨⟨1, some 0, 1, K1⟩, 0⟩: the opening's sender
  `openingCarried` es P ρ Sg p
      A PUBLIC TEST: for each number n below the count of the messages of Sg's first sending:
      `entryRunIs` at the entries of es that are carried to ⟨p.place, 0⟩ (`carryE`'s own text), at
      n, the address, `K1.startR` P ρ n and `K1.dueMsg` at P's message n
  `openingCarriedW`
      BY LEAN's KERNEL, at the written raw book's entries (`rawAheadW`,
      AtFullSide/K14/RawAheadWritten.lean, another group of authors'), the written opening
      (`parGF`, `qFull`), the written first segment and the 25 written places: that segment's
      first sending has four messages, and the test says yes at all 25
  `openingCarriedW_bent_e`, `_bent_f`, `_bent_count`, `_next`, `_other`
      FIVE CONTROLS, each over all 25 places and all four numbers: with the start bent by one coin
      of the extension field · of the base field · the count bent by one coin · at the entry one
      further · at another part's address: the test says yes NOWHERE: so its number and each of
      its three comparisons bite
  `ahead_at_book`
      what bookWhole returns at F0T has the written entries: by `rawBook_same`,
      `bookWhole_returns_raw`, `rawAhead_written` (theirs)
  `carried_opening_at_book`
      THE LAW: the head · the opening · the book · the first segment Sg · p of the plan · n below
      the count ⊢ the test's yes, AT THE HEAD's OWN LETTERS
  `carried_opening_at_zero`
      the same with the number written 0 + n

NEAR, another group of authors': `bookWhole_returns_written_ahead`
(AtFullSide/K14/BookWholeWritten.lean): there is a book that bookWhole returns at the written
description, with the written entries: `ahead_at_book` is its sister at F0T, at whatever book
returns.

WHAT IT IS NOT. It reads an entry's owner, start and count: not its name. Of the entries behind
these nothing is said: the later sendings' and the switches' own are not treated. THAT bookWhole
RETURNS AT F0T is not said here (it is said by `bookWhole_returns_at_head_of_written`, theirs). THE
MERGES ARE mergesByName's, WHICH THE FRAME's OWN TEXT CALLS A GUESS. ht's number is b₀ + n: that b₀
is 0 at the first segment is not said here; `carried_opening_at_zero` has the number written 0 + n,
as ht reads there. A statement on a public plan and book: nothing on a prover, a coin's value or a
run.

Limits. SIX CLOSED FACTS BY EVALUATION IN LEAN's KERNEL, five of them controls. The maker of the
carrying entries reads each message's link through String.splitOn and String.toNat?, which the
kernel does not unfold: it is led past them by the library's `Johnson.Unfolds.splitOn_eq` and
`slice_toNat?_eq`, in the three steps of another group of authors' `raw8_test`
(AtFullSide/K14/RawTwinEighth.lean). TWO OPTIONS ARE RAISED at each of the six: maxRecDepth to
1000000, maxHeartbeats to 0 (theirs; no lower number was tried). The full size; the format's second
hash function. All limits of RawAheadWritten.lean stand. Nothing on any property.
-/
import AtFullSide.K14.RawAtTheBookAtHead
import AtFullSide.K14.RawAheadWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexKeyWritten
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SliceFoldl
import AtFullSide.K2.CarriedWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF qFull firstPar gpOf)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace SegmentPub switchPlaces segmentsOf)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head segments_at_head)
open AtFullSide.K14 (rawAheadW rawSegW rawAhead_written rawBook_same bookWhole_returns_raw
  bookRaw_returns_written)

/-- The opening's sender. -/
def openingAddr : Addr := ⟨⟨1, some 0, 1, .K1⟩, 0⟩

/-- **A PUBLIC TEST**: the first entries of es that are carried to the switch's part are the
messages of Sg's first sending, number by number: owner, start and count. -/
def openingCarried (es : List Ahead) (P : VerifiableInference.Desc.K1.Par)
    (ρ : Nat → Option K1.Ride) (Sg : SegmentPub) (p : SwitchPlace) : Bool :=
  (List.range (Sg.sent.headD #[]).size).all fun n =>
    entryRunIs ((es.filter fun e => e.spender == ⟨p.place, 0⟩).filter fun e => !e.once) n
      openingAddr (K1.startR P ρ n) (K1.dueMsg P.codes (shapeAt P n) (ρ n))

/-- Tests that agree at each member of a list agree on the list. -/
theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- Tests that agree at each member of a list agree on the list. -/
theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

set_option maxRecDepth 1000000 in
/-- By Lean's kernel: the written switches are of the kind. -/
theorem placesW_kind : placesW.all (fun p => p.place.kind == VerifiableInference.Desc.KindName.K2) =
    true := by
  decide +kernel

/-- At a written switch the written book carries what the list says. -/
theorem carry_at_place {p : SwitchPlace} (hp : p ∈ placesW) :
    carryOf rawAheadW ⟨p.place, 0⟩ = carryOf carriedLitA ⟨p.place, 0⟩ :=
  carry_at_written (by simpa using List.all_eq_true.1 placesW_kind p hp) rfl

/-- The public test reads the written book as it reads the list. -/
theorem openingCarried_lit {P : VerifiableInference.Desc.K1.Par} {ρ : Nat → Option K1.Ride}
    {Sg : SegmentPub} {p : SwitchPlace} (hp : p ∈ placesW) :
    openingCarried rawAheadW P ρ Sg p = openingCarried carriedLitA P ρ Sg p := by
  have e := carry_at_place hp
  simp only [carryOf] at e
  simp only [openingCarried, e]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem openingCarriedLitW : ((segsW.take 1).all fun Sg =>
    decide ((Sg.sent.headD #[]).size = 4) &&
      placesW.all (openingCarried carriedLitA parGF (K1.rideOf (K1.firstFold qFull)) Sg)) = true ∧
    (segsW.take 1).length = 1 := by
  decide +kernel

/-- **At the written book's entries, the written opening, the written first segment and the 25
written places.** -/
theorem openingCarriedW : ((segsW.take 1).all fun Sg =>
    decide ((Sg.sent.headD #[]).size = 4) &&
      placesW.all (openingCarried rawAheadW parGF (K1.rideOf (K1.firstFold qFull)) Sg)) = true ∧
    (segsW.take 1).length = 1 := by
  refine ⟨?_, openingCarriedLitW.2⟩
  rw [← openingCarriedLitW.1]
  refine all_congr_mem fun Sg _ => ?_
  rw [all_congr_mem fun p hp => openingCarried_lit hp]

/-- The entries that the written book carries to a place. For the controls, which run over the
numbers below 4: the written first segment's first sending's size, by `openingCarriedW`. -/
def carriedW (p : SwitchPlace) : List Ahead :=
  (rawAheadW.filter fun e => e.spender == ⟨p.place, 0⟩).filter fun e => !e.once

/-- The entries that the list carries to a place. -/
def carriedLitW (p : SwitchPlace) : List Ahead := carryOf carriedLitA ⟨p.place, 0⟩

theorem carriedW_lit {p : SwitchPlace} (hp : p ∈ placesW) : carriedW p = carriedLitW p :=
  carry_at_place hp

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem openingCarriedW_bent_e_lit : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedLitW p) n openingAddr
      ⟨(K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).f,
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).e + 1⟩
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false := by
  decide +kernel

/-- A control: the start bent by one coin of the extension field: yes nowhere. -/
theorem openingCarriedW_bent_e : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedW p) n openingAddr
      ⟨(K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).f,
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).e + 1⟩
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false :=
  (any_congr_mem fun p hp => by rw [carriedW_lit hp]).trans openingCarriedW_bent_e_lit

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem openingCarriedW_bent_f_lit : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedLitW p) n openingAddr
      ⟨(K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).f + 1,
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).e⟩
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false := by
  decide +kernel

/-- A control: the start bent by one coin of the base field: yes nowhere. -/
theorem openingCarriedW_bent_f : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedW p) n openingAddr
      ⟨(K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).f + 1,
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).e⟩
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false :=
  (any_congr_mem fun p hp => by rw [carriedW_lit hp]).trans openingCarriedW_bent_f_lit

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem openingCarriedW_next_lit : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedLitW p) (n + 1) openingAddr
      (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false := by
  decide +kernel

/-- A control: the entry one further: yes nowhere. -/
theorem openingCarriedW_next : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedW p) (n + 1) openingAddr
      (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false :=
  (any_congr_mem fun p hp => by rw [carriedW_lit hp]).trans openingCarriedW_next_lit

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem openingCarriedW_other_lit : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedLitW p) n ⟨⟨1, some 0, 1, .K1⟩, 1⟩
      (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false := by
  decide +kernel

/-- A control: another part's address for the owner: yes nowhere. -/
theorem openingCarriedW_other : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedW p) n ⟨⟨1, some 0, 1, .K1⟩, 1⟩
      (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
      (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false :=
  (any_congr_mem fun p hp => by rw [carriedW_lit hp]).trans openingCarriedW_other_lit

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem openingCarriedW_bent_count_lit : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedLitW p) n openingAddr
      (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
      ⟨(K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n)).f,
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n)).e + 1⟩) =
      false := by
  decide +kernel

/-- A control: the count bent by one coin of the extension field: yes nowhere. -/
theorem openingCarriedW_bent_count : (placesW.any fun p => (List.range 4).any fun n =>
    entryRunIs (carriedW p) n openingAddr
      (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
      ⟨(K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n)).f,
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n)).e + 1⟩) =
      false :=
  (any_congr_mem fun p hp => by rw [carriedW_lit hp]).trans openingCarriedW_bent_count_lit

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- A list's first member is a member of its first one. (The like stands in a file of ours that is
not imported here: `mem_take_one`, Honest/K2/Law/K1SendersTies.lean.) -/
theorem head_mem_take_one {α : Type} {l : List α} {a : α} (h : l[0]? = some a) : a ∈ l.take 1 :=
  List.mem_of_getElem? (i := 0) (by rw [List.getElem?_take_of_lt (by omega)]; exact h)

/-- **What bookWhole returns at F0T has the written entries.** -/
theorem ahead_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    B.ahead = rawAheadW := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  rw [rawBook_same h.scope h.laid (bookWhole_returns_raw W hW) hB]
  exact rawAhead_written W hW

/-- THE HEAD, THE OPENING AND THE BOOK ARE PREMISES. **AT EVERY SWITCH OF THE PLAN THE BOOK's
CARRIED ENTRY NUMBER n IS THE OPENING's MESSAGE n: OWNER, START AND COUNT.** -/
theorem carried_opening_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {n : Nat}
    (hn : n < (Sg.sent.headD #[]).size) :
    entryRunIs (carryE B ⟨p.place, 0⟩) n openingAddr
      (K1.startR (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first)) n)
      (K1.dueMsg (firstPar Bs.G₀.first (gpOf Zp)).codes
        (shapeAt (firstPar Bs.G₀.first (gpOf Zp)) n)
        (K1.rideOf (K1.firstFold Bs.G₀.first) n)) = true := by
  rw [segments_at_head h.toAtMg O] at hS
  have hp' : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have k := List.all_eq_true.1 openingCarriedW.1 Sg (head_mem_take_one hS)
  obtain ⟨_, k2⟩ := Bool.and_eq_true_iff.1 k
  have t0 : ((List.range (Sg.sent.headD #[]).size).all fun n =>
      entryRunIs ((rawAheadW.filter fun e => e.spender == ⟨p.place, 0⟩).filter fun e => !e.once) n
        openingAddr (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = true :=
    List.all_eq_true.1 k2 p hp'
  rw [ProofFile.Honest.K11.par_at_head h O, ProofFile.Honest.K11.fold_at_head h O]
  unfold carryE
  rw [ahead_at_book h hB]
  exact List.all_eq_true.1 t0 n (List.mem_range.2 hn)

/-- The same with the number written 0 + n: the form in which the premise ht of K2's authors' two
laws reads at b₀ := 0. -/
theorem carried_opening_at_zero (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {n : Nat}
    (hn : n < (Sg.sent.headD #[]).size) :
    entryRunIs (carryE B ⟨p.place, 0⟩) (0 + n) openingAddr
      (K1.startR (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first)) n)
      (K1.dueMsg (firstPar Bs.G₀.first (gpOf Zp)).codes
        (shapeAt (firstPar Bs.G₀.first (gpOf Zp)) n)
        (K1.rideOf (K1.firstFold Bs.G₀.first) n)) = true := by
  rw [Nat.zero_add]
  exact carried_opening_at_book h O hB hS hp hn

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.openingAddr
#print axioms AtFullSide.K2.openingCarried
#print axioms AtFullSide.K2.openingCarriedW
#print axioms AtFullSide.K2.carriedW
#print axioms AtFullSide.K2.openingCarriedW_bent_e
#print axioms AtFullSide.K2.openingCarriedW_bent_f
#print axioms AtFullSide.K2.openingCarriedW_next
#print axioms AtFullSide.K2.openingCarriedW_other
#print axioms AtFullSide.K2.openingCarriedW_bent_count
#print axioms AtFullSide.K2.head_mem_take_one
#print axioms AtFullSide.K2.ahead_at_book
#print axioms AtFullSide.K2.carried_opening_at_book
#print axioms AtFullSide.K2.carried_opening_at_zero
