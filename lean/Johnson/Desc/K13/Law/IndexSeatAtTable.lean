-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/IndexSeatAtTable.lean: THE DOOR's ITEM "K12.seatsCarried" AT KIND K13's BLOCK
AND AT W's COMMITMENT: what it gives there (the index masks' seat, read off the promise of the
table of joints), and that it holds behind each of the two. Statements with their proofs. Why.
`FillM3.det` (Johnson/Desc/K13/Law/AtTable.lean) is false at a reader that goes from a message's
number to a tenant by the chain state's own book, unless the promise gives that by the book the
index masks' message sits at `N.index`. And `FillM4.pubRide` (AtTableW.lean) would be false at
this item over a bare step: W's commitment SENDS: the item is earned there. Main names:
  `seatsItem`: the door's item "K12.seatsCarried" (Johnson/Desc/K12/Door/Door.lean: K12's
    files' filling); its meant sentence: `K12.Coin.seatsPrefixB L` at the chain state's book
    (Johnson/Desc/K12/Coin/BookRides.lean).
  `seat_in_hand`: FROM WHAT `det` IS HANDED (the Bool of every public item open in front;
    `indexIs`; `indexThere`; `bookAt` at some place), UNDER FIVE PREMISES MORE: the item is among
    the open ones; the three sentences say at least `seatsPrefixB L`, `K1.indexIsB N.indexNo`,
    `K1.indexThereB`; the plan's list L has `N.index` at `N.indexNo`: `K1.indexSeatB N.index` says
    yes.
  `promise_seat`: so off the promise in front, at a state of the chain without a mark.
  `seats_ride_M3`: K13's block leaves the book: the sentence rides over a bare step.
  `core_same_M3`: it leaves the count of roots too.
  `seats_ride_M4`: **W's commitment earns it**: from the sentence in front, `bookAt` AT THE BLOCK's
    OWN PLACE, and two equations on the plan (from `N.msgsAt p` | `N.treesAt p` on the plan's lists
    go on with what the place lays): by `K1.SeatedBy.seatsRide`.
  `k13Asks` (Johnson/Desc/K13/Law/AsksDoor.lean): K13's block and W's commitment ASK the item: so
    that the table's own test on a filling guards it. THE TESTS ON THE TABLE AT MERGED FILLINGS OF
    THE DOOR STAND IN LEAF FILES (AtOurMore.lean, AtDoorSix.lean: neither is in this library): a
    change of the door in other files cannot make a law's file fail to compile.

What is not claimed. A member of `FillM3` | `FillM4` (`det`: Johnson/Desc/K13/Law/DetByBook.lean).
That a filling's sentences are these. The equations on the plan:
none has a test that has run by Lean; L is tied to no plan here. That the blocks in front of K13's
earn or keep the item. The riding of "K12.bookInOrder" at W's commitment (it wants ft = the place's
first tree). WHICH WAY THE WITNESS's ACCESSOR GOES: if from a seat to a number, `det` wants the
book's other table (a tree's parts), which this item does not hold. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtTableW
import Johnson.Desc.K1.Law.IndexSeatCarried
import Johnson.Desc.K1.Law.SeatsRideK1
import Johnson.Desc.K13.Law.SeatedJoined
import Johnson.Desc.K13.Law.AsksDoor
import Johnson.Desc.K12.Door.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.Sound (Frame onQ)

/-- The door's item "K12.seatsCarried". -/
def seatsItem : Pub := First.moreItem K12.Door.nSeats

section
variable {A Pp W : Type} {Fr : Frame}

/-- **From what `FillM3.det` is handed**, under five premises more. -/
theorem seat_in_hand (N : Numbers) (Mg : Meaning Pp W) (L : K12.Coin.Laid) (Q : List Pub)
    (hopen : seatsItem ∈ Q)
    (hS : ∀ x, Mg.pub seatsItem x = true → K12.Coin.seatsPrefixB L x.2.book = true)
    (hI : ∀ x, Mg.pub .indexIs x = true → K1.indexIsB N.indexNo x.2 = true)
    (hT : ∀ x, Mg.pub .indexThere x = true → K1.indexThereB x.2 = true)
    (hL : L.places[N.indexNo]? = some N.index) (x : Pp × S) (p : Option Place)
    (hQ : ∀ q ∈ Q, Mg.pub q x = true) (hii : Mg.pub .indexIs x = true)
    (hit : Mg.pub .indexThere x = true) (hbk : First.bookAt N p x.2 = true) :
    K1.indexSeatB N.index x.2 = true := by
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  exact K1.indexSeat_of_carried ((K12.Coin.seatsPrefix_iff L _).1 (hS x (hQ _ hopen))) hbk.1.2
    (hT x hit) (hI x hii) hL

/-- **Off the promise in front**, at a state of the chain without a mark. -/
theorem promise_seat (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (L : K12.Coin.Laid) (hp : Item.pinI ∈ openAt links ps k)
    (hopen : seatsItem ∈ (First.pubSets Mg.more links ps)[k]?.getD [])
    (hS : ∀ x, Mg.pub seatsItem x = true → K12.Coin.seatsPrefixB L x.2.book = true)
    (hI : ∀ x, Mg.pub .indexIs x = true → K1.indexIsB N.indexNo x.2 = true)
    (hT : ∀ x, Mg.pub .indexThere x = true → K1.indexThereB x.2 = true)
    (hL : L.places[N.indexNo]? = some N.index) (a : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) :
    K1.indexSeatB N.index (get a.1).2 = true := by
  obtain ⟨hii, hit, hbk, hQ⟩ := promise_index N Mg links ps get k hp a ha hm
  exact seat_in_hand N Mg L _ hopen hS hI hT hL _ _ (fun q hq => (hQ q hq).1) hii hit hbk

/-- K13's block leaves the book and the count of roots. -/
theorem core_same_M3 {Cl : Type} {P : Where} {x x' : Pp × S} (h : StepM3 Cl P x x') :
    x'.2.book = x.2.book ∧ x'.2.roots = x.2.roots := by
  obtain ⟨rs, gs, hd⟩ := h.2
  obtain ⟨_, _, _, _, e⟩ := atM3_rec hd
  rw [e]
  exact ⟨rfl, rfl⟩

/-- The sentence rides over a bare step of K13's block. -/
theorem seats_ride_M3 {Cl : Type} {P : Where} {x x' : Pp × S} (L : K12.Coin.Laid)
    (h : StepM3 Cl P x x') (h0 : K12.Coin.seatsPrefixB L x.2.book = true) :
    K12.Coin.seatsPrefixB L x'.2.book = true := by
  rw [(core_same_M3 h).1]
  exact h0

/-- **W's commitment earns it.** p: the block's own place. -/
theorem seats_ride_M4 {Cl : Type} {P : Where} {P' : K1.Par} {x x' : Pp × S} (N : Numbers)
    (p : Option Place) (L : K12.Coin.Laid) (h : StepM4 Cl P P' x x')
    (h0 : K12.Coin.seatsPrefixB L x.2.book = true) (hbk : First.bookAt N p x.2 = true)
    (hp : (L.places.drop (N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (N.treesAt p) P'.sent.size (K1.layOf P'))
    (hs : (L.shapes.drop (N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList) :
    K12.Coin.seatsPrefixB L x'.2.book = true := by
  obtain ⟨r₁, r₂, gs, hdec⟩ := h.decide
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  obtain ⟨⟨b1, b2⟩, b3⟩ := hbk
  refine (K12.Coin.seatsPrefix_iff L _).2 ((atM4_seated hdec).seatsRide
    ((K12.Coin.seatsPrefix_iff L _).1 h0) ?_ ?_)
  · rw [b2, b3, b1]
    exact hp
  · rw [b1]
    exact hs

end

end VerifiableInference.Desc.K13.Law
