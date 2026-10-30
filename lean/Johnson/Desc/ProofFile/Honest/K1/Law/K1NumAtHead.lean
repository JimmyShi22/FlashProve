-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1NumAtHead.lean: THE SHARED "SENDING" (the kind K1): WHICH
NUMBER OF THE WITNESS's MESSAGES, AND WHICH SEAT OF THE PLAN's OWN LIST, MESSAGE NUMBER n OF A
PLACE's SENDING HAS: AT THE OPENING (number 2 of the first chain) AND AT EACH OF THE FIFTY LATER
SENDINGS, UNDER THE LIBRARY's HEAD. PUBLIC DATA ALONE: plans, the plan's list of seats, numbers:
which message, never what stands in it. Two definitions with code; twenty-two theorems.


The two readings.
  - k1Num Zp bs b P n := P5J.At.arr Zp at seatAtMember bs b P n: the seat off the chain's blocks and
    the plan's laying (Honest/K1/Seated.lean). IT IS THE RECORD's OWN TERM in its field msgs at arr
    := P5J.At.arr Zp: k1Num_is, by rfl: meant as the letter "num" of the lots of msgTxt.
  - k1SeatIn ps send idx: the seat (tree, tenant) of the first member of a plan's list of seats with
    that sending's number and that place in the sending; none where there is none.

The road. Under the head the plan's list of all three chains' seats is the library's written
seatsAllFull (pseatsAll_written: seats_in_scope, Johnson/P5T/PlanSeatsTie.lean), and our seat is the
written plan's behind the written number of trees (seat_two_written, seat_fifty_written). At these
constants all is closed facts, evaluated in Lean's kernel.

  - seatW2, seatW50: AT EVERY MESSAGE OF THE PLAN, SAMPLED OR NOT: the written list filtered at our
    seat is ONE seat: member number n of sending number 0 (the opening), 3 l + 1 ("reads"), 3 l + 2
    ("digits"), of the message's shape; at the fifty its key is an own message's of link l. backW2,
    backW50: the other way: the list filtered at (sending, place) is one seat, and it is ours.
    keysW2: the opening's five keys: (0, 0, 0), (0, 0, 1), (0, 0, 2): by keyOf's text own or kept
    messages of link 0; (1, 0, 3), (1, 0, 4): by sending and place: no link's own message. It says
    the keys alone. indexW: number 4 alone sits at (1, 0).
  - seatW2_bites, seatW50_bites: NEGATIVE TESTS: one tree further the test says no: at each message
    of the opening; at each of the fifty.
  - one_of_filter, one_of_test: general: a list whose filter is [p]: p is there, alone, and find?
    hits it.
  - seat_two, seat_fifty: UNDER h (the library's head: A HYPOTHESIS), O (the description opened), n
    below the plan's number of messages (and hl : l < 25): JUST ONE SEAT p OF P5J.At.pseatsAll Zp
    STANDS AT OUR SEAT, with p.send, p.idx = n, p.shape.
  - seatIn_two, seatIn_fifty: under the same: THE TWO READINGS ARE ONE: k1SeatIn (P5J.At.pseatsAll
    Zp) ‹the sending› n = some ‹our seat›.
  - k1Num_of_one: where just one seat p stands at our seat, k1Num is the place of p's key among the
    keys: arrOf does not fall "beyond the list" (arrOf_of_find, Johnson/P5T/NumOfPlan.lean).
  - k1Num_fifty: at the fifty k1Num is P5J.At.num Zp l k for some k (arrOf_is_num).
  - index_two, k1Num_index: AT THE OPENING MESSAGE NUMBER 4 SITS AT THE TABLE's N.index: so k1Num
    there is P5J.At.arr Zp N.index.1 N.index.2.

Kin in the library. arrOf_all (Johnson/P5T/ArrAll.lean): at every seat of the first chain the
numbering over all three chains' seats is the first chain's. arrOf_key (Johnson/P5T/ArrApart.lean),
arrOf_same_key (Johnson/P5T/KeptAlign.lean).

Limits. 51 PLACES: W's sending is not here. THE FULL SIZE ALONE. THE PLAN IS THE DESCRIPTION's
GROUND's: that it is the plan of the prover that a filling makes is another file's
(RecordAtWider.lean). Nothing is said of the Script: that its message at this number is our text is
the record's field msgs: a premise. Evaluations in Lean's kernel (decide +kernel): no compiled code.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtFifty
import Johnson.P5T.NumOfPlan
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (parGF seatOfMsg placeL baseL3 momL fiftyB fifty_of)
open P5T (PSeat seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)
open IM (k1Ix)

/-! ## 1 The two readings -/

/-- **The witness's number of the place's message number n at the member number b**: the table's
number at our seat: the record's own term in its field msgs. -/
def k1Num {Cl : Type} (Zp : ProofFile.Pub) (bs : List (Block S Cl)) (b : ℕ) (P : K1.Par) (n : ℕ) : ℕ :=
  P5J.At.arr Zp (seatAtMember bs b P n).1 (seatAtMember bs b P n).2

/-- **The seat read off a plan's list of seats**, by the sending's number and the member's place in
it; none where the list has no such member. -/
def k1SeatIn (ps : List PSeat) (send idx : ℕ) : Option (ℕ × ℕ) :=
  (ps.find? fun p => p.send == send && p.idx == idx).map fun p => (p.j, p.t)

/-- The record's term is k1Num. -/
theorem k1Num_is {Cl : Type} (Zp : ProofFile.Pub) (bs : List (Block S Cl)) (b : ℕ) (P : K1.Par) (n : ℕ) :
    P5J.At.arr Zp (seatAtMember bs b P n).1 (seatAtMember bs b P n).2 = k1Num Zp bs b P n := rfl

/-- A list whose filter is one element: it is there, alone, and find? hits it. General. -/
theorem one_of_filter {α : Type} {l : List α} {q : α → Bool} {p : α} (h : l.filter q = [p]) :
    p ∈ l ∧ q p = true ∧ (∀ p' ∈ l, q p' = true → p' = p) ∧ l.find? q = some p := by
  have hm : p ∈ l.filter q := by rw [h]; exact List.mem_singleton.2 rfl
  refine ⟨(List.mem_filter.1 hm).1, (List.mem_filter.1 hm).2, fun p' h1 h2 => ?_, ?_⟩
  · have : p' ∈ l.filter q := List.mem_filter.2 ⟨h1, h2⟩
    rw [h] at this
    exact List.mem_singleton.1 this
  · rw [← List.head?_filter, h]
    rfl

/-- From the closed test's form. General. -/
theorem one_of_test {α : Type} {l : List α} {f : α → Bool}
    (h : (decide (l.length = 1) && l.all f) = true) : ∃ p, l = [p] ∧ f p = true := by
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 h.1
  exact ⟨p, rfl, List.all_eq_true.1 h.2 p (List.mem_singleton.2 rfl)⟩

/-! ## 2 At the written constants -/

/-- AT THE OPENING's WRITTEN PLAN, AT EVERY MESSAGE, SAMPLED OR NOT: the written list of all three
chains' seats has just one seat at our seat: member number n of sending number 0, of the message's
shape. -/
theorem seatW2 : ((List.range parGF.sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2).length = 1) &&
      (seatsAllFull.filter fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2).all fun p =>
          p.send == 0 && p.idx == n && decide (p.shape = shapeAt parGF n)) = true := by
  decide +kernel

/-- The other way: the list has just one member number n of sending number 0, and it sits at our
seat. -/
theorem backW2 : ((List.range parGF.sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.send == 0 && p.idx == n).length = 1) &&
      (seatsAllFull.filter fun p => p.send == 0 && p.idx == n).all fun p =>
        decide ((p.j, p.t) = seatOfMsg parGF 0 n)) = true := by
  decide +kernel

/-- The keys at the opening: three of link 0's messages; two by sending and place. -/
theorem keysW2 : (List.range parGF.sent.size).map (fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
      p.t == (seatOfMsg parGF 0 n).2).map keyOf) =
    [some (0, 0, 0), some (0, 0, 1), some (0, 0, 2), some (1, 0, 3), some (1, 0, 4)] := by
  decide +kernel

/-- The one message of the opening whose seat is (1, 0) is number 4. -/
theorem indexW : (List.range parGF.sent.size).filter
    (fun n => decide (seatOfMsg parGF 0 n = (1, 0))) = [4] := by
  decide +kernel

/-- The like at each of the fifty: sending number 3 l + 1 ("reads") or 3 l + 2 ("digits"); the key
is an own message's of link l. -/
theorem seatW50 : fiftyB (fun l d => (List.range (placeL l d).sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2).length = 1) &&
      (seatsAllFull.filter fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2).all fun p =>
          p.send == 3 * l + momL d && p.idx == n && decide (p.shape = shapeAt (placeL l d) n) &&
            (keyOf p).1 == 0 && (keyOf p).2.1 == l) = true := by
  decide +kernel

/-- The other way, at each of the fifty. -/
theorem backW50 : fiftyB (fun l d => (List.range (placeL l d).sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.send == 3 * l + momL d && p.idx == n).length = 1) &&
      (seatsAllFull.filter fun p => p.send == 3 * l + momL d && p.idx == n).all fun p =>
        decide ((p.j, p.t) = seatOfMsg (placeL l d) (baseL3 l d) n)) = true := by
  decide +kernel

/-- A negative test: at the opening, one tree further, at EACH message the test says no. -/
theorem seatW2_bites : ((List.range parGF.sent.size).all fun n =>
    !(decide ((seatsAllFull.filter fun p => p.j == (seatOfMsg parGF 1 n).1 &&
        p.t == (seatOfMsg parGF 1 n).2).length = 1) &&
      (seatsAllFull.filter fun p => p.j == (seatOfMsg parGF 1 n).1 &&
        p.t == (seatOfMsg parGF 1 n).2).all fun p =>
          p.send == 0 && p.idx == n && decide (p.shape = shapeAt parGF n))) = true := by
  decide +kernel

/-- A negative test: AT EACH OF THE FIFTY, one tree further, the test says no. -/
theorem seatW50_bites : fiftyB (fun l d => !((List.range (placeL l d).sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d + 1) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d + 1) n).2).length = 1) &&
      (seatsAllFull.filter fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d + 1) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d + 1) n).2).all fun p =>
          p.send == 3 * l + momL d && p.idx == n && decide (p.shape = shapeAt (placeL l d) n) &&
            (keyOf p).1 == 0 && (keyOf p).2.1 == l)) = true := by
  decide +kernel

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- Under the head the plan's list of all three chains' seats is the written one. -/
theorem pseatsAll_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    P5J.At.pseatsAll Zp = seatsAllFull :=
  (P5T.seats_in_scope h.scope h.laid.pub (K1.pin1_atAll h) (K1.laidP_atAll h)).2.1

/-- Our seat at number 2 is the written plan's, behind no tree. -/
theorem seat_two_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (n : ℕ) :
    seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n = seatOfMsg parGF 0 n := by
  unfold seatAtMember
  rw [trees_two h O (treesNo_atN Zp cF (show P5J.At.ps[2]? = some _ from placeW)),
    K1.eG_atAll h O (K1.pin1_atAll h)]

/-- Our seat at each of the fifty is the written plan's, behind baseL3 l d trees. -/
theorem seat_fifty_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) (n : ℕ) :
    seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n = seatOfMsg (placeL l d) (baseL3 l d)
        n := by
  unfold seatAtMember
  rw [(nums_fifty h O hl d).2, parL_written h O l d]

/-- **AT NUMBER 2, AT EVERY MESSAGE OF THE PLAN, SAMPLED OR NOT: JUST ONE SEAT OF THE PLAN's LIST
STANDS AT OUR SEAT**: member number n of sending number 0, of the message's shape. -/
theorem seat_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) :
    ∃ p, ((P5J.At.pseatsAll Zp).filter fun p =>
        p.j == (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1 &&
          p.t == (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2) = [p] ∧
      p.send = 0 ∧ p.idx = n ∧ p.shape = shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n := by
  rw [seat_two_written h O n, pseatsAll_written h]
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn ⊢
  obtain ⟨p, e, hp⟩ := one_of_test (List.all_eq_true.1 seatW2 n (List.mem_range.2 hn))
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨p, e, hp.1.1, hp.1.2, hp.2⟩

/-- **THE OTHER READING AT NUMBER 2**: the seat read off the plan's list, by the sending and the
member's place in it, is our seat. -/
theorem seatIn_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) :
    k1SeatIn (P5J.At.pseatsAll Zp) 0 n =
      some (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n) := by
  rw [seat_two_written h O n, pseatsAll_written h]
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn
  obtain ⟨p, e, hp⟩ := one_of_test (List.all_eq_true.1 backW2 n (List.mem_range.2 hn))
  unfold k1SeatIn
  rw [(one_of_filter e).2.2.2, Option.map_some, of_decide_eq_true hp]

/-- **THE LIKE AT EACH OF THE FIFTY**; the seat's key is an own message's of link l. -/
theorem seat_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) :
    ∃ p, ((P5J.At.pseatsAll Zp).filter fun p =>
        p.j == (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).1 &&
          p.t == (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).2) = [p] ∧
      p.send = 3 * l + momL d ∧ p.idx = n ∧ p.shape = shapeAt (K1.parL Zp Bs.G₀ l d) n ∧
      ∃ k, keyOf p = (0, l, k) := by
  rw [seat_fifty_written h O hl d n, pseatsAll_written h]
  rw [parL_written h O l d] at hn ⊢
  obtain ⟨p, e, hp⟩ := one_of_test
    (List.all_eq_true.1 (fifty_of seatW50 l hl d) n (List.mem_range.2 hn))
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq,
    beq_iff_eq, decide_eq_true_eq, beq_iff_eq, beq_iff_eq] at hp
  exact ⟨p, e, hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, (keyOf p).2.2,
    Prod.ext hp.1.2 (Prod.ext hp.2 rfl)⟩

/-- **THE OTHER READING AT EACH OF THE FIFTY.** -/
theorem seatIn_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) :
    k1SeatIn (P5J.At.pseatsAll Zp) (3 * l + momL d) n =
      some (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n) := by
  rw [seat_fifty_written h O hl d n, pseatsAll_written h]
  rw [parL_written h O l d] at hn
  obtain ⟨p, e, hp⟩ := one_of_test
    (List.all_eq_true.1 (fifty_of backW50 l hl d) n (List.mem_range.2 hn))
  unfold k1SeatIn
  rw [(one_of_filter e).2.2.2, Option.map_some, of_decide_eq_true hp]

/-- **THE NUMBER DOES NOT FALL BEYOND THE LIST**: where just one seat p of the plan's list stands at
our seat, k1Num is the place of p's key among the keys. General in the member. -/
theorem k1Num_of_one {b : ℕ} {P : K1.Par} {n : ℕ} {p : PSeat}
    (e : ((P5J.At.pseatsAll Zp).filter fun p => p.j == (seatAtMember cF.blocksInOrder b P n).1 &&
      p.t == (seatAtMember cF.blocksInOrder b P n).2) = [p]) :
    k1Num Zp cF.blocksInOrder b P n =
      (((P5J.At.pseatsAll Zp).map keyOf).eraseDups).idxOf (keyOf p) :=
  P5T.arrOf_of_find _ _ _ p (one_of_filter e).2.2.2

/-- **AT EACH OF THE FIFTY THE NUMBER IS THE TABLE's NUMBER OF AN OWN MESSAGE OF LINK l.** -/
theorem k1Num_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) :
    ∃ k, k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n = P5J.At.num Zp l k := by
  obtain ⟨p, e, -, -, -, k, hk⟩ := seat_fifty h O hl d hn
  exact ⟨k, P5T.arrOf_is_num _ _ _ l k p (one_of_filter e).2.2.2 hk⟩

/-- **AT THE OPENING, MESSAGE NUMBER 4 SITS AT THE TABLE's SEAT OF THE INDEX MASKS.** -/
theorem index_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4 = (P5J.At.N Zp cF).index := by
  rw [seat_two_written h O 4]
  have e : (P5J.At.N Zp cF).index = (1, 0) := K1.index_atAll h O (K1.pin1_atAll h)
  rw [e]
  have hm : 4 ∈ (List.range parGF.sent.size).filter
      (fun n => decide (seatOfMsg parGF 0 n = (1, 0))) := by
    rw [indexW]
    exact List.mem_singleton.2 rfl
  exact of_decide_eq_true (List.mem_filter.1 hm).2

/-- So the number there is the table's number at that seat. -/
theorem k1Num_index (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4 =
      P5J.At.arr Zp (P5J.At.N Zp cF).index.1 (P5J.At.N Zp cF).index.2 := by
  unfold k1Num
  rw [index_two h O]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Num
#print axioms ProofFile.Honest.K1.k1SeatIn
#print axioms ProofFile.Honest.K1.k1Num_is
#print axioms ProofFile.Honest.K1.one_of_filter
#print axioms ProofFile.Honest.K1.one_of_test
#print axioms ProofFile.Honest.K1.seatW2
#print axioms ProofFile.Honest.K1.backW2
#print axioms ProofFile.Honest.K1.keysW2
#print axioms ProofFile.Honest.K1.indexW
#print axioms ProofFile.Honest.K1.seatW50
#print axioms ProofFile.Honest.K1.backW50
#print axioms ProofFile.Honest.K1.seatW2_bites
#print axioms ProofFile.Honest.K1.seatW50_bites
#print axioms ProofFile.Honest.K1.pseatsAll_written
#print axioms ProofFile.Honest.K1.seat_two_written
#print axioms ProofFile.Honest.K1.seat_fifty_written
#print axioms ProofFile.Honest.K1.seat_two
#print axioms ProofFile.Honest.K1.seatIn_two
#print axioms ProofFile.Honest.K1.seat_fifty
#print axioms ProofFile.Honest.K1.seatIn_fifty
#print axioms ProofFile.Honest.K1.k1Num_of_one
#print axioms ProofFile.Honest.K1.k1Num_fifty
#print axioms ProofFile.Honest.K1.index_two
#print axioms ProofFile.Honest.K1.k1Num_index
