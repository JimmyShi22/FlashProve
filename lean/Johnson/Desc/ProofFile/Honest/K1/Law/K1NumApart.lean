-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1NumApart.lean: THE SHARED "SENDING" (the kind K1): ONE
NUMBER, ONE MESSAGE: THE WITNESS's NUMBERS k1Num (K1NumAtHead.lean) OF THE MESSAGES OF THE OPENING
AND OF THE FIFTY LATER SENDINGS ARE PAIRWISE APART, UNDER THE LIBRARY's HEAD. PUBLIC DATA ALONE:
plans, the plan's list of seats, keys, numbers. Nine theorems; no definition.

The road. Two found seats with one number have one key (arrOf_key, Johnson/P5T/ArrApart.lean). Under
the head our seats and the plan's list are the written ones (K1NumAtHead.lean). That the written
keys at two different messages part is a closed fact, pair by pair, evaluated in Lean's kernel.

  - apartW2, apartW2_50, apartW50: the three closed facts: within the opening; the opening against
    each of the fifty; the fifty among themselves.
  - apartAll_no: A NEGATIVE TEST: over ALL seats of the written list the like test says no: two
    different seats there bear one key: so the three facts are facts on these 55 seats, not on the
    test's form.
  - find_two, find_fifty: UNDER h, O: the one seat p of the plan's list at our seat is found both in
    the plan's list at our seat and in the written list at the written seat.
  - k1Num_apart_two: UNDER h (the library's head: A HYPOTHESIS), O, n and n' below the opening's
    plan's number of messages: equal numbers: n = n'.
  - k1Num_apart_two_fifty: a number of the opening's is no number of any of the fifty's.
  - k1Num_apart_fifty: equal numbers at two of the fifty: the same link, the same d, the same n.

For whom. The tie: that two of our own lots with one number are one lot (LotsAgree among K1's lots)
wants just this.

Mind. The closed facts compare OPTIONS of keys: two seats that the list lacks would make them false,
not idle; one found and one lacking would pass idly: seatW2, seatW50 (K1NumAtHead.lean) bar that: at
each of the 55 seats the list has a seat.

Kin in the library. seatsAllFull_apart (Johnson/P5T/PlanSeatsFull.lean): no seat stands twice in the
written list. arr_apart_written, arr_can_meet (Johnson/P5J/L0/PlanFourAtJoin.lean): the like fact on
the numbers themselves at another list of seats, with its negative. arr_apart
(Johnson/P5T/ArrApart.lean), arr_apart_chains (Johnson/P5T/ArrApartChains.lean): on the two later
chains' seats.

Limits. 51 PLACES: W's sending is not here; nothing on the numbers of other kinds' messages. THE
FULL SIZE ALONE. Nothing is said of the Script. Evaluations in Lean's kernel (decide +kernel): no
compiled code. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.P5T.ArrApart

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
open IM (k1Ix)

/-! ## 1 At the written constants -/

/-- Within the opening: two different messages have two keys. -/
theorem apartW2 : ((List.range parGF.sent.size).all fun n =>
    (List.range parGF.sent.size).all fun n' => n == n' ||
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2).map keyOf) !=
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n').1 &&
        p.t == (seatOfMsg parGF 0 n').2).map keyOf)) = true := by
  decide +kernel

/-- The opening against each of the fifty. -/
theorem apartW2_50 : ((List.range parGF.sent.size).all fun n => fiftyB fun l d =>
    (List.range (placeL l d).sent.size).all fun n' =>
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2).map keyOf) !=
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n').1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n').2).map keyOf)) = true := by
  decide +kernel

/-- The fifty among themselves. -/
theorem apartW50 : fiftyB (fun l d => fiftyB fun l' d' =>
    (List.range (placeL l d).sent.size).all fun n =>
      (List.range (placeL l' d').sent.size).all fun n' =>
        (l == l' && d == d' && n == n') ||
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2).map keyOf) !=
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l' d') (baseL3 l' d') n').1 &&
        p.t == (seatOfMsg (placeL l' d') (baseL3 l' d') n').2).map keyOf)) = true := by
  decide +kernel

/-- A negative test: OVER ALL SEATS OF THE WRITTEN LIST the like test says no: there some two
different seats do bear one key; WHICH two it does not say (by keyOf's text,
Johnson/P5T/PlanSeats.lean, an original and its kept copies have one key). So that the keys part is
a fact on these 55 seats, not on the form of the test. -/
theorem apartAll_no : (seatsAllFull.all fun p => seatsAllFull.all fun p' =>
    (p.j == p'.j && p.t == p'.t) || keyOf p != keyOf p') = false := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- The one seat at our seat, found in both lists: at number 2. -/
theorem find_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) :
    ∃ p, ((P5J.At.pseatsAll Zp).find? fun p =>
        p.j == (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1 &&
          p.t == (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2) = some p ∧
      (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2) = some p := by
  obtain ⟨p, e, -⟩ := seat_two h O hn
  have e1 := (one_of_filter e).2.2.2
  have e2 := e1
  rw [seat_two_written h O n, pseatsAll_written h] at e2
  exact ⟨p, e1, e2⟩

/-- The like at each of the fifty. -/
theorem find_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) :
    ∃ p, ((P5J.At.pseatsAll Zp).find? fun p =>
        p.j == (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).1 &&
          p.t == (seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n).2) = some p ∧
      (seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2) = some p := by
  obtain ⟨p, e, -⟩ := seat_fifty h O hl d hn
  have e1 := (one_of_filter e).2.2.2
  have e2 := e1
  rw [seat_fifty_written h O hl d n, pseatsAll_written h] at e2
  exact ⟨p, e1, e2⟩

/-- **WITHIN THE OPENING: ONE NUMBER, ONE MESSAGE.** -/
theorem k1Num_apart_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n n' : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size)
    (hn' : n' < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size)
    (e : k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n =
      k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n') : n = n' := by
  obtain ⟨p, f1, g1⟩ := find_two h O hn
  obtain ⟨p', f2, g2⟩ := find_two h O hn'
  have hk := P5T.arrOf_key _ _ _ _ _ p p' f1 f2 e
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn hn'
  have c := List.all_eq_true.1 (List.all_eq_true.1 apartW2 n (List.mem_range.2 hn)) n'
    (List.mem_range.2 hn')
  rw [g1, g2, Option.map_some, Option.map_some, hk, Bool.or_eq_true, beq_iff_eq] at c
  rcases c with c | c
  · exact c
  · simp at c

/-- **A NUMBER OF THE OPENING's IS NO NUMBER OF ANY OF THE FIFTY's.** -/
theorem k1Num_apart_two_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) {l : ℕ} (hl : l < 25) (d : Bool)
    {n' : ℕ} (hn' : n' < (K1.parL Zp Bs.G₀ l d).sent.size) :
    k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n ≠
      k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n' := by
  intro e
  obtain ⟨p, f1, g1⟩ := find_two h O hn
  obtain ⟨p', f2, g2⟩ := find_fifty h O hl d hn'
  have hk := P5T.arrOf_key _ _ _ _ _ p p' f1 f2 e
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn
  rw [parL_written h O l d] at hn'
  have c := List.all_eq_true.1 (fifty_of (List.all_eq_true.1 apartW2_50 n (List.mem_range.2 hn))
    l hl d) n' (List.mem_range.2 hn')
  rw [g1, g2, Option.map_some, Option.map_some, hk] at c
  simp at c

/-- **AMONG THE FIFTY: ONE NUMBER, ONE MESSAGE.** -/
theorem k1Num_apart_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l l' : ℕ} (hl : l < 25) (hl' : l' < 25)
    (d d' : Bool) {n n' : ℕ} (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size)
    (hn' : n' < (K1.parL Zp Bs.G₀ l' d').sent.size)
    (e : k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n =
      k1Num Zp cF.blocksInOrder (K1.noL l' d') (K1.parL Zp Bs.G₀ l' d') n') :
    l = l' ∧ d = d' ∧ n = n' := by
  obtain ⟨p, f1, g1⟩ := find_fifty h O hl d hn
  obtain ⟨p', f2, g2⟩ := find_fifty h O hl' d' hn'
  have hk := P5T.arrOf_key _ _ _ _ _ p p' f1 f2 e
  rw [parL_written h O l d] at hn
  rw [parL_written h O l' d'] at hn'
  have c := List.all_eq_true.1 (List.all_eq_true.1 (fifty_of (fifty_of apartW50 l hl d) l' hl' d')
    n (List.mem_range.2 hn)) n' (List.mem_range.2 hn')
  rw [g1, g2, Option.map_some, Option.map_some, hk, Bool.or_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq] at c
  rcases c with c | c
  · exact ⟨c.1.1, c.1.2, c.2⟩
  · simp at c

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.apartW2
#print axioms ProofFile.Honest.K1.apartW2_50
#print axioms ProofFile.Honest.K1.apartW50
#print axioms ProofFile.Honest.K1.apartAll_no
#print axioms ProofFile.Honest.K1.find_two
#print axioms ProofFile.Honest.K1.find_fifty
#print axioms ProofFile.Honest.K1.k1Num_apart_two
#print axioms ProofFile.Honest.K1.k1Num_apart_two_fifty
#print axioms ProofFile.Honest.K1.k1Num_apart_fifty
