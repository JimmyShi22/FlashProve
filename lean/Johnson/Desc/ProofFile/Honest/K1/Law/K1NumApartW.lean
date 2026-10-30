-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1NumApartW.lean: THE SHARED "SENDING" (the kind K1): ONE
NUMBER, ONE MESSAGE: THE WITNESS's NUMBERS k1Num (K1NumAtHead.lean) OF THE TWO MESSAGES OF W's
SENDING (number 356 of the first chain) PART FROM EACH OTHER AND FROM THOSE OF THE OPENING AND OF
THE FIFTY LATER SENDINGS, UNDER THE LIBRARY's HEAD: what K1NumApart.lean, whose 51 places lack this
one, leaves. PUBLIC DATA ALONE: plans, the plan's list of seats, keys, numbers. Seven theorems; no
definition.

The road is K1NumApart.lean's. Two found seats with one number have one key (arrOf_key,
Johnson/P5T/ArrApart.lean). Under the head our seats and the plan's list are the written ones
(K1NumAtW.lean, K1NumAtHead.lean). That the written keys at two different messages part is a closed
fact, pair by pair, evaluated in Lean's kernel.

  - apartW356, apartW356_2, apartW356_50: the three closed facts: within W's sending; W's sending
    against the opening; against each of the fifty.
  - find_w: UNDER h, O: the one seat p of the plan's list at our seat is found both in the plan's
    list at our seat and in the written list at the written seat.
  - k1Num_apart_w: UNDER h (the library's head: A HYPOTHESIS), O, n and n' below the plan's number
    of messages: equal numbers: n = n'.
  - k1Num_apart_w_two, k1Num_apart_w_fifty: a number of W's sending's is no number of the opening's,
    and none of any of the fifty's.

Mind, as in K1NumApart.lean. The closed facts compare OPTIONS of keys: two seats that the list lacks
would make them false, not idle; one found and one lacking would pass idly: seatW356
(K1NumAtW.lean), seatW2, seatW50 (K1NumAtHead.lean) bar that: at each of these seats the list has a
seat. That the like test can say no: apartAll_no (K1NumApart.lean).

Limits. K1's 52 PLACES, WITH K1NumApart.lean: nothing on the numbers of other kinds' messages. THE
FULL SIZE ALONE. Nothing is said of the Script. Evaluations in Lean's kernel (decide +kernel): no
compiled code. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumApart
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (parGF parWF seatOfMsg placeL baseL3 fiftyB fifty_of)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open P5T (PSeat seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 At the written constants -/

/-- Within W's sending: two different messages have two keys. -/
theorem apartW356 : ((List.range parWF.sent.size).all fun n =>
    (List.range parWF.sent.size).all fun n' => n == n' ||
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
        p.t == (seatOfMsg parWF 82 n).2).map keyOf) !=
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n').1 &&
        p.t == (seatOfMsg parWF 82 n').2).map keyOf)) = true := by
  decide +kernel

/-- W's sending against the opening. -/
theorem apartW356_2 : ((List.range parWF.sent.size).all fun n =>
    (List.range parGF.sent.size).all fun n' =>
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
        p.t == (seatOfMsg parWF 82 n).2).map keyOf) !=
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n').1 &&
        p.t == (seatOfMsg parGF 0 n').2).map keyOf)) = true := by
  decide +kernel

/-- W's sending against each of the fifty. -/
theorem apartW356_50 : ((List.range parWF.sent.size).all fun n => fiftyB fun l d =>
    (List.range (placeL l d).sent.size).all fun n' =>
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
        p.t == (seatOfMsg parWF 82 n).2).map keyOf) !=
      ((seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n').1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n').2).map keyOf)) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- The one seat at our seat, found in both lists: at number 356. -/
theorem find_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) :
    ∃ p, ((P5J.At.pseatsAll Zp).find? fun p =>
        p.j == (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).1 &&
          p.t == (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).2) = some p ∧
      (seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
        p.t == (seatOfMsg parWF 82 n).2) = some p := by
  obtain ⟨p, e, -⟩ := seat_w h O hn
  have e1 := (one_of_filter e).2.2.2
  have e2 := e1
  rw [seat_w_written h O n, pseatsAll_written h] at e2
  exact ⟨p, e1, e2⟩

/-- **WITHIN W's SENDING: ONE NUMBER, ONE MESSAGE.** -/
theorem k1Num_apart_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n n' : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size)
    (hn' : n' < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size)
    (e : k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n =
      k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n') : n = n' := by
  obtain ⟨p, f1, g1⟩ := find_w h O hn
  obtain ⟨p', f2, g2⟩ := find_w h O hn'
  have hk := P5T.arrOf_key _ _ _ _ _ p p' f1 f2 e
  rw [parW_written h O] at hn hn'
  have c := List.all_eq_true.1 (List.all_eq_true.1 apartW356 n (List.mem_range.2 hn)) n'
    (List.mem_range.2 hn')
  rw [g1, g2, Option.map_some, Option.map_some, hk, Bool.or_eq_true, beq_iff_eq] at c
  rcases c with c | c
  · exact c
  · simp at c

/-- **A NUMBER OF W's SENDING's IS NO NUMBER OF THE OPENING's.** -/
theorem k1Num_apart_w_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) {n' : ℕ}
    (hn' : n' < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) :
    k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n ≠
      k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n' := by
  intro e
  obtain ⟨p, f1, g1⟩ := find_w h O hn
  obtain ⟨p', f2, g2⟩ := find_two h O hn'
  have hk := P5T.arrOf_key _ _ _ _ _ p p' f1 f2 e
  rw [parW_written h O] at hn
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn'
  have c := List.all_eq_true.1 (List.all_eq_true.1 apartW356_2 n (List.mem_range.2 hn)) n'
    (List.mem_range.2 hn')
  rw [g1, g2, Option.map_some, Option.map_some, hk] at c
  simp at c

/-- **NOR OF ANY OF THE FIFTY's.** -/
theorem k1Num_apart_w_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) {l : ℕ} (hl : l < 25) (d : Bool)
    {n' : ℕ} (hn' : n' < (K1.parL Zp Bs.G₀ l d).sent.size) :
    k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n ≠
      k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n' := by
  intro e
  obtain ⟨p, f1, g1⟩ := find_w h O hn
  obtain ⟨p', f2, g2⟩ := find_fifty h O hl d hn'
  have hk := P5T.arrOf_key _ _ _ _ _ p p' f1 f2 e
  rw [parW_written h O] at hn
  rw [parL_written h O l d] at hn'
  have c := List.all_eq_true.1 (fifty_of (List.all_eq_true.1 apartW356_50 n (List.mem_range.2 hn))
    l hl d) n' (List.mem_range.2 hn')
  rw [g1, g2, Option.map_some, Option.map_some, hk] at c
  simp at c

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.apartW356
#print axioms ProofFile.Honest.K1.apartW356_2
#print axioms ProofFile.Honest.K1.apartW356_50
#print axioms ProofFile.Honest.K1.find_w
#print axioms ProofFile.Honest.K1.k1Num_apart_w
#print axioms ProofFile.Honest.K1.k1Num_apart_w_two
#print axioms ProofFile.Honest.K1.k1Num_apart_w_fifty
