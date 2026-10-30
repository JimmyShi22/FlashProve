-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1NumOthersW.lean: THE SHARED "SENDING" (the kind K1): WHO ELSE
BEARS A NUMBER OF OURS, AT W's SENDING (356) AND, SHARPER, AT THE FIFTY: NOBODY: UNDER THE LIBRARY's
HEAD: A SEAT OF THE PLAN's LIST (all three chains') WHOSE NUMBER IN THE WITNESS IS THE NUMBER k1Num
OF A MESSAGE OF W's SENDING, OR OF ONE OF THE FIFTY LATER SENDINGS, IS THAT MESSAGE's OWN SEAT. AND
WHICH KEPT COPIES BEAR A NUMBER OF THE OPENING's: JUST THREE, BY NAME. PUBLIC DATA ALONE: plans, the
plan's list of seats, keys, roles, numbers: WHICH MESSAGE, NEVER WHAT STANDS IN IT. Thirteen
theorems; no definition.

THE SISTER OF K1NumOthers.lean AND K1SeatAlone.lean, WHICH STAND AT 55 SEATS: "W's sending is not
here"; and of the fifty K1NumOthers.lean says of its arm "or its role is kept": "Whether it is spent
at any of the fifty is not told". HERE IT IS TOLD: AT NONE.

  CLOSED FACTS, evaluated in Lean's kernel at the written list, EACH WITH A TWIN THAT SAYS NO:
  - othersW356: at each of W's two written seats: every seat of the written list with that seat's
    key stands at that tree and tenant. NO ARM "kept". othersW356_bites: by the SENDING's number in
    the key's stead the test says no (the two messages share their sending).
  - segW356: W's two written seats bear NO link and moment (seg = none). segW356_bites: asked for
    "link 0, moment 0" the test says no. SO AT W "ANOTHER SENDING" IS TOLD BY send, NOT BY seg.
  - othersS50: othersW50 (K1NumOthers.lean) WITHOUT ITS ARM "kept": true at all fifty. ITS TWIN THAT
    SAYS NO IS A ROW: othersW_bites (K1NumOthers.lean): the same text at the opening.
  - keptAt2: THE KEPT COPIES, SAID OUT: the seats of the written list that bear the key of a message
    of the opening and are not its own seat: JUST THREE: of message 1: place 1 of sending 3; of
    message 2: place 2 of sending 3 and place 1 of sending 6: links 1, 1, 2 at moment 0: all three
    of a kept copy's role. keptAt2_bites: with one place bent the test says no.

  UNDER h (the library's head: A HYPOTHESIS) AND O:
  - met_of_two: a tool: from the two arms to the end (no premise on the head).
  - k1Num_met_w: n below W's plan's number of messages; q the seat that the plan's list holds at
    tree j and tenant t; the witness's number there is ours: (j, t) IS OUR SEAT.
  - k1Num_send_w: under the same: q.send = 81, q.idx = n, q.seg = none.
  - k1Seat_alone_w: a member q of the plan's list at our tree and tenant: the same three.
  - k1Num_met_fifty_own, k1Num_seg_fifty_own: k1Num_met_fifty | k1Num_seg_fifty (K1NumOthers.lean)
    WITHOUT THE ARM AND WITHOUT THE PREMISE hr.

THE KEPT COPIES. A LOT THAT STANDS AT ONE OF keptAt2's THREE SEATS BEARS A NUMBER OF THE OPENING's.
NOTHING HERE SAYS WHAT SUCH A LOT HOLDS, NOR THAT IT AGREES WITH OURS: that is a matter of the two
texts, not of numbers. AT W's TWO AND AT THE FIFTY's FIFTY MESSAGES THERE IS NO SUCH SEAT.

KIN, TOLD. THIS FILE's CLOSED FACTS ARE THE SISTERS OF K1NumOthers.lean's, IN THEIR FORM, BY THE
SEAT, AND ARE CARRIED UNDER THE HEAD.

For whom. The tie: LotsAgree | PadLotsAgree (Honest/Thread/ScriptLots.lean) between our lots and
another sender's bite only at one number | one tree and tenant. THAT JOIN IS NOT TYPED HERE: no lot
and no Script is named.

The road. K1NumOthers.lean's and K1SeatAlone.lean's proofs, with find_w (K1NumApartW.lean), seat_w
(K1NumAtW.lean) and parW_written (FitsAtW.lean) for find_two, seat_two and the opening's plan.

Limits. THE FULL SIZE ALONE; the format's second hash function alone. THE CLOSED FACTS SPEAK OF THE WRITTEN
LIST; the head carries them to the plan's (pseatsAll_written). Nothing is said of the Script, nor of
any lot. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1SeatAlone
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumApartW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (parGF parWF seatOfMsg placeL baseL3 momL fiftyB fifty_of)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open P5T (PSeat Role seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 The closed facts -/

/-- At W's two written seats: nobody else bears the key. -/
theorem othersW356 : ((List.range parWF.sent.size).all fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
      p.t == (seatOfMsg parWF 82 n).2 with
    | some s => seatsAllFull.all fun q => keyOf q != keyOf s || (q.j == s.j && q.t == s.t)
    | none => false) = true := by
  decide +kernel

/-- A NEGATIVE TEST: by the sending's number in the key's stead the test says no. -/
theorem othersW356_bites : ((List.range parWF.sent.size).all fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
      p.t == (seatOfMsg parWF 82 n).2 with
    | some s => seatsAllFull.all fun q => q.send != s.send || (q.j == s.j && q.t == s.t)
    | none => false) = false := by
  decide +kernel

/-- W's two written seats bear no link and moment. -/
theorem segW356 : ((List.range parWF.sent.size).all fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
      p.t == (seatOfMsg parWF 82 n).2).any fun s => s.seg == none) = true := by
  decide +kernel

/-- A NEGATIVE TEST: asked for "link 0, moment 0" the test says no. -/
theorem segW356_bites : ((List.range parWF.sent.size).all fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
      p.t == (seatOfMsg parWF 82 n).2).any fun s => s.seg == some (0, 0)) = false := by
  decide +kernel

/-- At the fifty: nobody else bears the key: othersW50 without its arm "kept". -/
theorem othersS50 : fiftyB (fun l d => (List.range (placeL l d).sent.size).all fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
      p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2 with
    | some s => seatsAllFull.all fun q => keyOf q != keyOf s || (q.j == s.j && q.t == s.t)
    | none => false) = true := by
  decide +kernel

/-- **THE KEPT COPIES, SAID OUT**: who else bears a key of the opening's: (the opening's message,
the other seat's sending, its place there, its link and moment, whether its role is a kept
copy's). -/
theorem keptAt2 : (((List.range parGF.sent.size).flatMap fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
      p.t == (seatOfMsg parGF 0 n).2 with
    | some s => (seatsAllFull.filter fun q => keyOf q == keyOf s &&
        !(q.j == s.j && q.t == s.t)).map fun q =>
          (n, q.send, q.idx, q.seg, match q.role with | .kept _ _ => true | _ => false)
    | none => [(n, 0, 0, none, false)]) ==
    ([(1, 3, 1, some (1, 0), true), (2, 3, 2, some (1, 0), true), (2, 6, 1, some (2, 0), true)] :
      List (ℕ × ℕ × ℕ × Option (ℕ × ℕ) × Bool))) = true := by
  decide +kernel

/-- A NEGATIVE TEST: with one place bent the test says no. -/
theorem keptAt2_bites : (((List.range parGF.sent.size).flatMap fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
      p.t == (seatOfMsg parGF 0 n).2 with
    | some s => (seatsAllFull.filter fun q => keyOf q == keyOf s &&
        !(q.j == s.j && q.t == s.t)).map fun q =>
          (n, q.send, q.idx, q.seg, match q.role with | .kept _ _ => true | _ => false)
    | none => [(n, 0, 0, none, false)]) ==
    ([(1, 3, 1, some (1, 0), true), (2, 3, 2, some (1, 0), true), (2, 6, 2, some (2, 0), true)] :
      List (ℕ × ℕ × ℕ × Option (ℕ × ℕ) × Bool))) = false := by
  decide +kernel

/-- A tool: from the two arms of the closed facts to the end. -/
theorem met_of_two {s q : PSeat} {j t : ℕ} {x₀ : ℕ × ℕ} (hk : keyOf q = keyOf s)
    (hq : (q.j == j && q.t == t) = true) (hs : (s.j == x₀.1 && s.t == x₀.2) = true)
    (c : (keyOf q != keyOf s || (q.j == s.j && q.t == s.t)) = true) : (j, t) = x₀ := by
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hq
  obtain ⟨s1, s2⟩ := Bool.and_eq_true_iff.1 hs
  rw [Bool.or_eq_true] at c
  rcases c with c | c
  · rw [hk] at c
    simp at c
  · obtain ⟨c1, c2⟩ := Bool.and_eq_true_iff.1 c
    have a : j = x₀.1 := by rw [← eq_of_beq q1, eq_of_beq c1, eq_of_beq s1]
    have b : t = x₀.2 := by rw [← eq_of_beq q2, eq_of_beq c2, eq_of_beq s2]
    exact Prod.ext a b

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **WHO BEARS A NUMBER OF W's SENDING: ITS OWN SEAT ALONE.** -/
theorem k1Num_met_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n) :
    (j, t) = seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n := by
  obtain ⟨s, f1, g1⟩ := find_w h O hn
  have hk := P5T.arrOf_key _ _ _ _ _ q s hq f1 e
  have hm : q ∈ seatsAllFull := by
    rw [← pseatsAll_written h]
    exact List.mem_of_find?_eq_some hq
  rw [parW_written h O] at hn
  have c := List.all_eq_true.1 othersW356 n (List.mem_range.2 hn)
  rw [g1] at c
  have hq' := List.find?_some hq
  have hs' := List.find?_some f1
  exact met_of_two hk hq' hs' (List.all_eq_true.1 c q hm)

/-- **A MEMBER OF THE PLAN's LIST AT OUR TREE AND TENANT, AT 356, IS OURS.** -/
theorem k1Seat_alone_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) {q : PSeat}
    (hm : q ∈ P5J.At.pseatsAll Zp)
    (e : (q.j, q.t) = seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n) :
    q.send = 81 ∧ q.idx = n ∧ q.seg = none := by
  obtain ⟨p, f, h1, h2, -⟩ := seat_w h O hn
  have hq : q = p := (one_of_filter f).2.2.1 q hm (by
    show (q.j == _ && q.t == _) = true
    rw [← e]
    simp)
  subst hq
  obtain ⟨s, f1, g1⟩ := find_w h O hn
  obtain rfl : q = s := Option.some.inj ((one_of_filter f).2.2.2.symm.trans f1)
  rw [parW_written h O] at hn
  have c := List.all_eq_true.1 segW356 n (List.mem_range.2 hn)
  rw [g1] at c
  exact ⟨h1, h2, eq_of_beq c⟩

/-- **AND SUCH A SEAT IS MEMBER n OF SENDING 81, OF NO LINK.** -/
theorem k1Num_send_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n) :
    q.send = 81 ∧ q.idx = n ∧ q.seg = none := by
  have e1 := k1Num_met_w h O hn hq e
  have hq₀ := List.find?_some hq
  have hq' : (q.j == j && q.t == t) = true := hq₀
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hq'
  have e0 : (q.j, q.t) = (j, t) := by rw [eq_of_beq q1, eq_of_beq q2]
  exact k1Seat_alone_w h O hn (List.mem_of_find?_eq_some hq) (e0.trans e1)

/-- **WHO BEARS A NUMBER OF ONE OF THE FIFTY: ITS OWN SEAT ALONE**: no arm "kept". -/
theorem k1Num_met_fifty_own (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n) :
    (j, t) = seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n := by
  obtain ⟨s, f1, g1⟩ := find_fifty h O hl d hn
  have hk := P5T.arrOf_key _ _ _ _ _ q s hq f1 e
  have hm : q ∈ seatsAllFull := by
    rw [← pseatsAll_written h]
    exact List.mem_of_find?_eq_some hq
  rw [parL_written h O l d] at hn
  have c := List.all_eq_true.1 (fifty_of othersS50 l hl d) n (List.mem_range.2 hn)
  rw [g1] at c
  have hq' := List.find?_some hq
  have hs' := List.find?_some f1
  exact met_of_two hk hq' hs' (List.all_eq_true.1 c q hm)

/-- **AND IT STANDS IN OUR SENDING**: k1Num_seg_fifty without its premise hr. -/
theorem k1Num_seg_fifty_own (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n) :
    q.seg = some (l, momL d) := by
  have e1 := k1Num_met_fifty_own h O hl d hn hq e
  have hq₀ := List.find?_some hq
  have hq' : (q.j == j && q.t == t) = true := hq₀
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hq'
  have e0 : (q.j, q.t) = (j, t) := by rw [eq_of_beq q1, eq_of_beq q2]
  exact (k1Seat_alone_fifty h O hl d hn (List.mem_of_find?_eq_some hq) (e0.trans e1)).2.2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.othersW356
#print axioms ProofFile.Honest.K1.othersW356_bites
#print axioms ProofFile.Honest.K1.segW356
#print axioms ProofFile.Honest.K1.segW356_bites
#print axioms ProofFile.Honest.K1.othersS50
#print axioms ProofFile.Honest.K1.keptAt2
#print axioms ProofFile.Honest.K1.keptAt2_bites
#print axioms ProofFile.Honest.K1.met_of_two
#print axioms ProofFile.Honest.K1.k1Num_met_w
#print axioms ProofFile.Honest.K1.k1Seat_alone_w
#print axioms ProofFile.Honest.K1.k1Num_send_w
#print axioms ProofFile.Honest.K1.k1Num_met_fifty_own
#print axioms ProofFile.Honest.K1.k1Num_seg_fifty_own
