-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1NumOthers.lean: THE SHARED "SENDING" (the kind K1): WHO ELSE
BEARS A NUMBER OF OURS: UNDER THE LIBRARY's HEAD: A SEAT OF THE PLAN's LIST (all three chains')
WHOSE NUMBER IN THE WITNESS IS THE NUMBER k1Num (K1NumAtHead.lean) OF A MESSAGE OF THE OPENING OR OF
ONE OF THE FIFTY LATER SENDINGS IS THAT MESSAGE's OWN SEAT, OR ITS ROLE IS A KEPT COPY's. PUBLIC
DATA ALONE: plans, the plan's list of seats, keys, roles, numbers. Eleven theorems; no definition.

  - othersW2, othersW50: the two closed facts, evaluated in Lean's kernel: at each of the 55
    written seats of ours: every seat of the written list with that seat's key stands at that tree
    and tenant, or its role is "kept".
  - othersW_bites: A NEGATIVE TEST: without the arm "or its role is kept" the test at the opening
    says no: kept copies of the opening's messages ARE in the list: so the arm is spent there.
    Whether it is spent at any of the fifty is not told.
  - met_of_arm: a tool: from one arm of the closed facts to the end.
  - k1Num_met_two, k1Num_met_fifty: UNDER h (the library's head: A HYPOTHESIS), O, n below the
    plan's number of messages (and hl : l < 25): if q is the seat that the plan's list holds at tree
    j and tenant t, and the witness's number there is ours: (j, t) is our seat, or q.role = kept l'
    k'.
  - segW2, segW50: two closed facts more: each of our 55 written seats stands in its own sending:
    "link 0, moment 0"; "link l, moment 1" (reads); "link l, moment 2" (digits). segW2_bites: A
    NEGATIVE TEST: asked for "link 0, moment 1" the opening's test says no.
  - k1Num_seg_two, k1Num_seg_fifty: UNDER THE SAME, and hr : q's role is no kept copy's: q.seg is
    that sending's. SO A SEAT OF ANOTHER SENDING THAT IS NO KEPT COPY BEARS NO NUMBER OF OURS.

For whom. The tie: LotsAgree (Honest/Thread/ScriptLots.lean) between our lots and another sender's
bites only at one number. By part 1's word its lots at the switches stand at seats of "link l,
moment 0" whose role is no kept copy's (its switchSeatIn; its firstNotKeptW | firstNotKept_at_head).
With this file: at l ≠ 0 such a lot's number is none of our 55. THAT JOIN IS NOT TYPED HERE: no text
of part 1's is imported.

The road. Two found seats with one number have one key (arrOf_key, Johnson/P5T/ArrApart.lean); under
the head our seats and the plan's list are the written ones (find_two, find_fifty, K1NumApart.lean;
pseatsAll_written, K1NumAtHead.lean).

Limits. 51 PLACES: W's sending is not here. THE FULL SIZE ALONE. Nothing is said of the Script, nor
of any lot. Evaluations in Lean's kernel (decide +kernel): no compiled code. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (parGF seatOfMsg placeL baseL3 momL fiftyB fifty_of)
open P5T (PSeat Role seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open IM (k1Ix)

/-! ## 1 At the written constants -/

/-- At the opening's written seats: who has the seat's key stands there, or is a kept copy. -/
theorem othersW2 : ((List.range parGF.sent.size).all fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2 with
    | some s => seatsAllFull.all fun q => keyOf q != keyOf s || (q.j == s.j && q.t == s.t) ||
        (match q.role with | .kept _ _ => true | _ => false)
    | none => false) = true := by
  decide +kernel

/-- The like at each of the fifty. -/
theorem othersW50 : fiftyB (fun l d => (List.range (placeL l d).sent.size).all fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
        p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2 with
    | some s => seatsAllFull.all fun q => keyOf q != keyOf s || (q.j == s.j && q.t == s.t) ||
        (match q.role with | .kept _ _ => true | _ => false)
    | none => false) = true := by
  decide +kernel

/-- A NEGATIVE TEST: without the arm on kept copies the test at the opening says no. -/
theorem othersW_bites : ((List.range parGF.sent.size).all fun n =>
    match seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2 with
    | some s => seatsAllFull.all fun q => keyOf q != keyOf s || (q.j == s.j && q.t == s.t)
    | none => false) = false := by
  decide +kernel

/-- Each of the opening's written seats stands in the sending "link 0, moment 0". -/
theorem segW2 : ((List.range parGF.sent.size).all fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
      p.t == (seatOfMsg parGF 0 n).2).any fun s => s.seg == some (0, 0)) = true := by
  decide +kernel

/-- A NEGATIVE TEST: asked for "link 0, moment 1" the opening's test says no. -/
theorem segW2_bites : ((List.range parGF.sent.size).all fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
      p.t == (seatOfMsg parGF 0 n).2).any fun s => s.seg == some (0, 1)) = false := by
  decide +kernel

/-- Each of the fifty's written seats stands in the sending "link l, moment 1" (reads) or "link l,
moment 2" (digits). -/
theorem segW50 : fiftyB (fun l d => (List.range (placeL l d).sent.size).all fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg (placeL l d) (baseL3 l d) n).1 &&
      p.t == (seatOfMsg (placeL l d) (baseL3 l d) n).2).any fun s =>
        s.seg == some (l, momL d)) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- From one arm of the closed facts to the end: general. -/
theorem met_of_arm {s q : PSeat} {j t : ℕ} {x₀ : ℕ × ℕ} (hk : keyOf q = keyOf s)
    (hq : (q.j == j && q.t == t) = true) (hs : (s.j == x₀.1 && s.t == x₀.2) = true)
    (c : (keyOf q != keyOf s || (q.j == s.j && q.t == s.t) ||
      (match q.role with | .kept _ _ => true | _ => false)) = true) :
    (j, t) = x₀ ∨ ∃ l' k', q.role = .kept l' k' := by
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hq
  obtain ⟨s1, s2⟩ := Bool.and_eq_true_iff.1 hs
  rw [Bool.or_eq_true, Bool.or_eq_true] at c
  rcases c with (c | c) | c
  · rw [hk] at c
    simp at c
  · obtain ⟨c1, c2⟩ := Bool.and_eq_true_iff.1 c
    left
    have a : j = x₀.1 := by rw [← eq_of_beq q1, eq_of_beq c1, eq_of_beq s1]
    have b : t = x₀.2 := by rw [← eq_of_beq q2, eq_of_beq c2, eq_of_beq s2]
    exact Prod.ext a b
  · right
    cases hr : q.role with
    | kept l' k' => exact ⟨l', k', rfl⟩
    | carried => rw [hr] at c; cases c
    | own k => rw [hr] at c; cases c
    | mask => rw [hr] at c; cases c
    | atStart i => rw [hr] at c; cases c
    | other => rw [hr] at c; cases c

/-- **AT NUMBER 2: WHO BEARS A NUMBER OF THE OPENING's IS ITS OWN SEAT, OR A KEPT COPY.** -/
theorem k1Num_met_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n) :
    (j, t) = seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n ∨
      ∃ l' k', q.role = .kept l' k' := by
  obtain ⟨s, f1, g1⟩ := find_two h O hn
  have hk := P5T.arrOf_key _ _ _ _ _ q s hq f1 e
  have hm : q ∈ seatsAllFull := by
    rw [← pseatsAll_written h]
    exact List.mem_of_find?_eq_some hq
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn
  have c := List.all_eq_true.1 othersW2 n (List.mem_range.2 hn)
  rw [g1] at c
  have hq' := List.find?_some hq
  have hs' := List.find?_some f1
  exact met_of_arm hk hq' hs' (List.all_eq_true.1 c q hm)

/-- **AT EACH OF THE FIFTY: THE LIKE.** -/
theorem k1Num_met_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n) :
    (j, t) = seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n ∨
      ∃ l' k', q.role = .kept l' k' := by
  obtain ⟨s, f1, g1⟩ := find_fifty h O hl d hn
  have hk := P5T.arrOf_key _ _ _ _ _ q s hq f1 e
  have hm : q ∈ seatsAllFull := by
    rw [← pseatsAll_written h]
    exact List.mem_of_find?_eq_some hq
  rw [parL_written h O l d] at hn
  have c := List.all_eq_true.1 (fifty_of othersW50 l hl d) n (List.mem_range.2 hn)
  rw [g1] at c
  have hq' := List.find?_some hq
  have hs' := List.find?_some f1
  exact met_of_arm hk hq' hs' (List.all_eq_true.1 c q hm)

/-- **AT NUMBER 2: WHO BEARS A NUMBER OF THE OPENING's AND IS NO KEPT COPY STANDS IN THE SENDING
"link 0, moment 0"**: so no seat of another sending does. -/
theorem k1Num_seg_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n)
    (hr : ∀ l' k', q.role ≠ .kept l' k') : q.seg = some (0, 0) := by
  rcases k1Num_met_two h O hn hq e with e1 | ⟨l', k', hk⟩
  · obtain ⟨s, f1, g1⟩ := find_two h O hn
    have ej : j = _ := congrArg Prod.fst e1
    have et : t = _ := congrArg Prod.snd e1
    subst ej et
    obtain rfl : q = s := Option.some.inj (hq.symm.trans f1)
    rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn
    have c := List.all_eq_true.1 segW2 n (List.mem_range.2 hn)
    rw [g1] at c
    exact eq_of_beq c
  · exact absurd hk (hr l' k')

/-- **AT EACH OF THE FIFTY: THE LIKE**: in "link l, moment 1" (reads) or "link l, moment 2"
(digits). -/
theorem k1Num_seg_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n)
    (hr : ∀ l' k', q.role ≠ .kept l' k') : q.seg = some (l, momL d) := by
  rcases k1Num_met_fifty h O hl d hn hq e with e1 | ⟨l', k', hk⟩
  · obtain ⟨s, f1, g1⟩ := find_fifty h O hl d hn
    have ej : j = _ := congrArg Prod.fst e1
    have et : t = _ := congrArg Prod.snd e1
    subst ej et
    obtain rfl : q = s := Option.some.inj (hq.symm.trans f1)
    rw [parL_written h O l d] at hn
    have c := List.all_eq_true.1 (fifty_of segW50 l hl d) n (List.mem_range.2 hn)
    rw [g1] at c
    exact eq_of_beq c
  · exact absurd hk (hr l' k')

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.othersW2
#print axioms ProofFile.Honest.K1.othersW50
#print axioms ProofFile.Honest.K1.othersW_bites
#print axioms ProofFile.Honest.K1.met_of_arm
#print axioms ProofFile.Honest.K1.k1Num_met_two
#print axioms ProofFile.Honest.K1.k1Num_met_fifty
#print axioms ProofFile.Honest.K1.segW2
#print axioms ProofFile.Honest.K1.segW2_bites
#print axioms ProofFile.Honest.K1.segW50
#print axioms ProofFile.Honest.K1.k1Num_seg_two
#print axioms ProofFile.Honest.K1.k1Num_seg_fifty
