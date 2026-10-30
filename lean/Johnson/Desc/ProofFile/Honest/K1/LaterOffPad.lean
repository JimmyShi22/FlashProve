-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LaterOffPad.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: AT THE LOT's LATER PLACES (each link's reads and digits): WHERE THE LOT's DATA
(lotData, Honest/K1/LotData.lean) LAY AN ELEMENT THERE IS ROOM, OFF THE PAD, AT THE SENDER's OWN
SHAPE AND CODES, UNDER TWO PUBLIC TESTS: codes.lengthsOk AND momentIs. One definition with code;
statements and proofs. PUBLIC: no coin, no witness, no input.

  filter_at_count   on lists: an entry's number among the entries that pass a test
  seat_text     what seatOf's "some s" says (Johnson/HonestTrace/SeatOf.lean), as equations
  seats_text    the same at a member of seatsOf
  seated_room   a filling by laidData at the ground's codes, shape and layout, whose seat answers
                only as pairOf of seatsOf does, under codes.lengthsOk (each code's message length is
                a power of two): where it lays: the seat at the address; a row below the seat's main
                rows; a place below the seat's length; off the pad; a sampled message
  reads_room, digitsFilling_room, lot_room   so, under codes.lengthsOk, the reads' filling (u3RowsOf), the
                digits' (digitsFill: bzRows over zzDataAt) and the lot's data off the opening's
                address
  momentIs      A PUBLIC TEST AT A SEAT: the array's message is of the moment t
  seat_shape_later   under it the seat's shape is the sender's: shapeAt (K1.parLater …) at the
                seat's number (by shapeAt_later, Honest/K1/SeatShape.lean)
  seat_seg      the seat's segment is the link of its address's place
  later_lays_room, later_lays_off_padB, later_clear   THE JOIN AT A LATER PLACE's PLAN, under
                codes.lengthsOk (hlen), at an address that is not the opening's (hne) and under
                momentIs at each seat that stands at the address (hmom): where the lot's data lay:
                room at the sender's shape and codes, off the pad, in a sampled message · the same
                in padB's form · so RowData.clear accepts there

WHY IT IS SHORT. The three fillings are laidData at a seat: u3Rows, bzRows and zzData lay the field
"ready" anew and nothing else: so lays_room (Honest/Law/LaysRoom.lean) serves as it stands.

THE PREMISE ON THE MOMENT. A seat's address is made by the rule "the sender of a segment's moment t
is the segment's place number t among its places of the kinds K1 and K2" (sendersOf,
Honest/K2/Seat.lean); a job's plan is made at a piece and a moment that the lot names
(K1.linkNumbers). THAT THE TWO AGREE IS HELD BY NO LAW: it is asked here as momentIs at the seat
that stands at the job's address: a test with code, to be evaluated beside readsSeatsOk and
digitsSeatsOk. THE OTHER ROAD, a law on spotsFrom (Johnson/Desc/ProofFile/Places.lean) and
K1.linkNumbers, IS NOT WALKED.

Limits. No filling calls it. SeatOf.lean's OWN TWO LIMITS HOLD HERE: moments from 1 on alone (seatOf
yields nothing for an array of moment 0); the rule on senders is held by no test against a
description's own list of sub-protocols. Z and G are two letters: nothing here holds that they
belong together. Of the layout, the shapes and the table of places alone: that a program lays as the
layout says is not said. The opening's address is left out: Honest/K1/FirstOffPad.lean. Nothing of
W's sending. Nothing of a pad in a mask row. On hiding nothing is said. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotData
import Johnson.Desc.ProofFile.Honest.K1.SeatShape
import Johnson.Desc.ProofFile.Honest.Law.LaysRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.HonestTrace (seatOf seatsOf seatAt pairOf mineOf laidRows inSending bzRows
  bzWithFits)
open OnBytes.HonestTrace.U3 (u3Rows u3RowsOf u3Seats)
open ProofFile.Honest.K2 (sendersOf)
open ProofFile.Honest.K8 (zzData zzDataAt bearsZz)
open Johnson.Prover.Send (shapeAt)

/-- An entry's number among the entries that pass a test. -/
theorem filter_at_count {α : Type} (p : α → Bool) : ∀ (L : List α) (m : Nat) (a : α),
    L[m]? = some a → p a = true → (L.filter p)[((L.take m).filter p).length]? = some a
  | [], m, a, h, _ => by simp at h
  | x :: L, 0, a, h, hp => by
    have e : x = a := by simpa using h
    subst e
    simp [List.filter_cons, hp]
  | x :: L, m + 1, a, h, hp => by
    have h' : L[m]? = some a := by simpa using h
    have ih := filter_at_count p L m a h' hp
    by_cases hx : p x = true
    · simp [List.take_succ_cons, List.filter_cons, hx, ih]
    · simp [List.take_succ_cons, List.filter_cons, hx, ih]

/-- **What seatOf's "some s" says.** -/
theorem seat_text {Z : Pub} {G : Ground} {sps : List Spot} {name : String} {seg : Nat}
    {s : OnBytes.HonestTrace.Seat} (h : seatOf Z G sps name seg = some s) :
    ∃ M, s.seg = seg ∧
      (G.first.shape.link.getD seg default).messages[s.array.message]? = some M ∧
      s.shape = M.shape ∧ s.ell = (G.first.codes.base.getD M.shape.code default).ell ∧
      s.link = G.first.shape.link.getD seg default ∧
      inSending s.link s.array.message = some (M.moment, s.addr.msg) ∧
      s.addr.sender.place ∈ sendersOf sps seg := by
  unfold seatOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨a, -, L, hL, M, hM, x, hx, code, hcode, h⟩ := h
  split at h
  · cases h
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨pl, hpl, sp, -, c, -, n, -, rfl⟩ := h
    have eL : G.first.shape.link.getD seg default = L := by
      rw [List.getD_eq_getElem?_getD, hL]
      rfl
    have ex : x = (M.moment, x.2) := by
      unfold inSending at hx
      rw [hM] at hx
      have q := Option.some.inj hx
      rw [← q]
    refine ⟨M, rfl, ?_, rfl, ?_, eL.symm, ?_, List.mem_of_getElem? hpl⟩
    · rw [eL]
      exact hM
    · show code.ell = _
      rw [Array.getD_eq_getD_getElem?, hcode]
      rfl
    · show inSending L a.message = some (M.moment, x.2)
      rw [hx, ← ex]

/-- The same at a member of seatsOf. -/
theorem seats_text {Z : Pub} {G : Ground} {name : String} {s : OnBytes.HonestTrace.Seat}
    (h : s ∈ seatsOf Z G name) :
    ∃ sps seg, seatOf Z G sps name seg = some s := by
  unfold seatsOf at h
  split at h
  · rename_i sps _
    obtain ⟨seg, -, hs⟩ := List.mem_filterMap.1 h
    exact ⟨sps, seg, hs⟩
  · cases h

/-- **A filling by laidData whose seat answers only as pairOf of seatsOf does**: under
codes.lengthsOk, where it lays there is room at the seat, off the pad, in a sampled message. -/
theorem seated_room (Z : Pub) (G : Ground) (name : String) (seat' : MsgAddr → Option (Nat × Nat))
    (hsub : ∀ a p, seat' a = some p → pairOf (seatsOf Z G name) a = some p)
    (heard : MsgAddr → Nat) (V : ArrayVals) (hlen : G.first.codes.lengthsOk = true) {a : MsgAddr}
    {r j : Nat}
    (h : (laidData G.first.codes G.first.shape G.first.layout seat' heard V).lays a r j = true) :
    ∃ s, seatAt (seatsOf Z G name) a = some s ∧ r < s.shape.mainRows ∧ j < s.ell ∧
      (r, j) ∉ padInMain s.ell s.shape ∧ s.shape.answers ≠ 0 := by
  cases hp : seat' a with
  | none =>
    have q := h
    unfold laidData at q
    simp only [hp] at q
    cases q
  | some p =>
    have hq := hsub a p hp
    unfold pairOf at hq
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hq
    have hmem : s ∈ seatsOf Z G name := by
      unfold seatAt at hs
      exact List.mem_of_find?_eq_some hs
    obtain ⟨sps, seg, hso⟩ := seats_text hmem
    obtain ⟨M, e1, hM, e3, e4, -, -, -⟩ := seat_text hso
    rw [← e1] at hM
    obtain ⟨q1, q2, q3, q4⟩ := lays_room _ _ _ seat' heard V hlen hp hM h
    refine ⟨s, hs, ?_, ?_, ?_, ?_⟩
    · rw [e3]
      exact q1
    · rw [e4]
      exact q2
    · rw [e3, e4]
      exact q3
    · rw [e3]
      exact q4

/-- The reads' filling. -/
theorem reads_room (Z : Pub) (G : Ground) (x : ProofFile.Inst) (hlen : G.first.codes.lengthsOk = true)
    {a : MsgAddr} {r j : Nat} (h : (u3RowsOf Z G x).lays a r j = true) :
    ∃ s, seatAt (seatsOf Z G "U3") a = some s ∧ r < s.shape.mainRows ∧ j < s.ell ∧
      (r, j) ∉ padInMain s.ell s.shape ∧ s.shape.answers ≠ 0 :=
  -- "heard" is named because Lean cannot find it: laidData's "lays" does not read it: any value
  -- serves
  seated_room Z G "U3" _ (fun _ _ e => e) (fun _ => 0) _ hlen h

/-- The digits' filling. -/
theorem digitsFilling_room (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat))
    (hlen : G.first.codes.lengthsOk = true) {a : MsgAddr} {r j : Nat}
    (h : (digitsFill Z G mats).lays a r j = true) :
    ∃ s, seatAt (seatsOf Z G "BZ") a = some s ∧ r < s.shape.mainRows ∧ j < s.ell ∧
      (r, j) ∉ padInMain s.ell s.shape ∧ s.shape.answers ≠ 0 := by
  have h' : ((bzRows Z G mats).lays a r j ||
      (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats).lays a r j) = true := h
  rcases Bool.or_eq_true _ _ ▸ h' with hb | hz
  · exact seated_room Z G "BZ" _ (fun _ _ e => e) (fun _ => 0) _ hlen hb
  · refine seated_room Z G "BZ" (bearsZz G.first.layout (pairOf (seatsOf Z G "BZ"))) ?_
      (fun _ => 0) _ hlen hz
    intro a p e
    unfold bearsZz at e
    exact (Option.filter_eq_some_iff.1 e).1

/-- **The lot's data, off the opening's address.** -/
theorem lot_room (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (hlen : G.first.codes.lengthsOk = true) {a : MsgAddr} {r j : Nat}
    (ha : a.sender ≠ firstAddr) (h : (lotData S Z G x).lays a r j = true) :
    ∃ s, (seatAt (seatsOf Z G "BZ") a = some s ∨ seatAt (seatsOf Z G "U3") a = some s) ∧
      r < s.shape.mainRows ∧ j < s.ell ∧ (r, j) ∉ padInMain s.ell s.shape ∧
      s.shape.answers ≠ 0 := by
  have hf : (a.sender == firstAddr) = false := by simpa using ha
  have h' : (if mineOf (seatsOf Z G "BZ") a then (digitsFill Z G (K3.matsOwn G.W)).lays a
      else (u3RowsOf Z G x).lays a) r j = true := by
    have q := h
    unfold lotData lotFill RowData.join at q
    simp only [hf, Bool.false_eq_true, if_false] at q
    exact q
  split at h'
  · obtain ⟨s, hs, q⟩ := digitsFilling_room Z G _ hlen h'
    exact ⟨s, Or.inl hs, q⟩
  · obtain ⟨s, hs, q⟩ := reads_room Z G x hlen h'
    exact ⟨s, Or.inr hs, q⟩

/-- **A PUBLIC TEST AT A SEAT**: the array's message is of the moment t. -/
def momentIs (s : OnBytes.HonestTrace.Seat) (t : Nat) : Bool :=
  (inSending s.link s.array.message).any (·.1 == t)

/-- **Under it the seat's shape is the sender's.** -/
theorem seat_shape_later {Z : Pub} {G : Ground} {sps : List Spot} {name : String} {seg : Nat}
    {s : OnBytes.HonestTrace.Seat} (h : seatOf Z G sps name seg = some s)
    (gp : _root_.Desc.Plain.GPar) (piece t : Nat) (ht : momentIs s t = true) :
    shapeAt (K1.parLater G.first gp seg piece t) s.addr.msg = s.shape := by
  obtain ⟨M, -, hM, e3, -, e5, e6, -⟩ := seat_text h
  unfold momentIs at ht
  rw [e6] at ht
  have hmt : M.moment = t := by simpa using ht
  have hcount : s.addr.msg = (((G.first.shape.link.getD seg default).messages.take
      s.array.message).filter fun N => N.moment == t).length := by
    have q := e6
    unfold inSending at q
    rw [e5, hM] at q
    have q2 := congrArg Prod.snd (Option.some.inj q)
    rw [← hmt]
    exact q2.symm
  rw [e3, hcount]
  exact shapeAt_later G.first gp seg piece t _ M
    (filter_at_count (fun N : Params.ReqMessage => N.moment == t) _ _ M hM (by simp [hmt]))

/-- The seat's segment is the link of its address's place. -/
theorem seat_seg {Z : Pub} {G : Ground} {sps : List Spot} {name : String} {seg : Nat}
    {s : OnBytes.HonestTrace.Seat} (h : seatOf Z G sps name seg = some s) :
    s.addr.sender.place.link = some seg := by
  obtain ⟨_, -, -, -, -, -, -, hm⟩ := seat_text h
  unfold sendersOf at hm
  obtain ⟨sp, hsp, e⟩ := List.mem_map.1 hm
  have q := (List.mem_filter.1 hsp).2
  rw [Bool.and_eq_true, beq_iff_eq] at q
  rw [← e]
  exact q.1

/-- **THE JOIN AT A LATER PLACE's PLAN**: where the lot's data lay at the message number k of the
sending at a later place: a row below the SENDER's main rows; a place below the SENDER's length; off
the pad; a sampled message. hlen: the codes' lengths are powers of two. hne: the address is not the
opening's. hmom: the public test momentIs at the seat that stands at the address. -/
theorem later_lays_room (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (gp : _root_.Desc.Plain.GPar) (l piece t k : Nat) (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece t).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ s, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ =
        some s ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ =
        some s) → momentIs s t = true) {r j : Nat}
    (h : (lotData S Z G x).lays ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ r j = true) :
    r < (shapeAt (K1.parLater G.first gp l piece t) k).mainRows ∧
      j < ((K1.parLater G.first gp l piece t).codes.base.getD
        (shapeAt (K1.parLater G.first gp l piece t) k).code default).ell ∧
      (r, j) ∉ padInMain ((K1.parLater G.first gp l piece t).codes.base.getD
        (shapeAt (K1.parLater G.first gp l piece t) k).code default).ell
        (shapeAt (K1.parLater G.first gp l piece t) k) ∧
      (shapeAt (K1.parLater G.first gp l piece t) k).answers ≠ 0 := by
  obtain ⟨s, hs, q1, q2, q3, q4⟩ := lot_room S Z G x hlen hne h
  have hm := hmom s hs
  -- the seat, its address, its text
  have key : ∀ name, seatAt (seatsOf Z G name)
      ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ = some s →
      shapeAt (K1.parLater G.first gp l piece t) k = s.shape ∧
        s.ell = (G.first.codes.base.getD s.shape.code default).ell := by
    intro name hsa
    unfold seatAt at hsa
    have hmem := List.mem_of_find?_eq_some hsa
    have hadr : s.addr = ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ := by
      have q := List.find?_some hsa
      exact beq_iff_eq.1 q
    obtain ⟨sps, seg, hso⟩ := seats_text hmem
    have hseg := seat_seg hso
    rw [hadr] at hseg
    have hl : l = seg := Option.some.inj hseg
    subst hl
    have hsh := seat_shape_later hso gp piece t hm
    rw [hadr] at hsh
    obtain ⟨M, -, -, e3, e4, -, -, -⟩ := seat_text hso
    exact ⟨hsh, by rw [e4, e3]⟩
  obtain ⟨e1, e2⟩ : shapeAt (K1.parLater G.first gp l piece t) k = s.shape ∧
      s.ell = (G.first.codes.base.getD s.shape.code default).ell := by
    rcases hs with hs | hs
    · exact key _ hs
    · exact key _ hs
  rw [parLater_codes, e1, ← e2]
  exact ⟨q1, q2, q3, q4⟩

/-- The same in the library's plain test's form. -/
theorem later_lays_off_padB (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (gp : _root_.Desc.Plain.GPar) (l piece t k : Nat) (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece t).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ s, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ =
        some s ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ =
        some s) → momentIs s t = true) {r j : Nat}
    (h : (lotData S Z G x).lays ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ r j = true) :
    padB (K1.parLater G.first gp l piece t).codes (shapeAt (K1.parLater G.first gp l piece t) k)
      false r j = false := by
  obtain ⟨-, q2, q3, q4⟩ := later_lays_room S Z G x gp l piece t k hlen hne hmom h
  exact padB_of_room _ _ q2 q3 q4

/-- **THE SEAT's TEST HOLDS AT THE SENDER's OWN SHAPE AND CODES**: the clause of placeSeatOk
(Honest/K1/PlaceJob.lean) on the pad: under later_lays_room's three premises (hlen, hne, hmom). -/
theorem later_clear (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (gp : _root_.Desc.Plain.GPar) (l piece t k : Nat) (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece t).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ s, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ =
        some s ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ =
        some s) → momentIs s t = true) :
    (lotData S Z G x).clear ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩
      ((K1.parLater G.first gp l piece t).codes.base.getD
        (shapeAt (K1.parLater G.first gp l piece t) k).code default).ell
      (shapeAt (K1.parLater G.first gp l piece t) k) = true := by
  have key : ∀ r j, (r, j) ∈ padInMain ((K1.parLater G.first gp l piece t).codes.base.getD
        (shapeAt (K1.parLater G.first gp l piece t) k).code default).ell
        (shapeAt (K1.parLater G.first gp l piece t) k) ∨
      (shapeAt (K1.parLater G.first gp l piece t) k).mainRows ≤ r ∨
      ((K1.parLater G.first gp l piece t).codes.base.getD
        (shapeAt (K1.parLater G.first gp l piece t) k).code default).ell ≤ j →
      (lotData S Z G x).lays ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ r j = false := by
    intro r j hc
    cases hl : (lotData S Z G x).lays ⟨⟨(K1.parLater G.first gp l piece t).place, 0⟩, k⟩ r j with
    | false => rfl
    | true =>
      obtain ⟨q1, q2, q3, -⟩ := later_lays_room S Z G x gp l piece t k hlen hne hmom hl
      rcases hc with hc | hc | hc
      · exact absurd hc q3
      · omega
      · omega
  unfold RowData.clear
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨fun p hp => key p.1 p.2 (Or.inl hp), key _ _ (Or.inr (Or.inl (Nat.le_refl _)))⟩,
    fun r _ => key _ _ (Or.inr (Or.inr (Nat.le_refl _)))⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.filter_at_count
#print axioms ProofFile.Honest.K1.seat_text
#print axioms ProofFile.Honest.K1.seats_text
#print axioms ProofFile.Honest.K1.seated_room
#print axioms ProofFile.Honest.K1.reads_room
#print axioms ProofFile.Honest.K1.digitsFilling_room
#print axioms ProofFile.Honest.K1.lot_room
#print axioms ProofFile.Honest.K1.momentIs
#print axioms ProofFile.Honest.K1.seat_shape_later
#print axioms ProofFile.Honest.K1.seat_seg
#print axioms ProofFile.Honest.K1.later_lays_room
#print axioms ProofFile.Honest.K1.later_lays_off_padB
#print axioms ProofFile.Honest.K1.later_clear
