-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnDataApart.lean: the kind "the code switch" (K2): THE DATA OF
THE SWITCHES' OWN MESSAGES (Honest/K2/OwnData.lean) STANDS APART FROM EVERY OTHER KIND's: at an
address whose sender's place is not of this kind there is no seat, so THE JOINED FILLING IS THE
OTHER LOT's THERE, IN ALL FOUR FIELDS. Statements with their proofs; no definition.

WHY. `withSwitchData S D` lays `switchData` in front of another lot's data D. That lot's own tests
and statements speak at D. They speak at the joined filling too wherever it is D's: that wants a
payer for "no seat here", and the like for each thing that a test reads, not for `RowData.at_`
alone.

  `switchPlaces_kind`   every place that `switchPlaces` makes is of the kind K2
  `switchSeat_none`  AT A SENDER WHOSE PLACE IS NOT OF THE KIND K2 THERE IS NO SEAT
  `with_else_heard`, `with_else_lays`, `with_else_entry`, `with_else_test`   off a seat each of the
                    joined filling's four fields is D's
  `with_else_ready`  so `RowData.readyAt` is (`RowData.at_`: `with_else`, Honest/K2/OwnData.lean)
  `with_other_kind`  AT A SENDER THAT IS NO SWITCH's: the four fields, `at_` and `readyAt` are D's
  `switchSeat_own`   at a place of the kind, at its own address number m: there is a seat wherever
                    the segment into which the switch leads has an m-th message of moment 0: the
                    payer of the premise of `with_own`, `with_own_lays`, `with_own_ready`

Limits. WHICH seat stands at a switch's own address is not said: `seatBy` takes the first entry of
its list that serves, and that no two places have one address is not shown. Nothing is said of D: in
particular not what D lays at a switch's address, which the joined filling never reads at a seat and
does read at the carrying message's, a copy's and the fresh mask's numbers. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.OwnData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz)

variable {Xi : Type}

/-- Every place that `switchPlaces` makes is of the kind K2. -/
theorem switchPlaces_kind (Z : Pub) (G : Ground) (p : SwitchPlace) (hp : p ∈ switchPlaces Z G) :
    p.place.kind = .K2 := by
  unfold switchPlaces at hp
  split at hp
  · simp only [List.mem_map, List.mem_filter] at hp
    obtain ⟨sp, ⟨_, hk⟩, rfl⟩ := hp
    exact eq_of_beq hk
  · simp at hp

/-- **At a sender whose place is not of the kind K2 there is no seat.** -/
theorem switchSeat_none (Z : Pub) (G : Ground) (a : MsgAddr) (h : a.sender.place.kind ≠ .K2) :
    switchSeat Z G a = none := by
  unfold switchSeat seatBy
  rw [List.findSome?_eq_none_iff]
  intro x hx
  unfold ownSeats at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  unfold K1.momentSeat
  refine if_neg fun hc => h ?_
  have e : a.sender = ⟨p.place, 0⟩ := eq_of_beq hc.1
  rw [e]
  exact switchPlaces_kind Z G p hp

section
variable (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi) (a : MsgAddr)

theorem with_else_heard (h : (switchSeat Z G a).isSome = false) :
    (withSwitchData S D Z G x).heardAt a = (D Z G x).heardAt a := by
  unfold withSwitchData RowData.join
  simp only [h, Bool.false_eq_true, if_false]

theorem with_else_lays (h : (switchSeat Z G a).isSome = false) :
    (withSwitchData S D Z G x).lays a = (D Z G x).lays a := by
  unfold withSwitchData RowData.join
  simp only [h, Bool.false_eq_true, if_false]

theorem with_else_entry (h : (switchSeat Z G a).isSome = false) (R : Readers)
    (hd : List Fmt.Drawn) :
    (withSwitchData S D Z G x).entry R hd a = (D Z G x).entry R hd a := by
  unfold withSwitchData RowData.join
  simp only [h, Bool.false_eq_true, if_false]

theorem with_else_test (h : (switchSeat Z G a).isSome = false) (hd : List Fmt.Drawn) :
    (withSwitchData S D Z G x).ready hd a = (D Z G x).ready hd a := by
  unfold withSwitchData RowData.join
  simp only [h, Bool.false_eq_true, if_false]

theorem with_else_ready (h : (switchSeat Z G a).isSome = false) (hd : List Fmt.Drawn) :
    (withSwitchData S D Z G x).readyAt hd a = (D Z G x).readyAt hd a := by
  unfold RowData.readyAt RowData.heardOk
  rw [with_else_heard S D Z G x a h, with_else_test S D Z G x a h]

/-- **At a sender that is no switch's the joined filling is the other lot's.** -/
theorem with_other_kind (h : a.sender.place.kind ≠ .K2) :
    (withSwitchData S D Z G x).heardAt a = (D Z G x).heardAt a ∧
      (withSwitchData S D Z G x).lays a = (D Z G x).lays a ∧
      (∀ R hd, (withSwitchData S D Z G x).entry R hd a = (D Z G x).entry R hd a) ∧
      (∀ hd, (withSwitchData S D Z G x).ready hd a = (D Z G x).ready hd a) ∧
      (∀ R hd r j, (withSwitchData S D Z G x).at_ R hd a r j = (D Z G x).at_ R hd a r j) ∧
      ∀ hd, (withSwitchData S D Z G x).readyAt hd a = (D Z G x).readyAt hd a := by
  have h0 : (switchSeat Z G a).isSome = false := by
    rw [switchSeat_none Z G a h]
    rfl
  exact ⟨with_else_heard S D Z G x a h0, with_else_lays S D Z G x a h0,
    with_else_entry S D Z G x a h0, with_else_test S D Z G x a h0,
    fun R hd r j => with_else S D Z G x R hd a r j h0, with_else_ready S D Z G x a h0⟩

end

/-- **At a place of the kind, at its own address number m, there is a seat** wherever the segment
into which the switch leads has an m-th message of moment 0. -/
theorem switchSeat_own (Z : Pub) (G : Ground) (p : SwitchPlace) (hp : p ∈ switchPlaces Z G)
    (m : Nat) (hm : (msgNo G.first.shape p.link 0 m).isSome = true) :
    (switchSeat Z G (p.ownAddr m)).isSome = true := by
  unfold switchSeat seatBy
  rw [List.findSome?_isSome_iff]
  refine ⟨(⟨p.place, 0⟩, p.link, 1 + p.sizes.kept.length), ?_, ?_⟩
  · unfold ownSeats
    exact List.mem_map.2 ⟨p, hp, rfl⟩
  · unfold K1.momentSeat SwitchPlace.ownAddr
    rw [if_pos ⟨beq_self_eq_true _, Nat.le_add_right _ _⟩, Option.isSome_map]
    show (msgNo G.first.shape p.link 0 (1 + p.sizes.kept.length + m -
      (1 + p.sizes.kept.length))).isSome = true
    rw [Nat.add_sub_cancel_left]
    exact hm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switchPlaces_kind
#print axioms ProofFile.Honest.K2.Law.switchSeat_none
#print axioms ProofFile.Honest.K2.Law.with_else_heard
#print axioms ProofFile.Honest.K2.Law.with_else_lays
#print axioms ProofFile.Honest.K2.Law.with_else_entry
#print axioms ProofFile.Honest.K2.Law.with_else_test
#print axioms ProofFile.Honest.K2.Law.with_else_ready
#print axioms ProofFile.Honest.K2.Law.with_other_kind
#print axioms ProofFile.Honest.K2.Law.switchSeat_own
