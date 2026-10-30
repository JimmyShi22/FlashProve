-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SeatsThereOf.lean: SeatsThere ("the mask row's message is seated; each
array below n is there": Johnson/Desc/First/Link/Law/SeatsRide.lean) CUT INTO FACTS ON ONE STATE,
each with a payer of its own. Theorems with their proofs; one is a negative test.

  seatsThere_nil   A NEGATIVE TEST: at the empty list of seats SeatsThere is false at every state.
                   So at free numbers N "SeatsThere (N.group m) n s" cannot be had from what is said
                   of the state alone.
  whereIs_mem, maskAt_mem   what the frame's whereIs | maskAt answer is a number of one of the
                   frame's two lists, own and keptBefore
  place_of_member  **the table's fixed test membersHeld ties N to the book**: where a class of rows
                   of segment m is open and its group is made, a member's place is in N.group m
  FrameFinds a n   the frame's half, on the open part alone: maskAt answers; each array below n has
                   a row of the layout, and whereIs answers at its message
  seatsThere_of    SeatsThere own n s from: a part is there · FrameFinds · every number of the
                   frame's two lists sits, by the book, at a seat of own
  seatsThere_held  **SeatsThere (N.group m) n s** from: a part is there · FrameFinds · membersHeld ·
                   a class of rows of m is open · the group is made · the frame's two lists are
                   among the group's members

Limits. ON ONE STATE: nothing on "reached". No premise is shown at a state here. Nothing on
soundness.

-/
import Johnson.Desc.First.Link.Law.SeatsRide
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS maskSeat maskAt arrayIn seatAt)
open VerifiableInference.Desc.First (S Item Numbers membersHeld rowSegs sameMembers)

/-- **A negative test**: no state has its seats in the empty list. -/
theorem seatsThere_nil (n : ℕ) (s : S) : ¬ SeatsThere [] n s := by
  rintro ⟨a, _, h, _⟩
  unfold maskSeat at h
  cases e : maskAt a.L.check.frame with
  | none => rw [e] at h; exact nomatch h
  | some o =>
    rw [e] at h
    have h' : (seatAt [] a.d.book o).isSome = true := h
    unfold seatAt at h'
    cases e' : a.d.book.place[o]? with
    | none => rw [e'] at h'; exact nomatch h'
    | some x => rw [e'] at h'; exact nomatch h'

/-- What whereIs answers is a number of one of the frame's two lists. -/
theorem whereIs_mem {f : ReqFrame} {born message o : ℕ} (h : f.whereIs born message = some o) :
    o ∈ f.own.toList ∨ o ∈ f.keptBefore.toList := by
  unfold ReqFrame.whereIs at h
  split at h
  · exact nomatch h
  · split at h
    · exact Or.inl (Array.mem_toList_iff.2 (Array.mem_of_getElem? h))
    · obtain ⟨i, _, hi⟩ := Option.bind_eq_some_iff.1 h
      exact Or.inr (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))

theorem maskAt_mem {f : ReqFrame} {o : ℕ} (h : maskAt f = some o) :
    o ∈ f.own.toList ∨ o ∈ f.keptBefore.toList := by
  unfold maskAt at h
  obtain ⟨i, _, hi⟩ := Option.bind_eq_some_iff.1 h
  exact whereIs_mem hi

/-- **membersHeld ties the numbers to the book.** -/
theorem place_of_member {N : Numbers} {O : List Item} {s : S} {m o : ℕ} {G : OnBytes.Group}
    (hM : membersHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G) (ho : o ∈ G.members.toList) :
    ∃ x, s.book.place[o]? = some x ∧ x ∈ N.group m := by
  unfold membersHeld at hM
  have h := List.all_eq_true.1 hM m hm
  rw [hG] at h
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  have hp := List.all_eq_true.1 h1 o ho
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hp
  refine ⟨x, hx, ?_⟩
  unfold sameMembers at h2
  have h3 := List.all_eq_true.1 ((Bool.and_eq_true _ _).mp h2).1 x
    (List.mem_filterMap.2 ⟨o, ho, hx⟩)
  have h4 : x ∈ (List.range 3).flatMap fun t =>
      if O.contains (.pin m t) then N.sent m t else [] := by simpa using h3
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.1 h4
  have ht3 : t < 3 := List.mem_range.1 ht
  split at hxt
  · unfold Numbers.group
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _ hxt)
    · exact List.mem_append_left _ (List.mem_append_right _ hxt)
    · exact List.mem_append_right _ hxt
  · exact absurd hxt List.not_mem_nil

/-- **The frame's half**: on the open part alone. -/
def FrameFinds (a : K9.Part) (n : ℕ) : Prop :=
  (maskAt a.L.check.frame).isSome = true ∧ ∀ i, i < n → ∃ b A, a.L.arrayOf[i]? = some b ∧
    reqArray a.L.check.rows.layout b.1 b.2 = some A ∧
    (a.L.check.frame.whereIs b.1 A.message).isSome = true

/-- **SeatsThere from three facts.** -/
theorem seatsThere_of (own : List (ℕ × ℕ)) (n : ℕ) {s : S} {a : K9.Part}
    (ha : atS.get? s = some a) (hF : FrameFinds a n)
    (hP : ∀ o, o ∈ a.L.check.frame.own.toList ∨ o ∈ a.L.check.frame.keptBefore.toList →
      ∃ x, a.d.book.place[o]? = some x ∧ x ∈ own) : SeatsThere own n s := by
  have seat : ∀ o, o ∈ a.L.check.frame.own.toList ∨ o ∈ a.L.check.frame.keptBefore.toList →
      (seatAt own a.d.book o).isSome = true := by
    intro o ho
    obtain ⟨x, hx, hxo⟩ := hP o ho
    unfold seatAt
    rw [hx]
    have hc : own.contains x = true := by simpa using hxo
    show (if own.contains x = true then some x else none).isSome = true
    rw [if_pos hc]
    rfl
  refine ⟨a, ha, ?_, fun i hi => ?_⟩
  · obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hF.1
    unfold maskSeat
    rw [ho]
    exact seat o (maskAt_mem ho)
  · obtain ⟨b, A, h1, h2, h3⟩ := hF.2 i hi
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h3
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (seat o (whereIs_mem ho))
    unfold arrayIn
    rw [h1]
    show ((reqArray a.L.check.rows.layout b.1 b.2).bind fun A =>
      (a.L.check.frame.whereIs b.1 A.message).bind fun o =>
        (seatAt own a.d.book o).map fun _ => A).isSome = true
    rw [h2]
    show ((a.L.check.frame.whereIs b.1 A.message).bind fun o =>
      (seatAt own a.d.book o).map fun _ => A).isSome = true
    rw [ho]
    show ((seatAt own a.d.book o).map fun _ => A).isSome = true
    rw [hx]
    rfl

/-- The open part's book is the state's. -/
theorem book_of_part {s : S} {a : K9.Part} (ha : atS.get? s = some a) : a.d.book = s.book := by
  have h := K9.segAt_of_atS s a ha
  unfold K9.segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        rw [← h]

/-- **SeatsThere at the numbers' own list of segment m's seats.** -/
theorem seatsThere_held {N : Numbers} {O : List Item} {s : S} {a : K9.Part} {m n : ℕ}
    {G : OnBytes.Group} (ha : atS.get? s = some a) (hF : FrameFinds a n)
    (hM : membersHeld N O s = true) (hm : m ∈ rowSegs O)
    (hG : s.st.groups[N.groupAt m]? = some G)
    (hIn : ∀ o, o ∈ a.L.check.frame.own.toList ∨ o ∈ a.L.check.frame.keptBefore.toList →
      o ∈ G.members.toList) : SeatsThere (N.group m) n s :=
  seatsThere_of (N.group m) n ha hF fun o ho => by
    rw [book_of_part ha]
    exact place_of_member hM hm hG (hIn o ho)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.seatsThere_nil
#print axioms VerifiableInference.Desc.LinkJoin.whereIs_mem
#print axioms VerifiableInference.Desc.LinkJoin.place_of_member
#print axioms VerifiableInference.Desc.LinkJoin.seatsThere_of
#print axioms VerifiableInference.Desc.LinkJoin.seatsThere_held
