-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SeatReach.lean: FOUR GENERAL LAWS ON THREE SMALL ROUTINES OF
THE FRAME's: WHAT THE SEAT OF ONE SENDING (`K1.momentSeat`) ANSWERS AT ITS OWN SENDER AND AT
ANOTHER; WHAT THE SEAT OVER A LIST OF SENDINGS (`K2.seatBy`) ANSWERS; AND THAT THE COUNT OF A
MOMENT's MESSAGES (`msgNo`) REACHES EVERY MESSAGE OF THAT MOMENT. On public data alone. No head, no
sizes, no premise on files. CONDITIONAL only on what each statement names. Lemmas.

What it is for. The premise's form `LaysFilling` (LaysFilling.lean in this folder) has a public
field, reach: each array that the values have lies in a message that is seated at an address. A seat
over all the switches' sendings lies typed (`K2.switchSeat`,
Johnson/Desc/ProofFile/Honest/K2/OwnData.lean): it is `K2.seatBy` at a list. These four laws are the
general half of "that seat reaches".

Main names:
  `seatBy_at`: **where the list's addresses are pairwise apart, at an entry (ad, l, fr) of the list
    the seat answers (l, m) at the address (ad, fr + k)**, m the k-th message of moment 0 of segment
    l.
  `msgNo_of_moment`: each message of a segment is the k-th of its moment, for some k.
  `momentSeat_at`, `momentSeat_other`: the seat of one sending at its own sender; at another:
    nothing.

Limits. That the switches' addresses are pairwise apart, that a switch leads into a given segment,
and that an array lies in a message of moment 0 are not shown here. `seatBy_at` is at moment 0, as
`K2.seatBy` is. `msgNo_of_moment` does not say which k. These are lemmas on the frame's routines: if
the frame has or wants their like, the frame's are the ones to keep.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.OwnData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5

/-- **The seat of one sending, at its own sender.** Conditional: hk: m is the k-th message of moment
t of segment l. -/
theorem momentSeat_at {s : OnBytes.Params.ReqShape} (sender : Addr) {l t k m : ℕ} (fr : ℕ)
    (hk : msgNo s l t k = some m) :
    K1.momentSeat s sender l t fr ⟨sender, fr + k⟩ = some (l, m) := by
  have c : ((⟨sender, fr + k⟩ : MsgAddr).sender == sender) = true ∧
      fr ≤ (⟨sender, fr + k⟩ : MsgAddr).msg := ⟨beq_self_eq_true _, Nat.le_add_right _ _⟩
  unfold K1.momentSeat
  rw [if_pos c]
  show (msgNo s l t (fr + k - fr)).map (fun m => (l, m)) = some (l, m)
  rw [Nat.add_sub_cancel_left, hk]
  rfl

/-- **At another sender it answers nothing.** -/
theorem momentSeat_other (s : OnBytes.Params.ReqShape) {sender : Addr} (l t fr : ℕ) {a : MsgAddr}
    (h : a.sender ≠ sender) : K1.momentSeat s sender l t fr a = none := by
  unfold K1.momentSeat
  rw [if_neg]
  intro c
  exact h (beq_iff_eq.1 c.1)

/-- **THE SEAT OVER A LIST OF SENDINGS, AT AN ENTRY OF THE LIST.** Conditional: hd: the list's
addresses are pairwise apart; hx: (ad, l, fr) is an entry; hk: m is the k-th message of moment 0 of
segment l. -/
theorem seatBy_at {s : OnBytes.Params.ReqShape} {L : List (Addr × ℕ × ℕ)}
    (hd : L.Pairwise fun x y => x.1 ≠ y.1) {ad : Addr} {l fr : ℕ} (hx : (ad, l, fr) ∈ L)
    {k m : ℕ} (hk : msgNo s l 0 k = some m) : K2.seatBy s L ⟨ad, fr + k⟩ = some (l, m) := by
  induction L with
  | nil => cases hx
  | cons x L ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hd
    unfold K2.seatBy
    rw [List.findSome?_cons]
    rcases List.mem_cons.1 hx with e | hx'
    · rw [← e, momentSeat_at ad fr hk]
    · rw [momentSeat_other s x.2.1 0 x.2.2 (a := ⟨ad, fr + k⟩) (h1 _ hx').symm]
      exact ih h2 hx'

/-- **Each message of a segment is the k-th of its moment, for some k.** Conditional: hM: M is
message number m of segment l. -/
theorem msgNo_of_moment {s : OnBytes.Params.ReqShape} {l m : ℕ} {M : OnBytes.Params.ReqMessage}
    (hM : (s.link.getD l default).messages[m]? = some M) : ∃ k, msgNo s l M.moment k = some m := by
  have h1 : (M, m) ∈ (s.link.getD l default).messages.zipIdx :=
    List.mem_zipIdx_iff_getElem?.2 hM
  have h2 : (M, m) ∈ (s.link.getD l default).messages.zipIdx.filter
      fun x => x.1.moment == M.moment := List.mem_filter.2 ⟨h1, beq_self_eq_true _⟩
  obtain ⟨k, hk⟩ := List.getElem?_of_mem h2
  refine ⟨k, ?_⟩
  unfold msgNo
  rw [hk]
  rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.momentSeat_at
#print axioms ProofFile.Honest.K5.momentSeat_other
#print axioms ProofFile.Honest.K5.seatBy_at
#print axioms ProofFile.Honest.K5.msgNo_of_moment
