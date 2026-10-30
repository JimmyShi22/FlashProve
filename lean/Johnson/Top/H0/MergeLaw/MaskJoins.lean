-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskJoins.lean: what the lemma that joins the two sentences for "weights" at
the output head's segment still asks of the verifier's state in front of the merge of the claims on
the committed table: "the state holds the mask row's seat". Here it follows from an accept of the
test `maskAtB` (MaskRow.lean) and two closed premises; and the merge's number of slots is the number
of entries of the segment's mask row that are in use. Theorems with their proofs, and small values.

Why. Two readers of segment 24's mask row off one witness are shown to be one where the state holds
the mask row's seat (the condition MaskSeatAt and the theorem maskRows_one of
Johnson/Desc/Kinds/Law/MaskRowsOne.lean). That condition was shown at no state in front of the
merge. `maskAtB` is a test with code on the state which is shown elsewhere along the states that the
verifier reaches.

THE CONDITION IS WRITTEN OUT. This file imports nothing of that other folder, and no definition
stands here: the conclusions are the body of MaskSeatAt arr N n rb s, sign for sign:
  ∃ aK o x, K9.segAt? s = some aK ∧ K9L.maskOracle aK.L.check.frame = some o ∧ K9.seatAt (N.sent 24
    0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧ aK.d.st.rowBits o .mask = rb.
That it is that body is held by Lean in MaskJoinsNamed.lean, which imports both files.

Main names:
  `seat_in_every`: a message's seat, found in one list of seats, is its seat in every list that
    holds it. (Statement and proof follow seatAt_wider of MaskRowsOne.lean line for line.)
  `sent_in_group`: a seat of a segment's first sending is a seat of its group.
  `maskSeat_of_test`: AT ONE STATE: an accept of `maskAtB own xs R s`, at any list own, with xs ∈
    N.sent 24 0 and arr xs.1 xs.2 = n, gives the condition at rb := R.
  `maskSeat_reached`: the same at the states in front of a sub-protocol, in the form in which the
    merge's law takes a fact on the state in front: the table's condition at border k, a condition
    Rch k, and "not: the mark is not none". Rch is a parameter of which nothing is asked here: at a
    condition that never holds the theorem is idle. hmask has the form of the conclusion of
    `maskAtB_reached` (MaskReached.lean): whatever ends in that form serves.
  `maskSeat_of_maskAt`, `maskSeat_of_front`: the same from the condition `MaskAt` (MaskRow.lean), of
    which `maskAtB` is the test, at the member's seat; and so from `MergeFront` (EntryFront.lean),
    whose first fact it is, at the states in front of the merge: whoever holds that structure there
    holds the condition, and no second fact on the family is wanted.
  `nMsg_le_ns`: the merge's number of slots, at the maker's parameters, is at most (it is) the
    public parameters' `H.ns`.
  `JoinsToy`: small values: the lemma on seats at a book of one message; two negative tests.

Limits. An implication: where `maskAtB` rejects, `maskSeat_of_test` asks nothing; where no unmarked
state meets Rch k and the table's condition, `maskSeat_reached` speaks of no state. No state at
which `maskAtB` accepts is exhibited here; of the two negative tests here the one on the blank state
falls at the test's first clause and probes neither the seat nor R. (An evaluation that is not
called here: a print of the lines of a file not in this library at one honest
full-size run over synthetic
weights has: the test accepts at the seat (73, 2) and R = 0, and rejects at R + 1, at the seat (73,
0), at the group of the segment in front, at twice the mask rows, at border 0 and behind the last
sub-protocol.) hmask is shown at no family here. THE TWO CLOSED PREMISES, at the release's numbers,
the seat (73, 2) and n := the number of message 0 of segment 24, are theorems under the structure of
conditions of the full size: Johnson/HB/LLHARD/MaskSeatWritten.lean; on the second hangs whether the
condition can be met at all, since two sides name the mask row's message in two ways. THE JOINING
LEMMA's OWN PREMISE on the two readers is not stated here. It asks their equation at every state
that meets a condition on the state alone (WaK6, seven clauses). That is not shown, and we hold it
false: WaK6 reads neither the frame, nor the book of trees, nor the messages' shapes, so the seat is
free under it; no counterexample is typed. The form that closes it: the written-out condition as an
eighth clause of that condition on the state. The equation then follows by maskRows_one and
`nMsg_le_ns` (WtJoinsSeat.lean), and the new clause is wanted where the condition on the state is
wanted: at the reached, unmarked states in front of the merge under the table's condition, which is
`maskSeat_reached`'s conclusion to the letter. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskRow
import Johnson.Top.H0.MergeLaw.EntryFront
import Johnson.Top.H0.MergeLaw.PlanNumsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Place)

/-- A message's seat, found in one list of seats, is its seat in every list that holds it. -/
theorem seat_in_every (own own' : List (ℕ × ℕ)) (book : OnBytes.TreeBook) (o : ℕ) (x : ℕ × ℕ)
    (e : K9.seatAt own book o = some x) (hx : x ∈ own') : K9.seatAt own' book o = some x := by
  unfold K9.seatAt at e ⊢
  obtain ⟨y, hy, e2⟩ := Option.bind_eq_some_iff.1 e
  rw [hy]
  split at e2
  · obtain rfl := Option.some.inj e2
    show (if own'.contains y then some y else none) = some y
    rw [if_pos (by simpa using hx)]
  · cases e2

/-- A seat of a segment's first sending is a seat of its group. -/
theorem sent_in_group (N : Numbers) (m : ℕ) {x : ℕ × ℕ} (hs : x ∈ N.sent m 0) : x ∈ N.group m :=
  List.mem_append_left _ (List.mem_append_left _ hs)

/-- **The state holds the mask row's seat, from an accept of the test.** own: any list of seats. -/
theorem maskSeat_of_test (arr : ℕ → ℕ → ℕ) (N : Numbers) {own : List (ℕ × ℕ)} {xs : ℕ × ℕ}
    {R n : ℕ} {s : S} (h : maskAtB own xs R s = true) (hs : xs ∈ N.sent 24 0)
    (hn : arr xs.1 xs.2 = n) :
    ∃ (aK : K9.Part) (o : ℕ) (x : ℕ × ℕ), K9.segAt? s = some aK ∧
      K9L.maskOracle aK.L.check.frame = some o ∧
      K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
      aK.d.st.rowBits o .mask = R := by
  unfold maskAtB at h
  cases e9 : K9.segAt? s with
  | none => simp [e9] at h
  | some a9 =>
    rw [e9] at h
    simp only [Option.any_some] at h
    cases eo : K9L.maskOracle a9.L.check.frame with
    | none => simp [eo] at h
    | some o =>
      rw [eo] at h
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨a9, o, xs, rfl, eo, seat_in_every own _ _ o xs h.1 hs, sent_in_group N 24 hs, hn, h.2⟩

/-- **The same at the states in front of a sub-protocol**, in the form in which the merge's law
takes a fact on the state in front. -/
theorem maskSeat_reached {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (arr : ℕ → ℕ → ℕ) (N : Numbers) (own : List (ℕ × ℕ)) (xs : ℕ × ℕ)
    (R n : ℕ) (hs : xs ∈ N.sent 24 0) (hn : arr xs.1 xs.2 = n)
    (hmask : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → maskAtB own xs R a.1 = true) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      ∃ (aK : K9.Part) (o : ℕ) (x : ℕ × ℕ), K9.segAt? a.1 = some aK ∧
        K9L.maskOracle aK.L.check.frame = some o ∧
        K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
        aK.d.st.rowBits o .mask = R :=
  fun z a hon hr hm =>
    maskSeat_of_test arr N (hmask z a hon hr (Classical.not_not.1 hm)) hs hn

/-- The same from the condition `MaskAt`, of which `maskAtB` is the test: at the member's seat. -/
theorem maskSeat_of_maskAt (arr : ℕ → ℕ → ℕ) (N : Numbers) {own : List (ℕ × ℕ)} {xM : Sound.Mem}
    {R n : ℕ} {s : S} (h : MaskAt own xM R s) (hs : Sound.seatOf xM ∈ N.sent 24 0)
    (hn : arr (Sound.seatOf xM).1 (Sound.seatOf xM).2 = n) :
    ∃ (aK : K9.Part) (o : ℕ) (x : ℕ × ℕ), K9.segAt? s = some aK ∧
      K9L.maskOracle aK.L.check.frame = some o ∧
      K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
      aK.d.st.rowBits o .mask = R := by
  obtain ⟨a9, o, e9, eo, h1, h2⟩ := h
  exact ⟨a9, o, Sound.seatOf xM, e9, eo, seat_in_every own _ _ o _ h1 hs, sent_in_group N 24 hs, hn,
    h2⟩

/-- **So whoever holds `MergeFront` at the states in front of the merge holds the condition there**:
no second fact on the family is wanted. hFr has the form in which the merge's law takes
`MergeFront`. -/
theorem maskSeat_of_front {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (arr : ℕ → ℕ → ℕ) (N : Numbers) (own : List (ℕ × ℕ))
    (xM : Sound.Mem) (R ni n : ℕ) (hs : Sound.seatOf xM ∈ N.sent 24 0)
    (hn : arr (Sound.seatOf xM).1 (Sound.seatOf xM).2 = n)
    (hFr : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront own xM R ni a.1) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      ∃ (aK : K9.Part) (o : ℕ) (x : ℕ × ℕ), K9.segAt? a.1 = some aK ∧
        K9L.maskOracle aK.L.check.frame = some o ∧
        K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
        aK.d.st.rowBits o .mask = R :=
  fun z a hon hr hm => maskSeat_of_maskAt arr N (hFr z a hon hr hm).mask hs hn

/-- **The merge's number of slots is at most the number of entries of the segment's mask row that
are in use**, at the maker's parameters: the two are one number. -/
theorem nMsg_le_ns {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G₀) : (K11.parOf Z G₀).nMsg ≤ Z.p.X.H.ns :=
  Nat.le_of_eq (parOf_nMsg h)

/-! ## Small values -/

namespace JoinsToy

/-- A book with one message, at the seat (7, 2). -/
def book1 : OnBytes.TreeBook := { place := #[(7, 2)] }

/-- The seat is found in a list that holds it, -/
theorem seat_found : K9.seatAt [(7, 0), (7, 2)] book1 0 = some (7, 2) := by decide

/-- and so, by the lemma, in another list that holds it. -/
theorem seat_found_wider : K9.seatAt [(7, 2), (9, 9)] book1 0 = some (7, 2) :=
  seat_in_every _ _ _ _ _ seat_found (by decide)

/-- NEGATIVE TEST: in a list that does not hold it the seat is not found: the premise hx is needed.
-/
theorem seat_lost : K9.seatAt [(7, 0), (9, 9)] book1 0 = none := by decide

/-- NEGATIVE TEST: the blank state has no open segment: the test rejects it. -/
theorem blank_rejected : maskAtB [(7, 2)] (7, 2) 0 S.blank = false := by decide

end JoinsToy

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.seat_in_every
#print axioms VerifiableInference.Desc.First.MergeLaw.sent_in_group
#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeat_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeat_reached
#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeat_of_maskAt
#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeat_of_front
#print axioms VerifiableInference.Desc.First.MergeLaw.nMsg_le_ns
#print axioms VerifiableInference.Desc.First.MergeLaw.JoinsToy.seat_found
#print axioms VerifiableInference.Desc.First.MergeLaw.JoinsToy.seat_found_wider
#print axioms VerifiableInference.Desc.First.MergeLaw.JoinsToy.seat_lost
#print axioms VerifiableInference.Desc.First.MergeLaw.JoinsToy.blank_rejected
