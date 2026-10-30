-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11Members.lean: THE TWO MEMBERS THAT `mergeFill_at`
(Johnson/Desc/Sound/MgAt/K11.lean) TAKES, AS TERMS OFF THE LIST OF MEMBERS AND THE TABLE's NUMBERS,
AND ITS FIVE PREMISES ON THEM (hxM, hsM, hfM, hxI, hsI) FROM ONE TEST WITH CODE. General in the list
ms, the numbers N and the segment m. Definitions with code; theorems with their proofs.

  `xM? ms N m`: the first member that sits at a place of segment m's first sending and has mask
    rows. `xI? ms N`: the first member that sits at the index masks' place (`N.index`).
  `firstB ms p s`: no member in front of the first one that meets p sits at the place s.
  **`k11MembersB ms N m`**: THE TEST: both are there, and no member in front of xM sits at xM's
    place. IT CAN FAIL.
  `find_of_first`: where x is the first that meets p, x meets q, and none in front of it meets q: x
    is the first that meets q.
  **`k11_members`**: a yes of the test gives xM and xI with the five premises, in
    `mergeFill_at`'s own letters.
  `xAt ms p`, `membersAtB ms N m pM`, **`members_at`**: THE SAME BY THE PLACE (the pick of the
    kind's own files): the first member at a given place pM, and at `N.index`: then three of the
    five hold by the make, and the test asks: both are there, and pM is a place of the first
    sending.
  `sent_withTold`, `index_withTold`: the numbers' fields sent and index are those of the numbers off
    the planner's seats, whatever rows and told lists are laid on (`withRows`, `withTold`): rfl.
Limits. That the test says yes is shown nowhere here: a sheet's matter. That «the first member with
mask rows at the head's first sending» is the message that the merge reads is not shown here. No
soundness is claimed.

-/
import Johnson.Desc.Sound.World
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.First.RowsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers)

/-- Does the member sit at a place of segment m's first sending, with mask rows? -/
def isM (N : Numbers) (m : ℕ) (y : Mem) : Bool :=
  decide (seatOf y ∈ N.sent m 0) && (y.1.l.get y.2).1.maskRows != 0

/-- The first such member. -/
def xM? (ms : List Mem) (N : Numbers) (m : ℕ) : Option Mem := ms.find? (isM N m)

/-- The first member at the index masks' place. -/
def xI? (ms : List Mem) (N : Numbers) : Option Mem :=
  ms.find? fun y => decide (seatOf y = N.index)

/-- No member in front of the first one that meets p sits at the place s. -/
def firstB (ms : List Mem) (p : Mem → Bool) (s : ℕ × ℕ) : Bool :=
  (ms.takeWhile fun y => !p y).all fun y => !decide (seatOf y = s)

/-- **The test.** -/
def k11MembersB (ms : List Mem) (N : Numbers) (m : ℕ) : Bool :=
  (match xM? ms N m with
    | some x => firstB ms (isM N m) (seatOf x)
    | none => false) && (xI? ms N).isSome

/-- Where x is the first that meets p, meets q, and none in front of it meets q. -/
theorem find_of_first {α : Type} (p q : α → Bool) : ∀ (l : List α) (x : α),
    l.find? p = some x → q x = true → ((l.takeWhile fun y => !p y).all fun y => !q y) = true →
    l.find? q = some x
  | [], _, h, _, _ => by cases h
  | a :: l, x, h, hq, hn => by
    by_cases hp : p a = true
    · have e : a = x := by
        rw [List.find?_cons_of_pos hp] at h
        exact Option.some.inj h
      subst e
      exact List.find?_cons_of_pos hq
    · have hp' : p a = false := by simpa using hp
      rw [List.find?_cons_of_neg hp] at h
      have ht : ((a :: l).takeWhile fun y => !p y) = a :: l.takeWhile fun y => !p y := by
        rw [List.takeWhile_cons_of_pos (by simp [hp'])]
      rw [ht, List.all_cons, Bool.and_eq_true] at hn
      have hqa : ¬ q a = true := by simpa using hn.1
      rw [List.find?_cons_of_neg hqa]
      exact find_of_first p q l x h hq hn.2

/-- **A yes of the test gives the two members with the five premises.** -/
theorem k11_members (ms : List Mem) (N : Numbers) (m : ℕ) (h : k11MembersB ms N m = true) :
    ∃ xM xI, xM? ms N m = some xM ∧ xI? ms N = some xI ∧ xM ∈ ms ∧ seatOf xM ∈ N.sent m 0 ∧
      (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM ∧ xI ∈ ms ∧
      seatOf xI = N.index := by
  unfold k11MembersB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases hM : xM? ms N m with
  | none => rw [hM] at h1; cases h1
  | some xM =>
    rw [hM] at h1
    obtain ⟨xI, hI⟩ := Option.isSome_iff_exists.1 h2
    have pM : isM N m xM = true := List.find?_some hM
    have pI : decide (seatOf xI = N.index) = true :=
      List.find?_some (p := fun y => decide (seatOf y = N.index)) hI
    unfold isM at pM
    rw [Bool.and_eq_true] at pM
    exact ⟨xM, xI, rfl, hI, List.mem_of_find?_eq_some hM, of_decide_eq_true pM.1,
      find_of_first (isM N m) (fun y => decide (seatOf y = seatOf xM)) ms xM hM
        (decide_eq_true rfl) h1,
      List.mem_of_find?_eq_some hI, of_decide_eq_true pI⟩

/-! ### The same by the place (the kind's own files' pick) -/

/-- The first member at the place p. -/
def xAt (ms : List Mem) (p : ℕ × ℕ) : Option Mem := ms.find? fun y => decide (seatOf y = p)

/-- **The test, at a given place pM of the segment's message with mask rows.** -/
def membersAtB (ms : List Mem) (N : Numbers) (m : ℕ) (pM : ℕ × ℕ) : Bool :=
  (xAt ms pM).isSome && decide (pM ∈ N.sent m 0) && (xAt ms N.index).isSome

/-- **A yes gives the two members with the five premises**: three of the five by the make. -/
theorem members_at (ms : List Mem) (N : Numbers) (m : ℕ) (pM : ℕ × ℕ)
    (h : membersAtB ms N m pM = true) :
    ∃ xM xI, xAt ms pM = some xM ∧ xAt ms N.index = some xI ∧ seatOf xM = pM ∧ xM ∈ ms ∧
      seatOf xM ∈ N.sent m 0 ∧ (ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM ∧
      xI ∈ ms ∧ seatOf xI = N.index := by
  unfold membersAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨xM, hM⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨xI, hI⟩ := Option.isSome_iff_exists.1 h3
  have eM : seatOf xM = pM :=
    of_decide_eq_true (List.find?_some (p := fun y => decide (seatOf y = pM)) hM)
  have eI : seatOf xI = N.index :=
    of_decide_eq_true (List.find?_some (p := fun y => decide (seatOf y = N.index)) hI)
  refine ⟨xM, xI, hM, hI, eM, List.mem_of_find?_eq_some hM, eM ▸ h2, ?_,
    List.mem_of_find?_eq_some hI, eI⟩
  rw [eM]
  exact hM

/-- The fields sent and index are untouched by the rows and the told lists that are laid on. -/
theorem sent_withTold (N : Numbers) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ)
    (ps : List Place) (told : List (List Oracle)) :
    ((N.withRows s t n).withTold ps told).sent = N.sent := rfl

theorem index_withTold (N : Numbers) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ)
    (ps : List Place) (told : List (List Oracle)) :
    ((N.withRows s t n).withTold ps told).index = N.index := rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.find_of_first
#print axioms VerifiableInference.Desc.Sound.k11_members
#print axioms VerifiableInference.Desc.Sound.members_at
#print axioms VerifiableInference.Desc.Sound.sent_withTold
#print axioms VerifiableInference.Desc.Sound.index_withTold
