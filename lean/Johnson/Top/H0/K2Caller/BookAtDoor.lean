-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/BookAtDoor.lean: THE PREMISE hBook OF THE CODE SWITCH's FIRST TIE
(K2Caller/TieOneR.lean) FROM THREE FACTS ALONG THE FOLD: at what the way in lets in of a reached
state under the table of joints' promise: the book is in order, the seats are the listed ones, the
book fits; and every kept old message has a place in the book.

Why it is light. The three tests (Johnson/Desc/K12/Door/DoorBools.lean) read of a state its book and
its count of roots alone. So they pass a way in that leaves these two.

  DoorKeepsBook enter   the way in leaves the book and the count of roots
  doorKeeps_id          so does the way in that lets every state in as it is
  doorKeeps_finish      so does "F.0.front" (`K2.finishFrontQ`): by
                        `finishFrontQ_rest`
  not_doorKeeps         IT CAN FAIL: at a way in that counts one root more
  tests_same            the three tests give one answer at two states with one book and one count
  hBook_of_fold         **hBook's body**, general in the index type of the kept old messages and in
                        "reached": from the three facts at border k (the letters of the fields
                        bookInOrder, seatsCarried, bookFits of Johnson/Desc/First/FoldFacts.lean at
                        at_ := fun a => (z, a.1)), `DoorKeepsBook`, and hOld: "every kept old
                        message's number is below the statement's count in front"
  old_of_msg            hOld's clause at one state from "the statement in front has that message"
  old_of_front          THE FOURTH CONJUNCT WITH A FRONT IN HAND: from "the state's oracle messages
                        are the front's" and "the front's statement has that message"

Limits. The three facts, hOld and the promise are premises. FoldFacts.lean is not imported: the
three premises are held against its fields by reading. Shown at no real state. No soundness
statement.

-/
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Top.H0.K2Caller.PlacesOf
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)
open VerifiableInference.Desc.K12.Door (Laid atFirstBook atFirstSeats atFirstFits)

/-- **The way in leaves the book and the count of roots.** -/
def DoorKeepsBook (enter : First.S → Except String First.S) : Prop :=
  ∀ s t, enter s = .ok t → t.book = s.book ∧ t.roots = s.roots

theorem doorKeeps_id : DoorKeepsBook fun s => .ok s := fun _ _ h => by
  cases h
  exact ⟨rfl, rfl⟩

theorem doorKeeps_finish : DoorKeepsBook K2.finishFrontQ := fun _ _ h =>
  ⟨(K2.finishFrontQ_rest h).1, (K2.finishFrontQ_rest h).2.1⟩

/-- **It can fail**: at a way in that counts one root more. -/
theorem not_doorKeeps (s : First.S) :
    ¬ DoorKeepsBook fun s => .ok { s with roots := s.roots + 1 } := fun H => by
  have h := (H s _ rfl).2
  simp at h

/-- The three tests pass a step that leaves the book and the count of roots. -/
theorem tests_same (ft : ℕ) (L : Laid) {s t : First.S} (hb : t.book = s.book)
    (hr : t.roots = s.roots) :
    atFirstBook ft t = atFirstBook ft s ∧ atFirstSeats L t = atFirstSeats L s ∧
      atFirstFits t = atFirstFits s := by
  unfold atFirstBook atFirstSeats atFirstFits
  rw [hb, hr]
  exact ⟨rfl, rfl, rfl⟩

variable {P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (k : ℕ) (z : P)

/-- hOld's clause at one state, from "the statement in front has that message". -/
theorem old_of_msg {s : First.S} {old : ℕ} {xo : OnBytes.Oracle}
    (h : s.st.oracles[old]? = some xo) : old < s.st.oracles.size :=
  (Array.getElem?_eq_some_iff.1 h).1

/-- **hBook's body.** -/
theorem hBook_of_fold {K : Type} (old : K → ℕ) (Rch : ℕ → First.S × F.E.Str → Prop) (ft : ℕ)
    (L : Laid) (enter : First.S → Except String First.S)
    (hb : ∀ a, Rch k a → a.1.failed = none → atFirstBook ft a.1 = true)
    (hs : ∀ a, Rch k a → a.1.failed = none → atFirstSeats L a.1 = true)
    (hf : ∀ a, Rch k a → a.1.failed = none → atFirstFits a.1 = true)
    (hE : DoorKeepsBook enter)
    (hOld : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ κ, old κ < a.1.st.oracles.size) :
    ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t →
        atFirstBook ft t = true ∧ atFirstSeats L t = true ∧ atFirstFits t = true ∧
        ∀ κ, old κ < t.book.place.size := by
  intro a ha hr hm t ht
  obtain ⟨eb, er⟩ := hE _ _ ht
  obtain ⟨e1, e2, e3⟩ := tests_same ft L eb er
  have h0 : a.1.failed = none := not_not.1 hm
  refine ⟨e1.trans (hb a hr h0), e2.trans (hs a hr h0), e3.trans (hf a hr h0), fun κ => ?_⟩
  rw [eb, places_of_promise N Mg links ps (fun s => (z, s)) k a ha hm]
  exact hOld a ha hr hm κ

/-- **The fourth conjunct with a front in hand**: os: the front's statement's oracle messages. -/
theorem old_of_front (enter : First.S → Except String First.S) (hE : DoorKeepsBook enter)
    (a : First.S × F.E.Str) (ha : onQ N Mg links ps (fun s => (z, s)) k a)
    (hm : ¬ a.1.failed ≠ none) {t : First.S} (ht : enter a.1 = .ok t)
    {os : Array OnBytes.Oracle} (hor : a.1.st.oracles = os) {old : ℕ} {xo : OnBytes.Oracle}
    (hx : os[old]? = some xo) : old < t.book.place.size := by
  rw [(hE _ _ ht).1, places_of_promise N Mg links ps (fun s => (z, s)) k a ha hm, hor]
  exact (Array.getElem?_eq_some_iff.1 hx).1

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.doorKeeps_id
#print axioms VerifiableInference.Desc.First.K2Caller.doorKeeps_finish
#print axioms VerifiableInference.Desc.First.K2Caller.not_doorKeeps
#print axioms VerifiableInference.Desc.First.K2Caller.tests_same
#print axioms VerifiableInference.Desc.First.K2Caller.old_of_msg
#print axioms VerifiableInference.Desc.First.K2Caller.hBook_of_fold
#print axioms VerifiableInference.Desc.First.K2Caller.old_of_front
