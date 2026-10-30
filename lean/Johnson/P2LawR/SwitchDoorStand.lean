-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SwitchDoorStand.lean: THE PREMISE hH ("if the switch m stands at the head: the state
  at the border does not stand at the head's link already") THAT FIVE THEOREMS ON THE CODE SWITCH's
  FRONT SHARE (skel_old_door, doorReads_door, front_shapes_door, keptCount_door:
  Johnson/Desc/First/Link/Law/FrontStEnds.lean; book_at_door: Johnson/P2LawR/SwitchNotices.lean),
  BEHIND K10's PLACE OF EVERY LINK l < 25.


WHAT IS FOUND.
hH IS AN IMPLICATION. ITS END ("the state does not stand at the head") CANNOT BE HAD AT EVERY ONE OF
  THESE BORDERS: behind K10's place of link 24, under the table's promise in front, the state DOES
  stand at the head (at_head_behind_24). So there hH holds only if the switch that spends that
  link's rows does not stand at the head. ANOTHER ROAD TO THAT: stands24, under the
  named test spotsFitB and "25 links"; for spotsFitB there is a theorem from the head and
  the cut (spots_atAll, Johnson/Loose/H2K12/SpotsAtAll.lean). This file does not go that way and
  needs none of it.
THE WAY ROUND: each of the five has, beside hH, the premise that THE WAY IN ANSWERS (doorZ Z m s' =
  some t); and at a state that stands inside an open link the way in of a switch at the head answers
  only if the state is not at the head: at the head's link, once opened, doorZ's own text says none.
SO hH FOLLOWS FROM "THE WAY IN ANSWERS" AND "THE STATE STANDS INSIDE AN OPEN LINK", WHICHEVER m:
  which switch stands at the head need not be known.
WHAT THE WAY ROUND COSTS: IT MAKES hH FREE BY MAKING THE BAD CASE EMPTY. Where hH's end fails (a
  switch at the head; the state in the head's opened link) the way in does not answer either: there
  the five theorems say NOTHING. So hH_behind_K10 does NOT say that a front is there at all 25
  links.

THE NAMES.
opened_of_stand: a state that stands inside an open link and whose part "here" is the head's: the
  head's link is opened.
hH_of_stand: **standOf s' = .link sub · doorZ Z m s' = some t ⊢ hH**, at every Z and m.
standK10B, stand_k10_all, stand_k10: a closed fact on the written list of places, by Lean's kernel:
  at each of the 25 numbers ixK10 l the table says "inside an open link".
stand_in_front: so under the table's promise in front of K10's place, at a state without a mark
  (stand_of_promise, Johnson/Top/H0/K2Caller/DoorOfPromise.lean).
stand_behind: and behind K10's own writing (putRec_standOf, Close/Law/ShapeBehind.lean).
hH_behind_K10: **the promise at ixK10 l · no mark · l < 25 · the way in answers at wrK s f S' ⊢ hH
  at wrK s f S'.**
head_of_stand, stand_k10_24, at_head_behind_24: why hH's end cannot be had at all 25 borders: at
  link 24 the table says "inside the head's open link" (by the kernel), and such a state's part
  "here" is the head's.
book_at_door_stand: book_at_door with "stands inside an open link" in hH's place.

Limits. The promise in front is a premise. THAT standK10B CAN SAY FALSE IS SHOWN BY NO LINE HERE:
  negative lines are left to other files. The full size's list of places alone. Nothing on
  soundness.
-/
import Johnson.P2LawR.SwitchNotices
import Johnson.Top.H0.K2Caller.DoorOfPromise
import Johnson.Desc.First.Close.Law.ShapeBehind
import Johnson.LPFK10R.SitsAll
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.P2Notices
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open Meaning.K2 (RecAll)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning Numbers standOf standAt)
open VerifiableInference.Desc.First.K2Caller (doorZ stand_of_promise)
open VerifiableInference.Desc.First.Close (wrK)
open _root_.Tw.K2 (switchNotices)
open LPFK10 (ixK10)

/-- Inside an open link, at the head: the head's link is opened. -/
theorem opened_of_stand {s : First.S} {sub : ModelPart} (h : standOf s = .link sub) {b : First.HeadOwn}
    (hb : s.here = .head b) : b.opened = true := by
  unfold standOf at h
  rw [hb] at h
  cases hi : s.inLink with
  | false =>
    rw [hi] at h
    cases h
  | true =>
    by_contra ho
    simp [First.S.inLink, First.S.fork?, hb, ho] at hi

/-- **hH, FROM "THE WAY IN ANSWERS" AND "THE STATE STANDS INSIDE AN OPEN LINK".** -/
theorem hH_of_stand {Z : ProofFile.Pub} {m : ℕ} {s' t : First.S} {sub : ModelPart}
    (hst : standOf s' = .link sub) (hd : doorZ Z m s' = some t) :
    (ProofFile.pAtK2 Z m).stands = .head → ∀ b, s'.here ≠ .head b := by
  intro hp b hb
  have ho := opened_of_stand hst hb
  simp [doorZ, hp, hb, ho] at hd

/-- The test on the written list of places: at each number ixK10 l the table says "inside an open
link". -/
def standK10B : Bool :=
  (List.range 25).all fun l =>
    match P5J.At.ps[ixK10 l]? with
    | some p =>
      match standAt P5J.fullLinks p with
      | .link _ => true
      | _ => false
    | none => false

/-- **It accepts**: by Lean's kernel. -/
theorem stand_k10_all : standK10B = true := by decide +kernel

theorem stand_k10 {l : ℕ} (hl : l < 25) :
    ∃ p sub, P5J.At.ps[ixK10 l]? = some p ∧ standAt P5J.fullLinks p = .link sub := by
  have k := List.all_eq_true.1 stand_k10_all l (List.mem_range.2 hl)
  cases hp : P5J.At.ps[ixK10 l]? with
  | none =>
    rw [hp] at k
    cases k
  | some p =>
    rw [hp] at k
    have k' : (match standAt P5J.fullLinks p with
      | .link _ => true
      | _ => false) = true := k
    cases hs : standAt P5J.fullLinks p with
    | link sub => exact ⟨p, sub, rfl, hs⟩
    | between => rw [hs] at k'; cases k'
    | headFront => rw [hs] at k'; cases k'
    | fin => rw [hs] at k'; cases k'
    | mem => rw [hs] at k'; cases k'

variable {A P W : Type} {F : Frame} (N : Numbers) (Mg : Meaning P W) (get : A → P × First.S)

/-- Under the table's promise in front of K10's place, at a state without a mark. -/
theorem stand_in_front {l : ℕ} (hl : l < 25) (a : A × F.E.Str)
    (ha : onQ N Mg P5J.fullLinks P5J.At.ps get (ixK10 l) a)
    (hm : ¬ (get a.1).2.failed ≠ none) : ∃ sub, standOf (get a.1).2 = .link sub := by
  obtain ⟨p, sub, hp, hs⟩ := stand_k10 hl
  exact ⟨sub, (stand_of_promise N Mg P5J.fullLinks P5J.At.ps get (ixK10 l) a ha hm p hp).trans hs⟩

/-- Behind K10's own writing. -/
theorem stand_behind {l : ℕ} (hl : l < 25) (a : A × F.E.Str)
    (ha : onQ N Mg P5J.fullLinks P5J.At.ps get (ixK10 l) a)
    (hm : ¬ (get a.1).2.failed ≠ none) (f : ReqFrame) (S' : Statement) :
    ∃ sub, standOf (wrK (get a.1).2 f S') = .link sub := by
  obtain ⟨sub, hs⟩ := stand_in_front N Mg get hl a ha hm
  exact ⟨sub, (First.putRec_standOf _ _).trans hs⟩

/-- **hH BEHIND K10's PLACE OF EVERY LINK, WHERE THE WAY IN ANSWERS.** -/
theorem hH_behind_K10 {l : ℕ} (hl : l < 25) (a : A × F.E.Str)
    (ha : onQ N Mg P5J.fullLinks P5J.At.ps get (ixK10 l) a)
    (hm : ¬ (get a.1).2.failed ≠ none) (f : ReqFrame) (S' : Statement) {Z : ProofFile.Pub} {m : ℕ}
    {t : First.S} (hd : doorZ Z m (wrK (get a.1).2 f S') = some t) :
    (ProofFile.pAtK2 Z m).stands = .head → ∀ b, (wrK (get a.1).2 f S').here ≠ .head b := by
  obtain ⟨sub, hs⟩ := stand_behind N Mg get hl a ha hm f S'
  exact hH_of_stand hs hd

/-- A state that stands inside the head's open link: its part "here" is the head's. -/
theorem head_of_stand {s : First.S} (h : standOf s = .link .head) : ∃ b, s.here = .head b := by
  unfold standOf at h
  cases hq : s.here with
  | head b => exact ⟨b, rfl⟩
  | between => rw [hq] at h; cases h
  | lay a => rw [hq] at h; cases h
  | att a => rw [hq] at h; cases h
  | fin a => rw [hq] at h; cases h
  | mem a => rw [hq] at h; cases h

/-- At K10's place of link 24 the table says "inside the head's open link": by Lean's kernel. -/
theorem stand_k10_24 :
    (P5J.At.ps[ixK10 24]?).map (standAt P5J.fullLinks) = some (.link .head) := by decide +kernel

/-- **WHY hH's END CANNOT BE HAD AT ALL 25 BORDERS**: behind K10's place of link 24, under the
promise in front, the state DOES stand at the head. -/
theorem at_head_behind_24 (a : A × F.E.Str)
    (ha : onQ N Mg P5J.fullLinks P5J.At.ps get (ixK10 24) a)
    (hm : ¬ (get a.1).2.failed ≠ none) (f : ReqFrame) (S' : Statement) :
    ∃ b, (wrK (get a.1).2 f S').here = .head b := by
  have k := stand_k10_24
  cases hp : P5J.At.ps[ixK10 24]? with
  | none =>
    rw [hp] at k
    cases k
  | some p =>
    rw [hp] at k
    have hs : standAt P5J.fullLinks p = .link .head := Option.some.inj k
    exact head_of_stand ((First.putRec_standOf _ _).trans
      ((stand_of_promise N Mg P5J.fullLinks P5J.At.ps get (ixK10 24) a ha hm p hp).trans hs))

/-- **THE BOOK BEHIND THE SWITCH's SENDING IS THERE**, at a state that stands inside an open link.
-/
theorem book_at_door_stand {cs : Codes} {sh : ReqShape} {Z : ProofFile.Pub} {m : ℕ} {s' : First.S}
    {sub : ModelPart} (R : RecAll cs sh s') (hs : s'.st.oracles.size = s'.book.place.size)
    (K : noticesOkB cs sh = true) (hst : standOf s' = .link sub) :
    ∀ t fx, doorZ Z m s' = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx →
      ∃ B, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx.st t.book t.roots
        (switchNotices fx.T fx.others) = some B :=
  fun t fx hd hf => book_at_door R hs K (hH_of_stand hst hd) t fx hd hf

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.opened_of_stand
#print axioms VerifiableInference.Desc.P2Notices.hH_of_stand
#print axioms VerifiableInference.Desc.P2Notices.stand_k10_all
#print axioms VerifiableInference.Desc.P2Notices.stand_k10
#print axioms VerifiableInference.Desc.P2Notices.stand_in_front
#print axioms VerifiableInference.Desc.P2Notices.stand_behind
#print axioms VerifiableInference.Desc.P2Notices.hH_behind_K10
#print axioms VerifiableInference.Desc.P2Notices.head_of_stand
#print axioms VerifiableInference.Desc.P2Notices.stand_k10_24
#print axioms VerifiableInference.Desc.P2Notices.at_head_behind_24
#print axioms VerifiableInference.Desc.P2Notices.book_at_door_stand
