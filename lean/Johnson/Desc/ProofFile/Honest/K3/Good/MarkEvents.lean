-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarkEvents.lean: the kind "lookup" (K3): where the test on the
lookup's own samples (`goodK3`, Honest/K3/GoodDraws.lean) rejects, one of a written list of events
holds: "one named sampled element is 0", or "is 1". The list is as long as that file counts.
Definitions with code; theorems.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: f is the lookup's face and ds the list of its own
samples.

What is shown.
  `Event`, `eventsAtSpot`, `eventsOf`, `runEvents`: the events: spot by spot; all; one run's.
  `Event.test`, `Event.round`, `Event.shows`, `Event.holds`: an event as a test on an element; the
    number of its round among the lookup's own; the event as a test on what that round samples; as a
    test on all the lookup's samples.
  `eventsOf_length`, `runEvents_length`: the lists' lengths are `events` and `eventsRun`
    (GoodDraws.lean).
  `ok_value`: samples that the rounds can sample have words below the prime at every spot.
  `event_of_bad`, `event_of_badRun`: where the samples are such and the test rejects, an event of
    the list holds.
  `holds_at`: an event reads its own round's sample alone.
Helpers: `length_atSpot`, `length_flat`, `ok_getD`, `event_of_notFine`, `notFine_of_all`,
`runEvents_sub`.

Hypotheses that remain.
  `hc`: the samples are such as the rounds can sample (`canDraw`, Honest/K3/GoodDrawsLaw.lean).
  `h`: the test rejects them (in `event_of_bad`, `event_of_badRun`); in `holds_at`, R is the sample
    of the event's round; in the helpers `event_of_notFine`, `notFine_of_all`, `runEvents_sub`: the
    test on the spot, or on some spot of the list, rejects; the event is one of the run's.
  `hok`, `hl`: (in `event_of_notFine`, `ok_getD`) the element's words, or all the list's, are below
    the prime.
  `h`: (in `ok_value`) `canDraw f ds = true`: what stands elsewhere under the name `hc`.

Users. `markK3_le` and `markRun_le` (Honest/K3/Good/MarkShare.lean) call `event_of_bad` and
`event_of_badRun`.

Limits. One direction alone: that the test rejects wherever an event holds is not stated here; it is
tried event by event in Honest/K3/GoodDrawsGuards.lean [not in this library].
No measure stands in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Gives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE okE isZeroE)

/-- **An event**: the element at a spot is 0, or it is 1. -/
structure Event where
  spot : Spot
  /-- false: the element is 0. true: it is 1 -/
  atOne : Bool
  deriving DecidableEq, Repr

/-- The events at a spot: one, or two where 1 is forbidden too. -/
def eventsAtSpot (p : Spot) : List Event := ⟨p, false⟩ :: (if p.one then [⟨p, true⟩] else [])

/-- **All events of a lookup.** -/
def eventsOf (f : LFace) : List Event := (spots f).flatMap eventsAtSpot

/-- The events at which a slot of one run's window may be named with the coefficient 0 alone. -/
def runEvents (f : LFace) (r : Run) : List Event :=
  ((spots f).filter fun p => p.run f == r).flatMap eventsAtSpot

/-- The event as a test on an element. -/
def Event.test (e : Event) (x : E) : Bool := if e.atOne then x == oneE else isZeroE x

/-- The number of the event's round among the lookup's own rounds. -/
def Event.round (f : LFace) (e : Event) : Nat := firstRound f e.spot.stage + e.spot.round

/-- The event as a test on what its round samples. -/
def Event.shows (e : Event) (R : Fmt.Drawn) : Bool :=
  e.test ((R.elems.map E.ofTriple).getD e.spot.draw zeroE)

/-- The event as a test on the lookup's own samples. -/
def Event.holds (f : LFace) (ds : List Fmt.Drawn) (e : Event) : Bool := e.test (e.spot.value f ds)

/-! ## The count -/

theorem length_atSpot (p : Spot) : (eventsAtSpot p).length = if p.one then 2 else 1 := by
  unfold eventsAtSpot
  cases p.one <;> rfl

theorem length_flat (l : List Spot) :
    (l.flatMap eventsAtSpot).length = (l.map fun p => if p.one then 2 else 1).sum := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.map_cons, List.sum_cons, length_atSpot]

/-- The list is as long as Honest/K3/GoodDraws.lean counts. -/
theorem eventsOf_length (f : LFace) : (eventsOf f).length = events f := length_flat _

theorem runEvents_length (f : LFace) (r : Run) : (runEvents f r).length = eventsRun f r :=
  length_flat _

/-! ## Words below the prime -/

theorem ok_getD (l : List E) (hl : ∀ x ∈ l, okE x = true) (k : Nat) :
    okE (l.getD k zeroE) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => rfl
  | some x => exact hl x (List.mem_of_getElem? hk)

/-- Samples that the rounds can sample have words below the prime at every spot. -/
theorem ok_value (f : LFace) (ds : List Fmt.Drawn) (h : canDraw f ds = true) (p : Spot) :
    okE (p.value f ds) = true := by
  unfold Spot.value elemsAt
  refine ok_getD _ ?_ _
  intro x hx
  cases hd : ds[firstRound f p.stage + p.round]? with
  | none =>
    rw [hd] at hx
    cases hx
  | some R =>
    rw [hd] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ok_of_fit _ _ h R (List.mem_of_getElem? hd) y hy

/-! ## From a rejection to an event -/

theorem event_of_notFine {f : LFace} {ds : List Fmt.Drawn} {p : Spot}
    (hok : okE (p.value f ds) = true) (h : p.fine f ds = false) :
    ∃ e ∈ eventsAtSpot p, e.holds f ds = true := by
  unfold Spot.fine at h
  rw [hok] at h
  cases hz : isZeroE (p.value f ds) with
  | true =>
    refine ⟨⟨p, false⟩, List.mem_cons_self, ?_⟩
    unfold Event.holds Event.test
    exact hz
  | false =>
    rw [hz] at h
    cases ho : p.one with
    | false =>
      rw [ho] at h
      simp at h
    | true =>
      rw [ho] at h
      have hv : p.value f ds = oneE := by simpa using h
      refine ⟨⟨p, true⟩, ?_, ?_⟩
      · unfold eventsAtSpot
        rw [ho]
        simp
      · unfold Event.holds Event.test
        simp [hv]

theorem notFine_of_all {f : LFace} {ds : List Fmt.Drawn} {l : List Spot}
    (h : l.all (Spot.fine f ds) = false) : ∃ p ∈ l, p.fine f ds = false := by
  by_contra hn
  have hall : l.all (Spot.fine f ds) = true := by
    rw [List.all_eq_true]
    intro p hp
    cases hq : p.fine f ds with
    | true => rfl
    | false => exact absurd ⟨p, hp, hq⟩ hn
  rw [hall] at h
  cases h

/-- **One run's test.** -/
theorem event_of_badRun (f : LFace) (r : Run) (ds : List Fmt.Drawn) (hc : canDraw f ds = true)
    (h : goodRun f r ds = false) : ∃ e ∈ runEvents f r, e.holds f ds = true := by
  obtain ⟨p, hp, hf⟩ := notFine_of_all h
  obtain ⟨e, he, hh⟩ := event_of_notFine (ok_value f ds hc p) hf
  exact ⟨e, List.mem_flatMap.2 ⟨p, hp, he⟩, hh⟩

theorem runEvents_sub (f : LFace) (r : Run) {e : Event} (h : e ∈ runEvents f r) :
    e ∈ eventsOf f := by
  obtain ⟨p, hp, he⟩ := List.mem_flatMap.1 h
  exact List.mem_flatMap.2 ⟨p, (List.mem_filter.1 hp).1, he⟩

/-- **Where the samples are such as the rounds can sample and the test rejects, an event of the list
holds.** -/
theorem event_of_bad (f : LFace) (ds : List Fmt.Drawn) (hc : canDraw f ds = true)
    (h : goodK3 f ds = false) : ∃ e ∈ eventsOf f, e.holds f ds = true := by
  have key : ∃ r, goodRun f r ds = false := by
    by_contra hn
    have hr : ∀ r, goodRun f r ds = true := fun r => by
      cases hq : goodRun f r ds with
      | true => rfl
      | false => exact absurd ⟨r, hq⟩ hn
    unfold goodK3 at h
    rw [hr, hr, hr] at h
    cases h
  obtain ⟨r, hr⟩ := key
  obtain ⟨e, he, hh⟩ := event_of_badRun f r ds hc hr
  exact ⟨e, runEvents_sub f r he, hh⟩

/-- **An event reads its own round's sample alone.** -/
theorem holds_at (f : LFace) (ds : List Fmt.Drawn) (e : Event) {R : Fmt.Drawn}
    (h : ds[e.round f]? = some R) : e.holds f ds = e.shows R := by
  unfold Event.holds Event.shows Spot.value elemsAt
  unfold Event.round at h
  rw [h]
  rfl

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.length_atSpot
#print axioms ProofFile.Honest.K3.Good.length_flat
#print axioms ProofFile.Honest.K3.Good.eventsOf_length
#print axioms ProofFile.Honest.K3.Good.runEvents_length
#print axioms ProofFile.Honest.K3.Good.ok_getD
#print axioms ProofFile.Honest.K3.Good.ok_value
#print axioms ProofFile.Honest.K3.Good.event_of_notFine
#print axioms ProofFile.Honest.K3.Good.notFine_of_all
#print axioms ProofFile.Honest.K3.Good.event_of_badRun
#print axioms ProofFile.Honest.K3.Good.runEvents_sub
#print axioms ProofFile.Honest.K3.Good.event_of_bad
#print axioms ProofFile.Honest.K3.Good.holds_at
