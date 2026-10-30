-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SeatIff.lean: A SUB-PROTOCOL AS THE PROOF FILE's DESCRIPTION SEATS IT
IN THE FIRST CHAIN, AND THE LOT's OWN SUB-PROTOCOL WITHIN: THE SEATED ONE's DECISION, BOTH WAYS: it
says yes just where the lot's own says yes and the way out returns. General in the lot's
sub-protocol; no state of the walk, no plan. THE LIBRARY HAS THE WAY DOWN (from the seated yes); THE
WAY UP IS WHAT IS NEW HERE. Statements with their proofs: unfolding and the library's own two-way
laws on the guards.

  `noMark_iff`, `seatSame_iff`, `guards_iff` the seat's guards as functions
                    (Johnson/P1K2R/SitsStep.lean, Johnson/Desc/SeatGuard.lean) return just where
                    their tests hold, and hand the state on
  `leaveOpened_iff` the way out at a link's first place: `leaveOpened f s m` returns t just where m
                    bears no mark, the row's `opened` returns t at m, t bears no mark, and the reply
                    is as it was at m and at s
  `with_iff` `seatedWith same b' q name a`, at an address that is not K7's: b' at the front of the
                    rounds and groups, no mark, q at the rest, `same` twice
  `joined_iff` THE FIRST TOP: the form of `IM.Joined`, at as many rounds and groups as b' has:
                    b.decide s rs gs = ok t ↔ ∃ m, b'.decide s rs gs = ok m ∧ leaveOpened f s m = ok
                    t
  `alone_iff` THE SECOND: laid alone: … ↔ ∃ m, b'.decide s rs gs = ok m ∧ guards s m = ok t

By, all the library's: `seatedWith`, `marked`, `LaidAlone`, `guardMark_yes`, `yes_alone`
(Johnson/IMR/SeatForm.lean) · `openedOf` (Johnson/IMR/FrameSeat.lean) · `guarded_yes`
(Johnson/Desc/Sound/SeatGuardLaws.lean) · `noMark`, `guards`, `leaveOpened`
(Johnson/P1K2R/SitsStep.lean) · `Except.bind_eq_ok` (Johnson/Top/H0/StepLaws/StepLaws.lean). NEAR
RELATIVES, ONE WAY, NOT CALLED: `yes_with` (Johnson/IMR/SeatForm.lean), `Joined.yes`, `Joined.step`
(Johnson/IMR/FirstSeats.lean, whose head says that the way back is not claimed) · `sits_with`,
`sits_alone`, `leaveWith_opened` (Johnson/P1K2R/SitsStep.lean, whose Limits say: one direction). THE
WAY DOWN OF THE FOUR SMALL LAWS ON THE GUARDS STANDS IN THE LIBRARY SEVERAL TIMES, NOT CALLED:
`noMark_same`, `seatSame_same`, `guards_same`, `leaveOpened_is` (Johnson/P1K2R/SitsDoor.lean) ·
`noMark_none`, `guards_none`, `leaveOpened_none` (Johnson/P1K2R/SitsMark.lean) · `noMark_ok`,
`guards_unmarked`, `leaveOpened_unmarked` (Johnson/P1K2R/SitsNoMark.lean) · `seatSame_ok`
(Johnson/Desc/Sound/SeatGuardLaws.lean and other files), `seatSame_inv`
(Johnson/Desc/First/Link/Law/GuardTies.lean). BOTH WAYS, AT OTHER KINDS' SEATS, NOT CALLED:
`seated_step_iff` (Johnson/Desc/Kinds/Law/SeatedBack.lean) · `step_seated_iff`
(Johnson/Desc/First/K8/LawSeated.lean).

Limits. At the decision, not at the step. That a way out returns is shown nowhere here. Which
sub-protocol the lot lays at a place is not said here. Nothing on any property.




-/
import Johnson.P1K2R.SitsStep
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open VerifiableInference.Desc (Block Place KindName seatSame guarded_yes)
open VerifiableInference.Desc.First (S hearsReply)
open Johnson.Desc.First.Walk.Seat (LinkFrame)
open IM (seatedWith marked openedOf LaidAlone guardMark_yes yes_alone)
open P1K2 (noMark guards leaveOpened)
open ProofFile (Cl)

theorem noMark_iff (t u : S) : noMark t = .ok u ↔ u = t ∧ t.failed = none := by
  unfold noMark
  split
  · rename_i h
    exact ⟨fun e => ⟨(Except.ok.inj e).symm, h⟩, fun e => (by rw [e.1])⟩
  · rename_i m h
    exact ⟨fun e => (by cases e), fun e => (by rw [h] at e; cases e.2)⟩

theorem seatSame_iff (same : S → S → Bool) (t s u : S) :
    seatSame same t s = .ok u ↔ u = s ∧ same t s = true := by
  unfold seatSame
  split
  · rename_i h
    exact ⟨fun e => ⟨(Except.ok.inj e).symm, h⟩, fun e => (by rw [e.1])⟩
  · rename_i h
    exact ⟨fun e => (by cases e), fun e => absurd e.2 h⟩

theorem guards_iff (s t u : S) :
    guards s t = .ok u ↔ u = t ∧ t.failed = none ∧ ProofFile.sameReply s t = true := by
  unfold guards
  rw [VerifiableInference.Desc.Except.bind_eq_ok]
  constructor
  · rintro ⟨a, h1, h2⟩
    obtain ⟨rfl, hf⟩ := (noMark_iff _ _).1 h1
    obtain ⟨rfl, hs⟩ := (seatSame_iff _ _ _ _).1 h2
    exact ⟨rfl, hf, hs⟩
  · rintro ⟨rfl, hf, hs⟩
    exact ⟨u, (noMark_iff _ _).2 ⟨rfl, hf⟩, (seatSame_iff _ _ _ _).2 ⟨rfl, hs⟩⟩

/-- **The way out at a link's first place, both ways.** -/
theorem leaveOpened_iff (f : LinkFrame) (s m t : S) :
    leaveOpened f s m = .ok t ↔ m.failed = none ∧ f.opened m = .ok t ∧ t.failed = none ∧
      ProofFile.sameReply m t = true ∧ ProofFile.sameReply s t = true := by
  unfold leaveOpened
  simp only [VerifiableInference.Desc.Except.bind_eq_ok, noMark_iff, seatSame_iff]
  constructor
  · rintro ⟨_, ⟨rfl, f1⟩, u, h2, _, ⟨rfl, f2⟩, _, ⟨rfl, s1⟩, rfl, s2⟩
    exact ⟨f1, h2, f2, s1, s2⟩
  · rintro ⟨f1, h2, f2, s1, s2⟩
    exact ⟨m, ⟨rfl, f1⟩, t, h2, t, ⟨rfl, f2⟩, t, ⟨rfl, s1⟩, rfl, s2⟩

/-- **With a sub-protocol joined behind, both ways.** -/
theorem with_iff {same : S → S → Bool} {b' q : Block S Cl} {name : String} {a : Place}
    (hk : a.kind ≠ KindName.K7) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (seatedWith same b' q name a).decide s rs gs = .ok t ↔
      ∃ m, b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok m ∧
        m.failed = none ∧
        q.decide m (rs.drop b'.rounds.length) (gs.drop b'.openings) = .ok t ∧
        same m t = true ∧ same s t = true := by
  have hp : hearsReply ({ (marked b' name).andThen name (q.guarded same fun _ => false) with
      place := a } : Block S Cl).place = false := by
    show (a.kind == KindName.K7) = false
    simpa using hk
  unfold seatedWith
  rw [guarded_yes same hearsReply _ hp]
  show ((ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings)).bind
      (fun s' => (q.guarded same fun _ => false).decide s' (rs.drop b'.rounds.length)
        (gs.drop b'.openings)) = .ok t ∧ _ ↔ _
  rw [VerifiableInference.Desc.Except.bind_eq_ok]
  constructor
  · rintro ⟨⟨m, h1, h2⟩, h3⟩
    obtain ⟨d1, d2⟩ := (guardMark_yes b' s m _ _).1 h1
    obtain ⟨e1, e2⟩ := (guarded_yes same (fun _ => false) q rfl m _ _ t).1 h2
    exact ⟨m, d1, d2, e1, e2, h3⟩
  · rintro ⟨m, d1, d2, e1, e2, h3⟩
    exact ⟨⟨m, (guardMark_yes b' s m _ _).2 ⟨d1, d2⟩,
      (guarded_yes same (fun _ => false) q rfl m _ _ t).2 ⟨e1, e2⟩⟩, h3⟩

/-- **At a link's first place: the seated decision, both ways.** -/
theorem joined_iff {b b' : Block S Cl} {f : LinkFrame} {a : Place}
    (e : b = seatedWith ProofFile.sameReply b' (ProofFile.guardMark (openedOf f).retype) b.name a)
    (hk : a.kind ≠ KindName.K7) {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hr : rs.length = b'.rounds.length) (hg : gs.length = b'.openings) (s t : S) :
    b.decide s rs gs = .ok t ↔ ∃ m, b'.decide s rs gs = .ok m ∧ leaveOpened f s m = .ok t := by
  rw [e, with_iff hk, List.take_of_length_le (le_of_eq hr), List.take_of_length_le (le_of_eq hg)]
  constructor
  · rintro ⟨m, d1, d2, d3, d4, d5⟩
    obtain ⟨o1, o2⟩ := (guardMark_yes _ m t _ _).1 d3
    exact ⟨m, d1, (leaveOpened_iff f s m t).2 ⟨d2, o1, o2, d4, d5⟩⟩
  · rintro ⟨m, d1, h⟩
    obtain ⟨d2, o1, o2, d4, d5⟩ := (leaveOpened_iff f s m t).1 h
    exact ⟨m, d1, d2, (guardMark_yes _ m t _ _).2 ⟨o1, o2⟩, d4, d5⟩

/-- **Laid alone: the seated decision, both ways.** -/
theorem alone_iff {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok t ↔ ∃ m, b'.decide s rs gs = .ok m ∧ guards s m = .ok t := by
  rw [yes_alone h hk]
  constructor
  · rintro ⟨d, f1, s1⟩
    exact ⟨t, d, (guards_iff s t t).2 ⟨rfl, f1, s1⟩⟩
  · rintro ⟨m, d, g⟩
    obtain ⟨rfl, f1, s1⟩ := (guards_iff s m t).1 g
    exact ⟨d, f1, s1⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.noMark_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.seatSame_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.guards_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.leaveOpened_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.with_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.joined_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.alone_iff
