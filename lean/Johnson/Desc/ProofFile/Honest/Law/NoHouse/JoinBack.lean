-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/JoinBack.lean: THE 25 LINKS' FIRST HEARING MEMBERS: THE
WAY BACK AT THE STEP. Such a member b of the first chain's flat list is a lot's sub-protocol b' with
the frame's «opened» of the link's own row joined behind it, under the seat's guards (the library's
`IM.Joined`, Johnson/IMR/SameSpot.lean). The library has the way forward: a yes of b's step is a yes
of b''s step to a state between, no mark there; then «opened»'s yes from there, no mark, the reply
as it was (`IM.Joined.step`, Johnson/IMR/FirstSeats.lean, whose head names «the way back at the
step» as not claimed). Here BOTH WAYS, AS ONE EQUIVALENCE.

WHAT THIS IS. Lemmas on the library's definitions. None of the library's goals.

  `seated_step_iff`   at the term `IM.seatedWith ProofFile.sameReply b' q name a`, q without a round:
                      general in b', q, the name and the address
  `opened_yes`   the joined half's decision, with its mark's guard, is the row's «opened» with no
                 mark behind it
  `joined_step_iff`   at `IM.Joined`, at the row f of the link's number
  `joined_step_back`   THE WAY BACK: what whoever owes «the member says yes» (`AcceptedS`,
                       Honest/Thread/PaysS.lean) is to bring: b''s step's yes · no mark between ·
                       «opened»'s yes · no mark behind · the reply as it was from the state between
                       · and, at an address that is not K7's, from the state in front

CALLED, NOT TYPED: `IM.step_iff` (a step reads its rounds and its decision alone),
`IM.guardMark_yes` (Johnson/IMR/SeatForm.lean) · `guarded_yes`
(Johnson/Desc/Sound/SeatGuardLaws.lean) · **`andThen_step_noRound`**
(Johnson/Top/H0/StepLaws/StepLaws.lean: two sub-protocols laid as one, the second without a round:
an equivalence).

Limits. Nothing says that either half's yes can be had. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.IMR.FirstSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn Place KindName andThen_step_noRound guarded_yes)
open VerifiableInference.Desc.First (S hearsReply)
open ProofFile (Cl)

/-- **A LOT's SUB-PROTOCOL WITH ONE WITHOUT A ROUND JOINED BEHIND IT, AS IT IS SEATED: ITS STEP,
BOTH WAYS.** -/
theorem seated_step_iff (b' q : Block S Cl) (name : String) (a : Place) (hq : q.rounds = [])
    (ft : Nat) (s t : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (IM.seatedWith ProofFile.sameReply b' q name a).step ft s rs cols = .ok (t, n) ↔
      (∃ m, b'.step ft s rs cols = .ok (m, n) ∧ m.failed = none ∧
        q.decide m [] [] = .ok t ∧ ProofFile.sameReply m t = true) ∧
      (hearsReply a = false → ProofFile.sameReply s t = true) := by
  -- the driver's guard around the whole
  have g1 := IM.step_iff
    (c := IM.seatedWith ProofFile.sameReply b' q name a)
    (d := (IM.marked b' name).andThen name (q.guarded ProofFile.sameReply fun _ => false))
    (Q := fun s t => hearsReply a = false → ProofFile.sameReply s t = true) rfl
    (fun s rs gs t => by
      cases hh : hearsReply a with
      | true =>
        show (if hearsReply a then ((IM.marked b' name).andThen name
            (q.guarded ProofFile.sameReply fun _ => false)).decide s rs gs
          else (((IM.marked b' name).andThen name
            (q.guarded ProofFile.sameReply fun _ => false)).decide s rs gs).bind
              (VerifiableInference.Desc.seatSame ProofFile.sameReply s)) = .ok t ↔ _
        rw [hh, if_pos rfl]
        exact ⟨fun h => ⟨h, fun e => by cases e⟩, fun h => h.1⟩
      | false =>
        have h0 := guarded_yes ProofFile.sameReply hearsReply
          ({ (IM.marked b' name).andThen name (q.guarded ProofFile.sameReply fun _ => false) with
            place := a } : Block S Cl) hh s rs gs t
        exact ⟨fun h => ⟨(h0.1 h).1, fun _ => (h0.1 h).2⟩, fun h => h0.2 ⟨h.1, h.2 rfl⟩⟩)
    ft s t n rs cols
  rw [g1, andThen_step_noRound name (IM.marked b' name)
    (q.guarded ProofFile.sameReply fun _ => false) hq ft s t rs cols n]
  refine and_congr_left fun _ => exists_congr fun m => ?_
  -- the mark's test off the first half; the guard off the second
  rw [IM.step_iff (c := IM.marked b' name) (d := b') (Q := fun _ t => t.failed = none) rfl
      (fun s rs gs t => IM.guardMark_yes b' s t rs gs) ft s m n rs cols,
    guarded_yes ProofFile.sameReply (fun _ => false) q rfl m [] [] t, and_assoc]

/-- The joined half's decision is the row's «opened», with no mark behind it. -/
theorem opened_yes (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m t : S) :
    (ProofFile.guardMark ((IM.openedOf f).retype : Block S Cl)).decide m [] [] = .ok t ↔
      f.opened m = .ok t ∧ t.failed = none :=
  IM.guardMark_yes _ m t [] []

/-- **A LINK's FIRST HEARING MEMBER: ITS STEP, BOTH WAYS**, at the link's own row f. -/
theorem joined_step_iff {Z : ProofFile.Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (hj : IM.Joined Z l b b' a) {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    (hf : fs[l]? = some f) (ft : Nat) (s t : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    b.step ft s rs cols = .ok (t, n) ↔
      (∃ m, b'.step ft s rs cols = .ok (m, n) ∧ m.failed = none ∧
        (f.opened m = .ok t ∧ t.failed = none) ∧ ProofFile.sameReply m t = true) ∧
      (hearsReply a = false → ProofFile.sameReply s t = true) := by
  obtain ⟨fs', f', hfs', hf', e⟩ := hj
  obtain rfl := Except.ok.inj (hfs.symm.trans hfs')
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  rw [e, seated_step_iff b' _ b.name a rfl ft s t n rs cols]
  simp only [opened_yes]

/-- **THE WAY BACK.** -/
theorem joined_step_back {Z : ProofFile.Pub} {l : Nat} {b b' : Block S Cl} {a : Place}
    (hj : IM.Joined Z l b b' a) {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    (hf : fs[l]? = some f) {ft : Nat} {s m t : S} {n : Nat} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (h1 : b'.step ft s rs cols = .ok (m, n)) (h2 : m.failed = none) (h3 : f.opened m = .ok t)
    (h4 : t.failed = none) (h5 : ProofFile.sameReply m t = true)
    (h6 : a.kind ≠ KindName.K7 → ProofFile.sameReply s t = true) : b.step ft s rs cols = .ok (t, n) :=
  (joined_step_iff hj hfs hf ft s t n rs cols).2 ⟨⟨m, h1, h2, ⟨h3, h4⟩, h5⟩,
    fun hh => h6 fun hk => by
      have e : hearsReply a = true := by
        show (a.kind == KindName.K7) = true
        rw [hk]
        rfl
      rw [e] at hh
      cases hh⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.seated_step_iff
#print axioms ProofFile.Honest.opened_yes
#print axioms ProofFile.Honest.joined_step_iff
#print axioms ProofFile.Honest.joined_step_back
