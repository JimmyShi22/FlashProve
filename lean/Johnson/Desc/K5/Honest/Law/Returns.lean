-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Returns.lean: CONDITIONAL: when the decision of the kind "an attention
segment's own rounds" (K5; Johnson/Desc/First/Att/K5AttentionKind.lean) at the first chain's state says yes, and
what the state behind its yes is. Over the library alone: no prover's text is read here.

The decision compares no value. It refuses where a count of rows waits, where no attention segment
is open, where the state bears a mark of failure, where the lookup on the calls has laid nothing,
where a round has another shape than the plan's, where the ledger lacks room, and where the
segment's rounds have been heard before. So its yes follows from facts on the state's own
book-keeping fields and from the shape of the rounds.

  `k5_returns`   CONDITIONAL: the test on the plan says yes, the state is ready (`ReadyO`,
                 Johnson/Desc/First/Att/K05SeatAccepts.lean) and the rounds have the plan's shape
                 (`Fits`, Johnson/Desc/Part/MaskedSumShape.lean): the decision says yes, with the
                 state `behind s a hd G`, where hd and G are the hearing's own return
  `k5_yes_is`    the other way: every yes of the decision is of that form
  `BehindIs`, `k5_behind_is`   the book-keeping fields behind a return of the hearing: the
                 ledger's number of slots, its next free number, its arrays' lengths, what it
                 keeps; no count of rows waits; the segment's rounds stand heard; mark and reply
                 are as in front
  `k5_returns_whole`   CONDITIONAL: the first and the third in one statement: under the premises of
                 `k5_returns` the decision says yes, and the book-keeping fields behind are these
  `K5Keeps`, `k5_keeps`   what the kind's step leaves of the state as it was

Who is meant to pay the premises. The test on the plan: a fact on the public plan. `ReadyO`: what
is known of the state in front of the kind's place. `Fits`: whoever shows what the rounds hold.

Limits. Every theorem here is conditional, and none shows that a ready state is ever reached.
`K5Keeps` is a definition: nothing is claimed of it. Nothing is said of any value that is heard.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05SeatAccepts
import Johnson.Desc.First.Att.K05SeatKeeps
import Johnson.Desc.First.Att.K05BehindLay3
import Johnson.Desc.First.Att.K05LeftOn
import Johnson.Desc.First.Att.K05HearBelow
import Johnson.Desc.Part.MaskedSumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Fits Free partReturns)
open VerifiableInference.Desc.First.Att.P

/-! ## 1 The yes -/

/-- **The kind's decision returns.** CONDITIONAL: under the plan's test, a ready state and rounds of
the plan's shape. No premise speaks of a value that the prover sends. -/
theorem k5_returns (p : Par) (hp : planOk p = true) {s : First.S} (R : ReadyO p s)
    {rs : List Fmt.RoundView} (hfit : Fits ((rounds p).map (·.entry)) rs) :
    ∃ a hd G, s.here = .att a ∧ hear p.own (a.F, rs, 0) = some (hd, G, [], 0) ∧
      decide seatSO p s rs = .ok (behind s a hd G) := by
  obtain ⟨a, g, hh, hg, h5, hz, hfree⟩ := R.open_
  obtain ⟨hd, G, e⟩ := hear_returns partReturns p hp hz hfit hfree
  obtain ⟨s', hl⟩ := seatSO_lays hh hg h5 R.clean hd G
  have hF : seatSO.ledger s = some a.F := by
    show (match s.here with
      | .att a => some a.F
      | _ => none) = some a.F
    rw [hh]
  obtain ⟨a', e', -, rfl⟩ := lay_is hF hl
  rw [hh] at e'
  cases e'
  refine ⟨a, hd, G, hh, e, (decide_lays seatSO p s _ rs).2 ⟨?_, a.F, hd, G, hF, e, hl⟩⟩
  show (if s.noneWaits then none else s.rowsOwed) = none
  rw [R.none_]
  rfl

/-- **Every yes of the kind's decision**: an attention segment stands open, the hearing has returned
from its ledger with all rounds used up, and the state behind is `behind s a hd G`. CONDITIONAL: the
yes is a premise. -/
theorem k5_yes_is (p : Par) {s s' : First.S} {rs : List Fmt.RoundView}
    (h : decide seatSO p s rs = .ok s') :
    ∃ a hd G, s.here = .att a ∧ hear p.own (a.F, rs, 0) = some (hd, G, [], 0) ∧
      s' = behind s a hd G := by
  obtain ⟨-, F, hd, G, hF, e, hl⟩ := (decide_lays seatSO p s s' rs).1 h
  obtain ⟨a, hh, rfl, rfl⟩ := lay_is hF hl
  exact ⟨a, hd, G, hh, e, rfl⟩

/-! ## 2 The book-keeping behind -/

/-- The book-keeping fields of the state behind the kind's yes, against those in front. own: the
plan's numbers of the segment's rounds. -/
structure BehindIs (own : Params.AttentionRounds) (s : First.S) (a : First.AttOwn) (hd : Heard)
    (G : Fork) : Prop where
  ns : G.ns = a.F.ns
  next : G.next = a.F.next + slotsOf (script own)
  sized : Road.Sized G
  later : PscRun.Later a.F G
  below : Below a.F G
  here : (behind s a hd G).here = .att { a with F := G, heard5 := some hd }
  rows : (behind s a hd G).rowsOwed = none
  waits : (behind s a hd G).noneWaits = true
  failed : (behind s a hd G).failed = s.failed
  out : (behind s a hd G).out = s.out

/-- **The book-keeping behind a return of the hearing.** CONDITIONAL: the ledger in front has its
arrays' lengths, and the slots that the segment's rounds take are free. -/
theorem k5_behind_is {own : Params.AttentionRounds} (s : First.S) {a : First.AttOwn} {hd : Heard}
    {G : Fork} {rs : List Fmt.RoundView} (hh : hear own (a.F, rs, 0) = some (hd, G, [], 0))
    (hz : Road.Sized a.F) (hfree : Free a.F a.F.next (slotsOf (script own))) :
    BehindIs own s a hd G := by
  have R : Room a.F a.F.ns a.F.next (slotsOf (script own) + 0) := ⟨rfl, rfl, hz, hfree⟩
  have RG := room_behind hh R
  obtain ⟨lt, zG⟩ := later_behind hh hz
  exact
    { ns := RG.ns
      next := RG.next
      sized := zG
      later := ⟨lt.next, lt.ns, fun _ => ⟨zG.vp, zG.mf, zG.got⟩, lt.keep⟩
      below := (hear_below hh hz).2
      here := rfl
      rows := rfl
      waits := rfl
      failed := rfl
      out := rfl }

/-- **THE KIND's DECISION RETURNS, AND THE BOOK-KEEPING FIELDS BEHIND ARE THESE**: in one statement.
CONDITIONAL: under the plan's test, a ready state and rounds of the plan's shape. No premise speaks
of a value that the prover sends: the kind has no test on values. -/
theorem k5_returns_whole (p : Par) (hp : planOk p = true) {s : First.S} (R : ReadyO p s)
    {rs : List Fmt.RoundView} (hfit : Fits ((rounds p).map (·.entry)) rs) :
    ∃ a hd G, s.here = .att a ∧ hear p.own (a.F, rs, 0) = some (hd, G, [], 0) ∧
      decide seatSO p s rs = .ok (behind s a hd G) ∧ BehindIs p.own s a hd G := by
  obtain ⟨a, hd, G, e, hh, hdec⟩ := k5_returns p hp R hfit
  obtain ⟨a', -, e', -, -, hz, hfree⟩ := R.open_
  rw [e] at e'
  cases e'
  exact ⟨a, hd, G, e, hh, hdec, k5_behind_is s hh hz hfree⟩

/-! ## 3 What the step leaves -/

/-- **What the kind's step leaves of the state as it was**: every field but the count of rows owed,
the open attention segment's ledger and what its own rounds have heard. Of the ledger: the one
behind is a later state of the one in front (as many slots; what lies under a filled slot is kept);
below the next free number in front its three arrays on slots are as they were; and every other
field but the next free number is as it was (its trees among them). It is a definition: a premise's
form. Nothing is claimed of it. -/
def K5Keeps (s s' : First.S) : Prop :=
  restO s' = restO s ∧ ∃ a a', s.here = .att a ∧ s'.here = .att a' ∧ PscRun.Later a.F a'.F ∧
    Below a.F a'.F

/-- **The kind's yes leaves that.** CONDITIONAL: the open ledger in front has its arrays' lengths.
-/
theorem k5_keeps (p : Par) {s s' : First.S} {rs : List Fmt.RoundView}
    (h : decide seatSO p s rs = .ok s') (hz : ∀ a, s.here = .att a → Road.Sized a.F) :
    K5Keeps s s' := by
  obtain ⟨-, F, hd, G, hF, e, hl⟩ := (decide_lays seatSO p s s' rs).1 h
  have hr := seatSO_rest hl
  obtain ⟨a, hh, rfl, rfl⟩ := lay_is hF hl
  obtain ⟨lt, zG⟩ := later_behind e (hz a hh)
  exact ⟨hr, a, _, hh, rfl, ⟨lt.next, lt.ns, fun _ => ⟨zG.vp, zG.mf, zG.got⟩, lt.keep⟩,
    (hear_below e (hz a hh)).2⟩

end H2K5.Honest

#print axioms H2K5.Honest.k5_returns
#print axioms H2K5.Honest.k5_yes_is
#print axioms H2K5.Honest.k5_behind_is
#print axioms H2K5.Honest.k5_returns_whole
#print axioms H2K5.Honest.k5_keeps
