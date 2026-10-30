-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/StatedReply.lean: the decision of the sub-protocol which the
lookups' lot states never changes the part of the state that holds the reply (`S.out`): what the
description's second guard on a member asks (`sameReply`, Johnson/Desc/ProofFile/Frames1.lean). And
the three steps without a round change no mark. Theorems, with no hypothesis but the decision's own
acceptance and, where the lot's sub-protocol is spoken of, that one stands at the address.

Terms. Honest/K3/GLOSSARY.md ("decision", "lot", "mark", "seat", "step without a round").

What is shown.
  `mark_out`, `putFork_out`, `putTl_out`, `hearLook_out`: the state's own functions that the seats
    call.
  `calls_put_out`, `digits_put_out`, `seatOf_put_out`: so neither seat's `put` changes `out`, at any
    state.
  `decideVia_put`, `decideVia_out`: an acceptance by the seated decision is the seat's `put`; so it
    does not change `out`.
  `quietLook_keeps`, `quietDigits_keeps`, `quietHead_keeps`, `quietAt_keeps`: an acceptance by a
    step without a round changes neither `out` nor the mark.
  `stated_out`, `theStated_out`, `theStated_sameReply`: the lot's sub-protocol: every acceptance by
    its decision leaves `out` as it was.
  `head_keeps`: at the digits of the head's link: behind `HeadBehind`
    (Honest/K3/Law/StatedMember.lean) the mark and `out` are as behind the decision.
Beside the library. Johnson/Desc/First/Look/K3ReplyLeaves.lean has the statements of `mark_out`,
`putFork_out`, `putTl_out` and `hearLook_out` under the same short names, and theorems on `out` at
the two seats' `put` (`calls_out`, `digits_out`), at the seated sub-protocol (`blockVia_put`,
`blockVia_out`), at the steps without a round (`quietLook_out`, `quietDigits_out`, `quietHead_out`,
`quietAt_out`) and at the whole sub-protocol (`theWhole_out`). This file calls none of them.

Hypotheses that remain. `h`: the decision, or the step without a round, accepts (in `head_keeps`:
`HeadBehind`). `hf`: (in `quietAt_keeps`) `quietAt` yields the step. `H`: (in `stated_out`)
`DecidesFrom`. `hb`: (in `theStated_out`, `theStated_sameReply`) `theStated` returns the
sub-protocol at the address.

Users. This file is imported by Honest/K3/Law/MemberYes.lean and Honest/K3/Shape/ClaimRuns.lean.

Limits. "Every acceptance": nothing here says that a decision accepts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.StatedMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (Block Place named need)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits quietAt quietLook quietDigits quietHead
  theStated
  Readers)
open VerifiableInference.Desc.K3.Law (decideVia hearVia)
open VerifiableInference.Desc.First.Look (P slotsTaken)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## The state's own functions -/

theorem mark_out (s : FS) (n : String) : (s.mark n).out = s.out := by
  unfold VerifiableInference.Desc.First.S.mark
  split <;> rfl

theorem putFork_out (s : FS) (G : Fork) : (s.putFork G).out = s.out := by
  unfold VerifiableInference.Desc.First.S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem putTl_out (s : FS) (tl : OnBytes.Model.HTailF2) : (s.putTl tl).out = s.out := by
  unfold VerifiableInference.Desc.First.S.putTl
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem hearLook_out (s : FS) (g : OnBytes.Model.Forest.Heard) : (s.hearLook g).out = s.out := by
  unfold VerifiableInference.Desc.First.S.hearLook
  split
  · split
    · exact mark_out s _
    · rfl
  · split
    · exact mark_out s _
    · rfl
  · split
    · exact mark_out s _
    · split
      · exact mark_out s _
      · rfl
  · exact mark_out s _

/-! ## The seats -/

theorem calls_put_out {Cl : Type} (claim : Aff → Cl) (s : FS) (g : OnBytes.Model.Forest.Heard)
    (G : Fork) : ((seatCalls claim).put s g G).out = s.out := by
  show ((s.putFork G).hearLook g).out = s.out
  rw [hearLook_out, putFork_out]

theorem digits_put_out {Cl : Type} (claim : Aff → Cl) (s : FS) (g : OnBytes.Model.Forest.Heard)
    (G : Fork) : ((seatDigits claim).put s g G).out = s.out := by
  show (match s.tl?, s.fork? with
    | some tl, some F => _
    | _, _ => _ : FS).out = s.out
  split
  · rw [putFork_out, putTl_out]
  · exact mark_out s _

theorem seatOf_put_out {Cl : Type} (claim : Aff → Cl) (digits : Bool) (s : FS)
    (g : OnBytes.Model.Forest.Heard) (G : Fork) : ((seatOf claim digits).put s g G).out = s.out :=
      by
  cases digits
  · exact calls_put_out claim s g G
  · exact digits_put_out claim s g G

/-- An acceptance by the seated decision is the seat's `put`. Conditional on that acceptance. -/
theorem decideVia_put {S Cl : Type} (seat : Seat S Cl) (p : P) (s s' : S) (rs : List Fmt.RoundView)
    (h : decideVia seat p s rs = .ok s') : ∃ g G, s' = seat.put s g G := by
  unfold decideVia at h
  cases hF : seat.fork s with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    by_cases h1 : (seat.heard s).isNone = true
    · by_cases h2 : (seat.owed s).noneWaits = true
      · by_cases h3 : (F.next == p.first) = true
        · cases hv : hearVia p F rs with
          | none => simp [hF, h1, h2, h3, hv, named, need, bind, Except.bind] at h
          | some x =>
            simp [hF, h1, h2, h3, hv, named, need, bind, Except.bind, pure, Except.pure] at h
            exact ⟨x.1, x.2, h.symm⟩
        · simp [hF, h1, h2, h3, named, need, bind, Except.bind] at h
      · simp [hF, h1, h2, named, need, bind, Except.bind] at h
    · simp [hF, h1, named, need, bind, Except.bind] at h

/-- Every acceptance by the seated decision leaves `out` as it was. Conditional on that acceptance.
-/
theorem decideVia_out {Cl : Type} (claim : Aff → Cl) (digits : Bool) (p : P) (s s' : FS)
    (rs : List Fmt.RoundView) (h : decideVia (seatOf claim digits) p s rs = .ok s') : s'.out = s.out := by
  obtain ⟨g, G, rfl⟩ := decideVia_put _ p s s' rs h
  exact seatOf_put_out claim digits s g G

/-! ## The steps without a round -/

/-- Conditional on the step's acceptance. -/
theorem quietLook_keeps (fs : OnBytes.Model.Forest.Shape) (s t : FS) (h : quietLook fs s = .ok t) :
    t = s := by
  unfold quietLook at h
  cases hg : s.lookHeard? with
  | none => simp [hg, named, bind, Except.bind] at h
  | some g =>
    by_cases hs : VerifiableInference.Desc.First.Look.sameShape g.shape fs = true
    · simp [hg, hs, named, need, bind, Except.bind, pure, Except.pure] at h
      exact h.symm
    · simp [hg, hs, named, need, bind, Except.bind] at h

/-- Conditional on the step's acceptance. -/
theorem quietDigits_keeps (used claims : Nat) (s t : FS) (h : quietDigits used claims s = .ok t) :
    t.out = s.out ∧ t.failed = s.failed := by
  unfold quietDigits at h
  cases hF : s.fork? with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    cases hG : slotsTaken used claims F with
    | none => simp [hF, hG, named, bind, Except.bind] at h
    | some G =>
      simp [hF, hG, named, bind, Except.bind, pure, Except.pure] at h
      rw [← h]
      exact ⟨putFork_out s G, putFork_failed s G⟩

/-- Conditional on the step's acceptance. -/
theorem quietHead_keeps (X : OnBytes.Model.Verify.Public) (s t : FS) (h : quietHead X s = .ok t) :
    t.out = s.out ∧ t.failed = s.failed := by
  unfold quietHead at h
  split at h
  · rename_i a _
    simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at h; rw [← h]; exact ⟨rfl, rfl⟩)
      | cases h
  · cases h

/-- **An acceptance by the step that stands behind a lookup changes neither `out` nor the mark.**
Conditional on that acceptance. -/
theorem quietAt_keeps (X : OnBytes.Model.Verify.Public) (i : Nat) (digits : Bool)
    (f : FS → Except String FS) (hf : quietAt X i digits = some f) (s t : FS) (h : f s = .ok t) :
    t.out = s.out ∧ t.failed = s.failed := by
  unfold quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact quietDigits_keeps _ _ s t h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact quietHead_keeps X s t h
         | (rw [quietLook_keeps _ s t h]; exact ⟨rfl, rfl⟩))
    | cases hf

/-! ## The lot's sub-protocol -/

/-- **Every acceptance by such a sub-protocol's decision leaves `out` as it was.** Conditional on
that acceptance. -/
theorem stated_out {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {a : Place}
    {b : Block FS Cl} {q : Bool} (H : DecidesFrom claim X a b q) (s t : FS) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide s rs gs = .ok t) : t.out = s.out := by
  obtain ⟨i, digits, p, _, _, _, _, H⟩ := H
  rcases H with ⟨_, H⟩ | ⟨_, f, hf, H⟩
  · rw [H] at h
    exact decideVia_out claim digits p s t rs h
  · rw [H] at h
    cases hd : decideVia (seatOf claim digits) p s (rs.take p.rounds.length) with
    | error e => rw [hd] at h; exact nomatch h
    | ok s' =>
      rw [hd] at h
      exact (quietAt_keeps X i digits f hf s' t h).1.trans (decideVia_out claim digits p s s' _ hd)

/-- The lot's sub-protocol at every address. Conditional on there being a sub-protocol there, and
on its acceptance. -/
theorem theStated_out {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (hb : theStated claim readers X codes shape a = some b) (s t : FS)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide s rs gs = .ok t) :
    t.out = s.out :=
  stated_out (theStated_decides claim readers X codes shape a b hb) s t rs gs h

/-- **The description's guard on the reply accepts behind every acceptance by the lot's
sub-protocol.** Conditional on there being a sub-protocol at the address, and on its acceptance. -/
theorem theStated_sameReply {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (hb : theStated claim readers X codes shape a = some b) (s t : FS)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide s rs gs = .ok t) :
    ProofFile.sameReply s t = true ∧ ProofFile.sameReply t s = true := by
  have e := theStated_out claim readers X codes shape a b hb s t rs gs h
  unfold ProofFile.sameReply
  rw [e]
  simp

/-- **At the digits of the head's link**: behind the named hypothesis the mark and `out` are as
behind the seated decision. Conditional on `HeadBehind`. -/
theorem head_keeps (X : OnBytes.Model.Verify.Public) (s' t' : FS) (h : HeadBehind X s' t') :
    t'.out = s'.out ∧ t'.failed = s'.failed := quietHead_keeps X s' t' h

#print axioms ProofFile.Honest.K3.Law.mark_out
#print axioms ProofFile.Honest.K3.Law.putFork_out
#print axioms ProofFile.Honest.K3.Law.putTl_out
#print axioms ProofFile.Honest.K3.Law.hearLook_out
#print axioms ProofFile.Honest.K3.Law.calls_put_out
#print axioms ProofFile.Honest.K3.Law.digits_put_out
#print axioms ProofFile.Honest.K3.Law.seatOf_put_out
#print axioms ProofFile.Honest.K3.Law.decideVia_put
#print axioms ProofFile.Honest.K3.Law.decideVia_out
#print axioms ProofFile.Honest.K3.Law.quietLook_keeps
#print axioms ProofFile.Honest.K3.Law.quietDigits_keeps
#print axioms ProofFile.Honest.K3.Law.quietHead_keeps
#print axioms ProofFile.Honest.K3.Law.quietAt_keeps
#print axioms ProofFile.Honest.K3.Law.stated_out
#print axioms ProofFile.Honest.K3.Law.theStated_out
#print axioms ProofFile.Honest.K3.Law.theStated_sameReply
#print axioms ProofFile.Honest.K3.Law.head_keeps

end ProofFile.Honest.K3.Law
