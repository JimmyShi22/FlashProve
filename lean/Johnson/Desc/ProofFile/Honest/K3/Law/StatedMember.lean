-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/StatedMember.lean: the digits of the head's link, and the
description's own member: from the decision of the sub-protocol that the lookups' lot states
(Honest/K3/Law/Stated.lean) to the decision of the description's own member, which is that
sub-protocol behind a guard on the state's mark (`guardMark`, Johnson/Desc/ProofFile/Frames1.lean),
under a name of the plan. Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("decision", "description", "mark", "member", "step without a round").
The lookup on the digits of the head's link is the one sort of place that Stated.lean does not
reach.

What is shown.
  `HeadBehind`, `stated_yes_head`: behind the digits of the head's link: the sub-protocol's decision
    accepts, conditional on one named hypothesis more: the step without a round that stands there
    returns.
  `putFork_failed`: writing a ledger changes no mark. (The library has that statement under the same
    short name: Johnson/Desc/First/Look/K3QuietLaws.lean.)
  `guardMark_yes`, `named_yes`: an acceptance by a sub-protocol that leaves no mark is an acceptance
    by the member.
  `blind_guardMark`, `blind_named`, `member_blind`: the member decides without reading a sealed
    digest.

Hypotheses that remain.
  `HeadBehind`, in `stated_yes_head`, with the hypotheses in front of the decision and the return of
    `hearV`: `hb`, `hl`, `hp`, `hN`, `hF`, `h0`, `hO`, `hn`, `hh`, as in `stated_yes_digits`
    (Stated.lean). No instance of `HeadBehind` is exhibited in this file.
  In `guardMark_yes` and `named_yes`: `h`, `hf`: the sub-protocol accepts, and no mark stands behind
    it.
  `hb`: (in `blind_guardMark`, `blind_named`) `DecidesBlind b`. `h`: (in `member_blind`) `theStated`
    returns the sub-protocol at the address.

Users. This file is imported by Honest/K3/Law/Joined.lean and Honest/K3/Law/StatedReply.lean.

Limits. The member with a sub-protocol of the kind "frame" joined behind it (the second form in
which a hearing sub-protocol stands in a chain) is not reached. That the description's member at a
lookup's place is the guard of the lot's sub-protocol under a name is the library's own equation
(Johnson/Desc/First/K9x/RanAtPure.lean), not called here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.StatedBlind
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Place noDigest)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG seatDigits quietHead
  theStated
  Readers)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## The digits of the head's link -/

/-- **The named hypothesis at the head's digits**: the step without a round that stands behind that
lookup returns, at the state t that the seated decision leaves. What that step reads (`quietHead`,
Johnson/Desc/First/Look/K3Whole.lean), none of it the lookup's: that the head's link is open; the
covered positions, of the request's words and the reply (`S.covered`); what the head's own rounds
heard (`a.x`) and the head's tables (`a.t`), both written by other sub-protocols; in the claim on
the committed weights (`weightsClaim`, Johnson/Desc/First/Look/LookQuiet.lean): the layout's call
and segment "HD0", the last unit of the weights' layout, and, at each covered position, that the
checked token is an entry of the vocabulary ("header-y"); that the plan has one claim on the
weights. -/
def HeadBehind (X : OnBytes.Model.Verify.Public) (t t' : FS) : Prop := quietHead X t = .ok t'

/-- **Behind the digits of the head's link.** Conditional on the hypotheses in front, on the return
of `hearV`, and on `HeadBehind`. -/
theorem stated_yes_head {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (p : P)
    (h : Shape) (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim true) p s (rs.take p.rounds.length)).bind (quietHead X))
    (s : FS) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (gs : List (List (Nat × List UInt64)))
    (hl : rs.length = p.rounds.length) (hp : p.shape = some h) (hN : 1 < h.NC)
    (hF : (seatDigits claim).fork s = some F) (h0 : ((seatDigits claim).heard s).isNone = true)
    (hO : ((seatDigits claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ decideVia (seatDigits claim) p s rs = .ok s' ∧
      (seatDigits claim).heard s' = some g' ∧ (seatDigits claim).fork s' = some G ∧
      s'.failed = s.failed ∧ ∀ t', HeadBehind X s' t' → b.decide s rs gs = .ok t' := by
  obtain ⟨g', s', hg, hd, a1, a2, a3⟩ := digits_accepts claim p h s hp hN hF h0 hO hn hh
  refine ⟨g', s', hg, hd, a1, a2, a3, fun t' ht => ?_⟩
  rw [hb, ← hl, List.take_length]
  have hd' : decideVia (seatOf claim true) p s rs = .ok s' := hd
  rw [hd']
  exact ht

/-! ## The guard on the mark -/

/-- Writing a ledger changes no mark. -/
theorem putFork_failed (s : FS) (G : Fork) : (s.putFork G).failed = s.failed := by
  unfold VerifiableInference.Desc.First.S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

/-- **An acceptance by a sub-protocol that leaves no mark is an acceptance behind the guard.**
Conditional on the sub-protocol's acceptance and on no mark behind it. -/
theorem guardMark_yes {b : Block FS ProofFile.Cl} {s s' : FS} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok s')
    (hf : s'.failed = none) : (ProofFile.guardMark b).decide s rs gs = .ok s' := by
  show (b.decide s rs gs).bind _ = _
  rw [h]
  show (match s'.failed with
    | none => Except.ok s'
    | some m => .error ("marked: " ++ m)) = _
  rw [hf]

/-- The same under a name.
Conditional on the same two. -/
theorem named_yes {b : Block FS ProofFile.Cl} (n : String) {s s' : FS} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok s')
    (hf : s'.failed = none) :
    ({ ProofFile.guardMark b with name := n } : Block FS ProofFile.Cl).decide s rs gs = .ok s' :=
  guardMark_yes h hf

theorem blind_guardMark {b : Block FS ProofFile.Cl} (hb : DecidesBlind b) :
    DecidesBlind (ProofFile.guardMark b) := by
  intro s rs gs
  show (b.decide s (rs.map noDigest) gs).bind _ = (b.decide s rs gs).bind _
  rw [hb]

theorem blind_named {b : Block FS ProofFile.Cl} (n : String) (hb : DecidesBlind b) :
    DecidesBlind ({ ProofFile.guardMark b with name := n } : Block FS ProofFile.Cl) :=
  blind_of_decide rfl (blind_guardMark hb)

/-- **The guard of the lot's sub-protocol, under a name, decides without reading a sealed digest.**
Conditional on there being a sub-protocol at the address. -/
theorem member_blind (claim : Aff → ProofFile.Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS ProofFile.Cl) (n : String)
    (h : theStated claim readers X codes shape a = some b) :
    DecidesBlind ({ ProofFile.guardMark b with name := n } : Block FS ProofFile.Cl) :=
  blind_named n (theStated_blind claim readers X codes shape a b h)

#print axioms ProofFile.Honest.K3.Law.stated_yes_head
#print axioms ProofFile.Honest.K3.Law.putFork_failed
#print axioms ProofFile.Honest.K3.Law.guardMark_yes
#print axioms ProofFile.Honest.K3.Law.named_yes
#print axioms ProofFile.Honest.K3.Law.blind_guardMark
#print axioms ProofFile.Honest.K3.Law.blind_named
#print axioms ProofFile.Honest.K3.Law.member_blind

end ProofFile.Honest.K3.Law
