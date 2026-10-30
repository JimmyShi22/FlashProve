-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Stated.lean: the decision of the sub-protocol that the lookups'
lot states (`theStated`, Johnson/Desc/First/Look/K3Stated.lean): what it is, and that it accepts
where `hearV` returns. Theorems, with two definitions.

Terms. Honest/K3/GLOSSARY.md ("address", "decision", "lot", "seat", "step without a round",
"sub-protocol").

What is shown.
  `seatOf`: the seat at a lookup on the calls, or on the digits. It has the text of the library's
    `K3.seatOfLookupOnDigitsOrCalls` (Johnson/Desc/First/Look/K3OwnIs.lean); the tie: `seatOf_eq_lookSeat`
    (Honest/K3/Law/Ties.lean [not in this library]).
  `DecidesFrom`: what is said of a sub-protocol at an address: the place's own parameters; its
    rounds are theirs; its decision is `decideVia` at the seat, then the step without a round that
    stands behind the lookup (`quietAt`), where one stands there.
  `theOwn_decides`, `theWhole_decides`, `theStated_decides`: that holds of the three texts, one over
    the other. (The library's `theOwn_is`, `theWhole_is`, `theStated_is`, K3OwnIs.lean, run beside
    them.)
  `quietLook_returns`, `quietDigits_returns`: two of the three steps without a round return, from
    what the seated decision leaves and one public test each.
  `stated_yes_plain`, `stated_yes_look`, `stated_yes_digits`: the sub-protocol's own decision
    accepts: where nothing stands behind the lookup (the calls of an attention link and of the
    head's); behind a layers' link's calls; behind the digits of a layers' or an attention link. The
    three speak of a sub-protocol b whose decision has the form in question (`hb`), with the step
    behind at letters: that the lot's sub-protocol has that form is `theStated_decides`; the
    composition is a caller's.

Hypotheses that remain, in the three `stated_yes_…`.
  `hb`: the decision's form. `hp`, `hN`: the place's parameters make the shape h; it has more than
    one call.
  `hl`: (in `stated_yes_look`, `stated_yes_digits`) as many rounds as the parameters state.
  The two public tests (`hfs`: the shape is the layout's; `hu`: the lookup ends at the plan's number
    of slots): numbers of the public structure alone.
  In front of the decision (`hF`, `h0`, `hO`, `hn`; `hS` in `stated_yes_digits`): a ledger is open;
    nothing is heard yet; no rows are owed; the count of slots is the place's; arrays of the right
    size. These are for a caller that walks the chain to show.
  `hh`: that `hearV` returns on the honest rounds is another statement's.
In the others: `h`: the library's text returns the sub-protocol at the address. `hg`, `hs`: (in
`quietLook_returns`) what was heard is stored; its shape is the layout's. `hF`, `hn`: (in
`quietDigits_returns`) a ledger is open; its next slot is the plan's number.

Users. This file is imported by Honest/K3/Law/StatedBlind.lean.

Limits. Not reached: the digits of the head's link. The step behind that lookup (`quietHead`) reads
what the head's own rounds heard, the head's tables and the covered positions, and makes the claim
on the weights: its hypotheses are other kinds'. Shown in part: `stated_yes_head`
(Honest/K3/Law/StatedMember.lean): the decision accepts there too, conditional, besides, on
`HeadBehind`: that this step returns, which remains a hypothesis there. This is the sub-protocol's
`decide`: the tests of `Block.step` around it are not walked here. Shown in part: `step_yes`
(Honest/K3/Law/StepYes.lean) with `theStated_blind` (Honest/K3/Law/StatedBlind.lean): the step
accepts just where the decision does, under the five hypotheses of `step_iff_decide`, which remain
hypotheses there.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedAll
import Johnson.Desc.First.Look.K3Stated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Fork Aff)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc (Block Place named need)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG Seat seatCalls seatDigits
  pieceAt
  theOwn theWhole theStated quietAt quietLook quietDigits Readers)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (P placeAt sameShape slotsTaken)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The seat at a lookup on the digits, or on the calls. -/
def seatOf {Cl : Type} (claim : Aff → Cl) (digits : Bool) : Seat FS Cl :=
  if digits then seatDigits claim else seatCalls claim

/-- **What is said of a sub-protocol at an address.** -/
def DecidesFrom {Cl : Type} (claim : Aff → Cl) (X : OnBytes.Model.Verify.Public) (a : Place)
    (b : Block FS Cl) (quiet : Bool) : Prop :=
  ∃ i digits p, a.link = some i ∧ a.piece = pieceAt X i digits ∧ placeAt X i digits = some p ∧
    b.rounds = p.rounds ∧
    ((quiet = false ∨ quietAt X i digits = none) ∧
        (∀ s rs gs, b.decide s rs gs = decideVia (seatOf claim digits) p s rs) ∨
      quiet = true ∧ ∃ f, quietAt X i digits = some f ∧ ∀ s rs gs, b.decide s rs gs =
        (decideVia (seatOf claim digits) p s (rs.take p.rounds.length)).bind f)

/-- Conditional on there being a sub-protocol at the address. -/
theorem theOwn_decides {Cl : Type} (claim : Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (h : theOwn claim runs X codes shape a = some b) :
    DecidesFrom claim X a b false := by
  unfold theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, hi, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hp
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, hpl, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      refine ⟨i, digits, p, hi, by simpa using hp, hpl, ?_, Or.inl ⟨Or.inl rfl, ?_⟩⟩
      · cases runs <;> rfl
      · intro s rs gs
        cases runs <;> rfl

theorem piece_digits (X : OnBytes.Model.Verify.Public) (i : Nat) (d : Bool) :
    (pieceAt X i d == pieceAt X i true) = d := by
  unfold pieceAt
  cases d <;> split <;> rfl

/-- Conditional on there being a sub-protocol at the address. -/
theorem theWhole_decides {Cl : Type} (claim : Aff → Cl) (runs : Bool)
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (h : theWhole claim runs X codes shape a = some b) :
    DecidesFrom claim X a b true := by
  unfold theWhole at h
  obtain ⟨b₀, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨i, digits, p, h1, h2, h3, h4, h5⟩ := theOwn_decides claim runs X codes shape a b₀ hb
  have h5' : ∀ s rs gs, b₀.decide s rs gs = decideVia (seatOf claim digits) p s rs := by
    rcases h5 with ⟨_, h5⟩ | ⟨h5, _⟩
    · exact h5
    · exact nomatch h5
  have hq : (a.link.bind fun i => quietAt X i (a.piece == pieceAt X i true)) = quietAt X i digits :=
    by
    rw [h1, h2]
    show quietAt X i (pieceAt X i digits == pieceAt X i true) = _
    rw [piece_digits]
  refine ⟨i, digits, p, h1, h2, h3, ?_⟩
  rw [hq]
  cases hf : quietAt X i digits with
  | none => exact ⟨h4, Or.inl ⟨Or.inr rfl, h5'⟩⟩
  | some f =>
    refine ⟨?_, Or.inr ⟨rfl, f, rfl, fun s rs gs => ?_⟩⟩
    · show b₀.rounds ++ [] = p.rounds
      rw [List.append_nil, h4]
    · show (b₀.decide s (rs.take b₀.rounds.length) (gs.take b₀.openings)).bind _ = _
      rw [h5', h4]
      rfl

/-- **The decision of the lot's sub-protocol is the seated decision, then the step without a round
where one stands.** Conditional on there being a sub-protocol at the address. No instance of these
hypotheses is exhibited in this file. -/
theorem theStated_decides {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (h : theStated claim readers X codes shape a = some b) :
    DecidesFrom claim X a b true := by
  unfold theStated at h
  obtain ⟨b₀, hb, h⟩ := Option.bind_eq_some_iff.1 h
  have H := theWhole_decides claim true X codes shape a b₀ hb
  split at h
  · obtain rfl := Option.some.inj h
    exact H
  · split at h
    · obtain rfl := Option.some.inj h
      exact H
    · split at h
      · obtain rfl := Option.some.inj h
        exact H
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact H

/-! ## The steps without a round -/

/-- Behind a layers' link's calls: what was heard is stored, and its shape is the layout's.
Conditional on both. -/
theorem quietLook_returns (fs : Shape) (s : FS) {g' : OnBytes.Model.Forest.Heard}
    (hg : s.lookHeard? = some g') (hs : sameShape g'.shape fs = true) : quietLook fs s = .ok s := by
  unfold quietLook
  simp [hg, hs, named, need, bind, Except.bind, pure, Except.pure]

/-- Behind the digits of a layers' or an attention link: a ledger is open, and its count of slots is
the plan's number.
Conditional on both. -/
theorem quietDigits_returns (used claims : Nat) (s : FS) {G : Fork} (hF : s.fork? = some G)
    (hn : G.next = used) :
    quietDigits used claims s = .ok (s.putFork { G with planClaimsF := claims }) := by
  unfold quietDigits
  simp [hF, hn, slotsTaken, named, bind, Except.bind, pure, Except.pure]

/-! ## The sub-protocol's own decision accepts -/

/-- **Where nothing stands behind the lookup.** Conditional on the hypotheses in front and
on the return of `hearV`. -/
theorem stated_yes_plain {Cl : Type} (claim : Aff → Cl) (p : P) (h : Shape) (digits : Bool)
    (b : Block FS Cl) (hb : ∀ s rs gs, b.decide s rs gs = decideVia (seatOf claim digits) p s rs)
    (s : FS) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (gs : List (List (Nat × List UInt64)))
    (hp : p.shape = some h) (hN : 1 < h.NC) (hF : (seatOf claim digits).fork s = some F)
    (h0 : ((seatOf claim digits).heard s).isNone = true)
    (hO : ((seatOf claim digits).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ b.decide s rs gs = .ok s' ∧
      (seatOf claim digits).heard s' = some g' ∧ (seatOf claim digits).fork s' = some G ∧
      s'.failed = s.failed := by
  rw [hb]
  cases digits with
  | false => exact calls_accepts claim p h s hp hN hF h0 hO hn hh
  | true => exact digits_accepts claim p h s hp hN hF h0 hO hn hh

/-- **Behind a layers' link's calls.** fs: the layout's shape. Conditional on the hypotheses in
front, on the return of `hearV`, and on one public test: the place's shape is the layout's.
No instance of these hypotheses at this seat is exhibited in this file (at a small seat:
Honest/K3/Law/SeatedGuards.lean [not in this library], by evaluation). -/
theorem stated_yes_look {Cl : Type} (claim : Aff → Cl) (p : P) (h fs : Shape) (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim false) p s (rs.take p.rounds.length)).bind (quietLook fs))
    (s : FS) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (gs : List (List (Nat × List UInt64)))
    (hl : rs.length = p.rounds.length) (hp : p.shape = some h) (hN : 1 < h.NC)
    (hfs : sameShape h fs = true) (hF : (seatCalls claim).fork s = some F)
    (h0 : ((seatCalls claim).heard s).isNone = true)
    (hO : ((seatCalls claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧ b.decide s rs gs = .ok s' ∧
      (seatCalls claim).heard s' = some g' ∧ (seatCalls claim).fork s' = some G ∧
      s'.failed = s.failed := by
  obtain ⟨g', s', hg, hd, a1, a2, a3⟩ := calls_accepts claim p h s hp hN hF h0 hO hn hh
  obtain ⟨pt, form, hk, hs⟩ := keys_of_hearV h hh
  obtain ⟨g'', hg'', hsh, _⟩ := toHeard_returns h g pt form hk hs (countsOk_of_shape hp)
  obtain rfl : g'' = g' := Option.some.inj (hg''.symm.trans hg)
  refine ⟨g'', s', hg, ?_, a1, a2, a3⟩
  rw [hb, ← hl, List.take_length]
  have hd' : decideVia (seatOf claim false) p s rs = .ok s' := hd
  rw [hd']
  exact quietLook_returns fs s' a1 (by rw [hsh]; exact hfs)

/-- **Behind the digits of a layers' or an attention link.** used, claims: the plan's numbers.
Conditional on the hypotheses in front, on the return of `hearV`, on one public test: the lookup's
hidden values end at the plan's number of slots; and on the first ledger's arrays having their size.
No instance of these hypotheses at this seat is exhibited in this file (at a small seat:
Honest/K3/Law/SeatedGuards.lean [not in this library], by evaluation). -/
theorem stated_yes_digits {Cl : Type} (claim : Aff → Cl) (p : P) (h : Shape) (used claims : Nat)
    (b : Block FS Cl)
    (hb : ∀ s rs gs, b.decide s rs gs =
      (decideVia (seatOf claim true) p s (rs.take p.rounds.length)).bind (quietDigits used claims))
    (s : FS) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (gs : List (List (Nat × List UInt64)))
    (hl : rs.length = p.rounds.length) (hp : p.shape = some h) (hN : 1 < h.NC)
    (hu : p.first + (faceOf h).slots = used) (hS : Sized F)
    (hF : (seatDigits claim).fork s = some F) (h0 : ((seatDigits claim).heard s).isNone = true)
    (hO : ((seatDigits claim).owed s).noneWaits = true) (hn : F.next = p.first)
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    ∃ g' s', toHeard h (toHeardG g) = some g' ∧
      decideVia (seatDigits claim) p s rs = .ok s' ∧
      b.decide s rs gs = .ok (s'.putFork { G with planClaimsF := claims }) ∧
      (seatDigits claim).heard s' = some g' ∧ s'.failed = s.failed := by
  obtain ⟨g', s', hg, hd, a1, a2, a3⟩ := digits_accepts claim p h s hp hN hF h0 hO hn hh
  refine ⟨g', s', hg, hd, ?_, a1, a3⟩
  rw [hb, ← hl, List.take_length]
  have hd' : decideVia (seatOf claim true) p s rs = .ok s' := hd
  rw [hd']
  exact quietDigits_returns used claims s' a2 (by rw [hearV_next _ hS hh, hn, hu])

#print axioms ProofFile.Honest.K3.Law.theOwn_decides
#print axioms ProofFile.Honest.K3.Law.piece_digits
#print axioms ProofFile.Honest.K3.Law.theWhole_decides
#print axioms ProofFile.Honest.K3.Law.theStated_decides
#print axioms ProofFile.Honest.K3.Law.quietLook_returns
#print axioms ProofFile.Honest.K3.Law.quietDigits_returns
#print axioms ProofFile.Honest.K3.Law.stated_yes_plain
#print axioms ProofFile.Honest.K3.Law.stated_yes_look
#print axioms ProofFile.Honest.K3.Law.stated_yes_digits

end ProofFile.Honest.K3.Law
