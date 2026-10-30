-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SeatedBridge.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing on what the lot lays as "before". A harness's seat.
LETTERS. seatedOf_some | seatedClaims_some: under "there is": b0: pinned by blockOf W l = some b0
(or blockClaims) and b = tested (laidOk W) (startOk W) before b0.
OBJECT. THE SEATED CONSTANT IS seatedOf | seatedClaims: a row's line on its object names it and
reaches blockOf | blockClaims by one rewrite with these lemmas.
WHAT IT IS. THE BRIDGE FROM THE BLOCK THAT A LOT SEATS (Stored/HeadSeatAt.lean: seatedOf; Stored/
HeadAddsAtS.lean: seatedClaims) TO THE BLOCK THAT OUR LAWS SPEAK OF (blockOf; blockClaims): the two
have one name, place, table of rounds, oracles and runs, BY rfl; THE SEATED ONE's DECISION GOES ON
JUST WHERE THE OTHER's DOES AND THE RECORD's OWN TEST ON THE REQUEST SAYS YES; the seated one's test
on the plan is the other's AND HeadLaid.lean's; its "before" is the lot's list.
  tested_name, tested_place, tested_rounds, tested_oracles, tested_claims, tested_after,
  tested_planOk, tested_before   field by field.
  tested_decide     the decision: an "if and only if" with the test on the record in front.
  tested_decide_of  where that test says yes the two decisions are one.
  seatedOf_some, seatedClaims_some   where the seated block is there.
  seatedOf_plan, seatedClaims_plan   where the seated block's test on the plan says yes: Par.ok at
                    the seat's parameters AND laidOk W: both halves, by name.
  seatedOf_before, seatedClaims_before   its "before" is the lot's list.
  seated_plan       the same of tested, at letters.

-/
import Mathlib
import Johnson.Stored.HeadAddsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open OnBytes

variable {Cl : Type} (ok : Bool) (start : S → Bool) (before : List (Nat × Nat)) (b : Block S Cl)

theorem tested_name : (tested ok start before b).name = b.name := rfl
theorem tested_place : (tested ok start before b).place = b.place := rfl
theorem tested_rounds : (tested ok start before b).rounds = b.rounds := rfl
theorem tested_oracles : (tested ok start before b).oracles = b.oracles := rfl
theorem tested_claims : (tested ok start before b).claims = b.claims := rfl
theorem tested_after : (tested ok start before b).after = b.after := rfl
theorem tested_planOk : (tested ok start before b).planOk = (b.planOk && ok) := rfl
theorem tested_before : (tested ok start before b).before = before := rfl

/-- Where the test on the record says yes the two decisions are one. -/
theorem tested_decide_of {s : S} (hs : start s = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (tested ok start before b).decide s rs gs = b.decide s rs gs := by
  show (if start s then b.decide s rs gs else _) = _
  rw [hs, if_pos rfl]

/-- **The seated decision goes on just where the block's own does and the test says yes.** -/
theorem tested_decide (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (tested ok start before b).decide s rs gs = .ok s' ↔
      b.decide s rs gs = .ok s' ∧ start s = true := by
  constructor
  · intro h
    have h' : (if start s then b.decide s rs gs
      else Except.error "the request: rows and tokens") = .ok s' := h
    cases hs : start s with
    | true => rw [hs, if_pos rfl] at h'; exact ⟨h', rfl⟩
    | false => rw [hs] at h'; cases h'
  · rintro ⟨h, hs⟩
    rw [tested_decide_of ok start before b hs]
    exact h

theorem seatedOf_some {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Unit} (h : seatedOf W l ms = some b) :
    ∃ b0, blockOf W l = some b0 ∧ b = tested (laidOk W) (startOk W) ms b0 := by
  unfold seatedOf at h
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b0, h0, rfl⟩

theorem seatedClaims_some {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) :
    ∃ b0, blockClaims W l = some b0 ∧ b = tested (laidOk W) (startOk W) ms b0 := by
  unfold seatedClaims at h
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨b0, h0, rfl⟩

/-- **WHERE THE SEATED BLOCK's TEST ON THE PLAN SAYS YES: BOTH HALVES, BY NAME**: the kind's own
tests on the plan (HeadFrame.lean: Par.ok, at the seat's parameters) and HeadLaid.lean's. -/
theorem seatedOf_plan {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Unit} (h : seatedOf W l ms = some b) (hp : b.planOk = true) :
    (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request)).ok = true ∧
      laidOk W = true := by
  obtain ⟨b0, h0, rfl⟩ := seatedOf_some h
  rw [tested_planOk, Bool.and_eq_true] at hp
  unfold blockOf at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  exact hp

theorem seatedClaims_plan {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true) :
    (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request)).ok = true ∧
      laidOk W = true := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  rw [tested_planOk, Bool.and_eq_true] at hp
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  exact hp

/-- And its "before" is the lot's list. -/
theorem seatedOf_before {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Unit} (h : seatedOf W l ms = some b) : b.before = ms := by
  obtain ⟨b0, _, rfl⟩ := seatedOf_some h
  rfl

theorem seatedClaims_before {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) : b.before = ms := by
  obtain ⟨b0, _, rfl⟩ := seatedClaims_some h
  rfl

theorem seated_plan {ok : Bool} {start : S → Bool} {before : List (Nat × Nat)} {b : Block S Cl}
    (h : (tested ok start before b).planOk = true) : b.planOk = true ∧ ok = true := by
  rw [tested_planOk, Bool.and_eq_true] at h
  exact h

end VerifiableInference.Desc.Kinds.Head.Law
