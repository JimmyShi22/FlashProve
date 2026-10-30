--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/SeatedBack.lean.
WHAT IT DOES NOT SHOW. No soundness; nothing on the plan's tests: a step does not read them.
OBJECT. Stored/HeadAddsAtS.lean's seatedClaims W l ms; Stored/HeadSeatAt.lean's blockOf W l.
WHAT IT IS. Law/SeatedSays.lean's seated_step THE OTHER WAY: for whoever has an honest run at
blockOf's block and wants it at the block as a lot seats it.
  seated_step_back  where blockOf's block's step goes on AND THE RECORD's OWN TEST ON THE REQUEST
                    SAYS YES, the seated block's goes on to the same record.
  seated_step_iff   both ways: the seated step is the other's and that test.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SeatedSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open OnBytes

theorem seated_step_back {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {bU : Block S Unit}
    (hU : blockOf W l = some bU) {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {n : Nat} (hs : bU.step ft s rs cols = .ok (s', n)) (h4 : startOk W s = true) :
    b.step ft s rs cols = .ok (s', n) := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, hi, rfl⟩ := Option.map_eq_some_iff.mp h0
  unfold blockOf at hU
  rw [hi] at hU
  obtain rfl : blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l = bU :=
    Option.some.inj hU
  have hsame : (blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l).decide =
      (kindWithJoin (K3.seatCalls asClaim) (seatAt W.hS iU3) l 4
        (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).decide := rfl
  exact step_carries
    (blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l)
    (tested (laidOk W) (startOk W) ms (kindWithJoin (K3.seatCalls asClaim) (seatAt W.hS iU3) l 4
      (parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request)))) rfl
    (fun rs gs t e => (tested_decide _ _ _ _ _ _ _ _).2 ⟨hsame ▸ e, h4⟩) hs

theorem seated_step_iff {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {bU : Block S Unit}
    (hU : blockOf W l = some bU) (ft : Nat) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (n : Nat) : b.step ft s rs cols = .ok (s', n) ↔
      bU.step ft s rs cols = .ok (s', n) ∧ startOk W s = true := by
  constructor
  · intro hs
    obtain ⟨bU', hU', hs', h4⟩ := seated_step h hs
    obtain rfl : bU = bU' := Option.some.inj (hU.symm.trans hU')
    exact ⟨hs', h4⟩
  · rintro ⟨hs, h4⟩
    exact seated_step_back h hU hs h4

end VerifiableInference.Desc.Kinds.Head.Law
