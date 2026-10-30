-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/RoomAcross.lean:
ONE SHARE OF THE KEEPING BENEATH room_at_reach: THE FIELD k12 OF
KeepShares (Johnson/P1L20R/RoomKeep.lean): the proximity test's sub-protocol on the
proof file's first chain, which a lot of the seat makes at the place ⟨1, none, 2, K12⟩, hands on
from the state in front to the state behind an accepting step: the ledger of the message that the
state names as out.indexMasks is not closed and has n entries left, at every n; and that message is
a member of no group.

  atFinish_hands    an accepting decision of atFinish p, at every p: from "member of no group" in
                    front: Hands2. By atFinish_room (Johnson/Desc/K12/Law/RoomAcross.lean). THE TEST
                    IS NO KEEPER OF THE STATEMENT (a group comes for each code switch inside it, and
                    the group under test is marked): so hands2_same does not serve here.
  k12_keeps         THE FIELD, at every Z, G, c and start: no scope is asked; neither "chain 1" nor
                    "reached" is spent. The lot's one member by lot_of_kind and blocks_mem
                    (Johnson/IMR/LotKinds.lean).

Limits. One field of thirteen. A law from an accept: no example of an accepting step is shown. It
does not say that the ledger is open, or that the message is a member of no group, at any state. No
soundness statement. Nothing on hiding.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.IMR.LotKinds
import Johnson.Desc.K12.Law.RoomAcross

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- As RoomKeep.lean and RoomKeepK8.lean have it: the instance of the reference scales,
-- which Lean would else fill in silently (Inst/Model/ScalesGuard.lean), is struck.
attribute [-instance] Inst.Model.Scl.ref

namespace H2K12

open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- An accepting decision of the test at the first chain's finish hands both clauses on. -/
theorem atFinish_hands (p : VerifiableInference.Desc.K12.P12) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K12.atFinish p).decide s rs gs = .ok s')
    (hout : P1L20.outOfGroupsB s = true) : P1L20.Hands2 s s' := by
  intro n hn
  have ha : H2K.Out.Apart s.st s.out.indexMasks := P1L20.outOfGroupsB_iff.1 hout
  have ho : s.out.indexMasks < s.st.oracles.size := by
    by_contra hc
    unfold Johnson.Desc.First.Walk.Tied.leftIsB Johnson.Desc.First.Walk.Law.ledgerAt at hn
    rw [Array.getElem?_eq_none (by omega)] at hn
    cases hn
  obtain ⟨_, e2, e3⟩ := H2K.Out.atFinish_room p h ho ha
  refine ⟨?_, P1L20.outOfGroupsB_iff.2 e3⟩
  rw [P1L20.leftIsB_of_ledger (s := s) e2]
  exact hn

/-- **THE FIELD k12 OF KeepShares.** -/
theorem k12_keeps {Q : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (c : VerifiableInference.Desc.Chain S Cl) (start : Q → S) :
    P1L20.LotKeeps Z G₀ c start KindName.K12 := by
  rintro b' ⟨L, hL, hb⟩ _ hk z s s' _ hy hout
  obtain rfl : L = VerifiableInference.Desc.K12.lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  obtain ⟨x, hx, rfl⟩ : ∃ x ∈ (VerifiableInference.Desc.K12.lot Z).own G₀, b' = x.retype := by
    rcases IM.blocks_mem hb with h | h
    · exact h
    · exact absurd h List.not_mem_nil
  obtain rfl := List.mem_singleton.1 hx
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  exact atFinish_hands _ e hout

end H2K12

#print axioms H2K12.atFinish_hands
#print axioms H2K12.k12_keeps
