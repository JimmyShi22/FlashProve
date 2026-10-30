-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerTiesJoin.lean: the proof of the statement `TiesJoinOwed`
(Johnson/Desc/K14/Law/LedgerTiesJoinOwed.lean): in scope, where the value is laid and the row's data
are the second chain's, the five ties that kind K14's law at the cap asks hold at the written list
of the full proof file: round 0's entry and kind, and `Ties` at the pieces number 2, 4, 5 and 7. One
theorem: calls alone.
  tiesJoin   `takeOfRow` (the first seven rounds of the row's data are the pieces' own) and
             `tiesAtScope` (they bear the written rounds' entries and kinds), both of
             Johnson/Desc/K14/Law/LedgerTies.lean, CALLED. `atW`
             (Johnson/Goal/Numbers/K14RoundsAt.lean)
             is `writtenAt` by unfolding. Of `Ties`' four clauses (K14OwnAt.lean) one speaks at each
             number; the other three ask another number and are idle.
What is not claimed. That a row's data are the second chain's, or that three pieces have no data.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerTiesJoinOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- **The five ties that the law at the cap asks.** -/
theorem tiesJoin : TiesJoinOwed := by
  intro o Z D r hS hL C Fr S Cl W f pt x2 x3 x4 x5 x6 x7 rest d d21 d22 d4 d51 d52 d7 hrow hf h1
    h2 h3 h4 h5 h6 h7
  have ht := takeOfRow C Fr S Cl W f pt x2 x3 x4 x5 x6 x7 rest d d21 d22 d4 d51 d52 d7 hf h1 h2
    h3 h4 h5 h6 h7
  rw [hrow] at ht
  obtain ⟨a0, a1, a3, a4, a6⟩ := tiesAtScope o Z D r hS hL d d21 d22 d4 d51 d52 d7 ht
  refine ⟨a0, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro e₁ e₂ _ h
    cases h
    exact a1
  · exact fun _ hk _ => absurd hk (by decide)
  · exact fun _ _ hk _ => absurd hk (by decide)
  · exact fun _ hk _ => absurd hk (by decide)
  · exact fun _ _ hk _ => absurd hk (by decide)
  · intro e _ h
    cases h
    exact a3
  · exact fun _ _ hk _ => absurd hk (by decide)
  · exact fun _ hk _ => absurd hk (by decide)
  · exact fun _ _ hk _ => absurd hk (by decide)
  · exact fun _ hk _ => absurd hk (by decide)
  · intro e₁ e₂ _ h
    cases h
    exact a4
  · exact fun _ hk _ => absurd hk (by decide)
  · exact fun _ _ hk _ => absurd hk (by decide)
  · exact fun _ hk _ => absurd hk (by decide)
  · exact fun _ _ hk _ => absurd hk (by decide)
  · intro e _ h
    cases h
    exact a6

end Desc.K14.Law

#print axioms Desc.K14.Law.tiesJoin
