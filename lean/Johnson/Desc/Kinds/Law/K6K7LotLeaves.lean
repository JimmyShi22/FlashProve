-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6K7LotLeaves.lean: WHAT AN ACCEPTING DECISION OF THE SUB-PROTOCOLS THAT THE
TWO LOTS OF THE PROOF FILE's IOP MAKE FOR THE OUTPUT HEAD's OWN ROUNDS (K6) AND FOR THE NEXT TOKEN
(K7) LEAVES OF THE CHAIN's STATEMENT AND OF WHAT WAS PUT OUT. Statements and proofs.

  k6Hear_leaves    a member of P4.k6Hear Z G (Johnson/Desc/ProofFile/Lot/K6K7.lean): the statement
                   and all that was put out are as they were (Law/K6Leaves.lean: seated_leaves).
  h1Front          an accept of the guarded quiet entry is an accept of headFrontQ.
  h1Own_keeps      a member of ProofFile.h1Own G (Johnson/Desc/ProofFile/Lots/H1.lean: the quiet entry
                   into the head's link, guarded, then the next token's sub-protocol): the oracle
                   messages and the number of the index masks' message are as they were; every group
                   behind is a group in front or has no member (Law/K7Leaves.lean: place_keeps).

USER. The fields k6 and k7 of KeepShares (Johnson/P1L20R/RoomKeep.lean).
WHAT IT IS NOT. The decisions alone. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Leaves
import Johnson.Desc.Kinds.Law.K7Leaves
import Johnson.Desc.ProofFile.Lots.H1
import Johnson.Desc.Sound.SeatGuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ)

/-- **K6's lot.** -/
theorem k6Hear_leaves {Z : ProofFile.Pub} {G : ProofFile.Ground} {B : Block S ProofFile.Cl}
    (h : B ∈ P4.k6Hear Z G) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : B.decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out := by
  unfold P4.k6Hear at h
  cases hb : P4.headBefore Z G with
  | none =>
    rw [hb] at h
    cases h
  | some ms =>
    rw [hb] at h
    exact seated_leaves (Option.mem_toList.1 h) hd

/-- An accept of the guarded quiet entry is an accept of headFrontQ. -/
theorem h1Front (tl : OnBytes.Model.HTailF2) (name : String) (l : Nat)
    (a : VerifiableInference.Desc.Place) (same : S → S → Bool)
    (but : VerifiableInference.Desc.Place → Bool) :
    ∀ s rs gs s1, (Block.guarded same but
      ({ (roundlessBlock name 1 (some l) 1 (headFrontQ tl) : Block S Unit) with place := a })).decide
        s rs gs = .ok s1 → headFrontQ tl s = .ok s1 :=
  fun s rs gs s1 h => VerifiableInference.Desc.guarded_under same but _ s rs gs s1 h

/-- **K7's lot.** -/
theorem h1Own_keeps {G : ProofFile.Ground} {x : Block S Unit} (h : x ∈ ProofFile.h1Own G) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hd : x.decide s rs gs = .ok t) :
    t.st.oracles = s.st.oracles ∧ t.out.indexMasks = s.out.indexMasks ∧
      ∀ Gr ∈ t.st.groups, Gr ∈ s.st.groups ∨ Gr.members = #[] := by
  unfold ProofFile.h1Own at h
  obtain rfl := List.mem_singleton.1 h
  exact place_keeps G.W (G.built.size - 1) "H:1" _ G.W.H.tl (h1Front _ _ _ _ _ _) s rs gs t hd

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Hear_leaves
#print axioms VerifiableInference.Desc.Kinds.Head.Law.h1Own_keeps
