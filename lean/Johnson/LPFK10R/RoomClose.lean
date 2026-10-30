-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/RoomClose.lean: ONE SHARE OF THE KEEPING BENEATH room_at_reach: THE FIELD close OF KeepShares (Johnson/P1L20R/RoomKeep.lean), TO THE LETTER, FROM ONE NAMED PREMISE. A definition, statements and proofs.
THE FIELD: at each of the 25 links, each of the three sub-protocols that close it (K9.closeOf p Q = the one equation · K10's closing · "the segment is shut") hands on, from a reached state at which the index masks' message is a member of no group: "its ledger is not closed and has n entries left", and "it is a member of no group".
  OwnIn c start   THE PREMISE: at every state that is reached in front of a link's one equation (number 14 l + nA l + 4), every one of the link's own messages (L.check.frame.own) is a member of some group of the statement.
  hands2_of       from the two ends in plain terms (the ledger as it was; still a member of no group) to P1L20.Hands2.
  room_close      OwnIn c start gives the field's statement, at every Z.
BY: j = 0: oneEquation_ledger (Johnson/Desc/First/Close/Law/EqLedger.lean): THE ONE PLACE WHERE OwnIn AND "reached" ARE SPENT: the one equation takes its mask entries out of the ledger of one of the link's own messages · j = 1: closing_ledger (LedgerBehind.lean, beside it): no "reached" · j = 2: shut_same (there) with
hands2_same.
LIMITS. **OwnIn IS A PREMISE: SHOWN OF NO CHAIN HERE.** By report (its files are not imported here and were not compiled with this file) members_at has "G.members = pre ++ keptBefore ++ own" at the reached cuts of every link l < 24;
the head's link (l = 24): members_head (Johnson/IMR/HeadMembers.lean) has "G.members = #[n₀] ++
keptBefore ++ own" at the reached cuts 340 + n, n ≤ 10 (of a fold that returns): in scope, the files
read, at an opening, at OnBytes.secondHashFunction.
One field of
thirteen. No soundness statement.

-/
import Johnson.P1L20R.RoomKeep
import Johnson.Desc.First.Close.Law.LedgerBehind
import Johnson.Desc.First.Close.Law.EqLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK10

open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par closing_ledger shut_same oneEquation_ledger)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P1L20 (KeepsAt Hands2 nA outOfGroupsB outOfGroupsB_iff leftIsB_of_ledger hands2_same)

/-- **What is owed at the reached states in front of a link's one equation**: every one of the link's own messages is a member of some group of the statement. -/
def OwnIn {Q : Type} (c : Chain S Cl) (start : Q → S) : Prop :=
  ∀ l < 25, ∀ z s, Reach 0 c.blocksInOrder start (14 * l + nA l + 4) (z, s) → ∀ L, s.link? = some L →
    ∀ o ∈ L.check.frame.own, ∃ G ∈ s.st.groups, o ∈ G.members

/-- From the two ends in plain terms to what is handed on. -/
theorem hands2_of {s s' : S}
    (h1 : (s'.st.oracles[s'.out.indexMasks]?).bind (·.ledger) =
      (s.st.oracles[s.out.indexMasks]?).bind (·.ledger))
    (h2 : ∀ G ∈ s'.st.groups, s'.out.indexMasks ∉ G.members) : Hands2 s s' :=
  fun n hn => ⟨by rw [leftIsB_of_ledger (s := s) (s' := s') h1]; exact hn, outOfGroupsB_iff.2 h2⟩

/-- **THE FIELD close OF KeepShares, TO THE LETTER, FROM OwnIn.** -/
theorem room_close {Q : Type} (Z : ProofFile.Pub) (c : Chain S Cl) (start : Q → S)
    (H : OwnIn c start) :
    ∀ l < 25, ∀ p Q j (x : Block S Unit), IM.k9At Z l = some p →
      ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q →
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x →
      KeepsAt c start (14 * l + nA l + 4 + j) (x.retype : Block S Cl) := by
  intro l hl p Q j x _ _ hx z s s' hr hy hout
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  have ho := outOfGroupsB_iff.1 hout
  rcases j with _ | _ | _ | j
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨a1, a2, -⟩ := oneEquation_ledger (Cl := Unit) p s s' rs gs e ho (H l hl z s hr)
    exact hands2_of a1 a2
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨a1, a2, -⟩ := closing_ledger (Cl := Unit) Q s s' rs gs e ho
    exact hands2_of a1 a2
  · obtain rfl : _ = x := Option.some.inj hx
    obtain ⟨e1, e2⟩ := shut_same (Cl := Unit) p (Q.piece + 1) s s' rs gs e
    exact hands2_same (ledger_same e1 e2) (by rw [e1]) (by rw [e2]) hout
  · cases hx

end LPFK10

#print axioms LPFK10.hands2_of
#print axioms LPFK10.room_close
