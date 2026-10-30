-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MemberAtSite.lean: the description's own member at a lookup's
place: what it has of the sub-protocol that the lookups' lot supplies there. A statement and its
proof, with one lemma.

Terms. Honest/K3/GLOSSARY.md ("address", "description", "lot", "member", "step", "sub-protocol").

What is shown.
  `k3_alone`: a lookup's address is a place at which nothing is laid behind the lot's sub-protocol
    (`AlonePlace`, Honest/Member/Statement.lean: its second case: another kind than K9 and K10, a
    piece from 2 to 9): the lookups stand at the pieces 2 and 7, at the head 3 and 8.
  `MemberAtSite`, `memberAtSite`: the statement and its proof.

Hypotheses that remain. Inside the statement `MemberAtSite`: the description returns (`IM.Open`); b
is one of the lot's sub-protocols; a member m of the first chain's flat list stands at its place.
`hx`: (in `k3_alone`) the address is one of the lot's list.

How the proof goes. It rests on `member_alone` and `alone_gives` (Honest/Member/AtLot.lean: from the
member of the flat list to "a sub-protocol of a lot at that place", and what the wrapping keeps) and
on `lot_block_at` and `reads_none` (Honest/K3/Law/LotMember.lean: from "a sub-protocol of the
lookups' lot" to the address, the parameters and the rounds).

Imported. The files under Honest/Member/.

Users. This file is imported by Honest/K3/Law/LotOfSite.lean, Honest/K3/Law/MemberYes.lean,
Honest/K3/Law/PlanOkGives.lean and Honest/K3/Law/Thread/SeatedTerm.lean [not in this library].

Limits. It says what the member has of the lot's sub-protocol; that the step of the lot's
sub-protocol accepts on played rounds is shown, conditionally, in other files
(Honest/K3/Law/Stated.lean: the decision, where the hearing returns; Honest/K3/Law/StepYes.lean:
from the decision to the step, under the five hypotheses of `step_iff_decide`). No instance of these
hypotheses is exhibited in this file: that the description returns at three public files, and has
ten such members, is seen by evaluation (the lines of Honest/K3/LotSheet.lean at the shipped small
example; in a run whose print is not in the library).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LotMember
import Johnson.Desc.ProofFile.Honest.Member.AtLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain FileDescription KindName Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.AtPlace (AlonePlace member_alone alone_gives)

/-- A lookup's address is a place at which nothing is laid behind the lot's sub-protocol. -/
theorem k3_alone (Z : Pub) (x : Nat × Bool × Place) (hx : x ∈ K3Lot.addresses Z) :
    x.2.2.kind = KindName.K3 ∧ AlonePlace Z x.2.2 := by
  unfold K3Lot.addresses at hx
  obtain ⟨i, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨d, _, rfl⟩ := List.mem_map.1 hx
  refine ⟨rfl, Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)⟩
  · show KindName.K3 ≠ KindName.K9
    decide
  · show KindName.K3 ≠ KindName.K10
    decide
  · show 2 ≤ VerifiableInference.Desc.K3.pieceAt Z.p.X i d
    unfold VerifiableInference.Desc.K3.pieceAt
    split <;> split <;> decide
  · show VerifiableInference.Desc.K3.pieceAt Z.p.X i d ≤ 9
    unfold VerifiableInference.Desc.K3.pieceAt
    split <;> split <;> decide

/-- **The description's own member at a lookup's place.** Wherever the proof file's description
returns (opened: `IM.Open`): for every sub-protocol b of the lookups' lot and every member m of the
first chain's flat list at b's place: b stands at an address x of the lot's list and bears it as its
place; m has b's rounds, which are those of the verifier's own parameters at the address
(`FromPlace`), and b's oracle messages; nothing is read in m's rounds, and the columns are filled:
none; and m's step accepts with a state and a number of columns just where b's step accepts with
them, the state bears no mark of failure and holds the reply that stood in front. (By the second
case of `AlonePlace`: no hypothesis on the head's link is needed.) A lemma's statement, none of the
library's goals. -/
def MemberAtSite : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ b ∈ (K3Lot.lot Z).blocks Bs.G₀, ∀ m ∈ c.blocksInOrder, m.place = b.place →
    (∃ x ∈ K3Lot.addresses Z, m.place = x.2.2 ∧ FromPlace Z.p.X x.2.2 m) ∧
    m.rounds = b.rounds ∧ m.oracles = b.oracles ∧
    (∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
      (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) (back : List OpenedColumn),
      fillCols (readsOf chain ft stored tree m.rounds ds) back = .ok []) ∧
    ∀ (ft : Nat) (t t' : S) (k : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
      m.step ft t rs cols = .ok (t', k) ↔
        b.step ft t rs cols = .ok (t', k) ∧ t'.failed = none ∧ sameReply t t' = true

/-- **The proof of `MemberAtSite`.** -/
theorem memberAtSite : MemberAtSite := by
  intro o pol lay KL F Z Bs base c A B O b hb m hm hp
  obtain ⟨x, hx, hbx, i, d, p, h1, h2, h3, h4⟩ := lot_block_at Z Bs.G₀ b hb
  obtain ⟨hk, hal⟩ := k3_alone Z x hx
  have hL : K3Lot.lot Z ∈ onlineFirstChainBlockTables Z := by simp [onlineFirstChainBlockTables]
  obtain ⟨y, hy, hlaid⟩ := member_alone o pol lay KL F Z Bs base c A B O (K3Lot.lot Z) hL b hb
    (by rw [hbx, hk]; decide) (by rw [hbx]; exact hal) m hm hp
  obtain ⟨_, _, g3, g4, _, _, g7⟩ := alone_gives sameReply y m b m.name b.place hy hlaid
  refine ⟨⟨x, hx, hp.trans hbx, i, d, p, h1, h2, h3, g3.trans h4⟩, g3, g4, ?_, ?_⟩
  · intro chain ft stored tree ds back
    rw [g3, h4]
    have e : readsOf chain ft stored tree p.rounds ds = [] := reads_none chain ft stored tree _ ds
    rw [e]
    rfl
  · intro ft t t' k rs cols
    rw [g7 ft t t' k rs cols]
    have hne : b.place.kind ≠ KindName.K7 := by rw [hbx, hk]; decide
    constructor
    · rintro ⟨a1, a2, a3⟩
      exact ⟨a1, a2, a3.resolve_left hne⟩
    · rintro ⟨a1, a2, a3⟩
      exact ⟨a1, a2, Or.inr a3⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.k3_alone
#print axioms ProofFile.Honest.K3.Law.memberAtSite
