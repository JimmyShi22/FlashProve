-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Leaves.lean: what the block of an attention segment's own rounds owes as
a block that stands in front of the smallness test's draw.

The law by which the block of the draw is shown to say yes
(Johnson/Desc/First/K8/LawReadyAtt.lean) asks of every block in front of it that it has left five
fields of the smallness test's part of the verifier's state, has left the mark "the list of tables
is closed", and has left no count of rows waiting where none waited
(`LeavesFront`, Johnson/Desc/First/K8/LawReadyRow.lean). That is enough for the law, not needed for
the yes: the block of the draw itself tests the state in front of it and reads nothing of the blocks
in front. This file shows it of the attention segment's block in its three forms.

Main names:
  `leavesFront_of_tl_waits`: any block whose decision leaves the smallness test's part (`S.tl?`)
    and behind whose yes no count waits pays `LeavesFront`.
  `leavesFront_k5`: the block `attentionKind seatSO claims p`, for every list of runs of claims and every
    setting p.
  `leavesFront_k5AtN`: the block that `k5AtN` returns, where it returns one.
  `leavesFront_lotN`: every block of the lot `H2K5.lotN`.
  `leavesFront_under_lotN`: every block, with whatever type of claims, whose yes is the same yes of
    a block of the lot (`Block.Under`): so the lot's block as a chain holds it, wrapped or guarded.

Why not by `leavesFront_of_tl`: that lemma asks that the count of rows that is owed is as it was.
This block's decision lays "nothing is owed", also where "0 rows are owed" stood in front, so the
field may turn. What `LeavesFront` itself asks, that no count waits behind, holds behind every yes.

Limits. All five speak of the decision alone, and only where it says yes: where it refuses they
say nothing, and that it ever says yes is not shown here. The verifier's chain holds the lot's block
wrapped and behind a guard. `LeavesFront` goes over to such a block by `LeavesFront.under` or
`LeavesFront.guards` (Johnson/Desc/First/K8/LawReadyText.lean); the first is called in
`leavesFront_under_lotN`. That the chain's member stands under the lot's block is its premise u and
is not shown here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K8.LawReadyText
import Johnson.Desc.First.Att.K05Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready (LeavesFront keep closedAt)
open VerifiableInference.Desc.First.Att.P

/-- A block whose decision leaves the smallness test's part of the state, and behind whose yes no
count of rows waits, pays what a block in front of the draw owes. Conditional on both premises;
whoever calls it for a block pays them from that block's text. -/
theorem leavesFront_of_tl_waits {Cl : Type} (b : Block S Cl) (h1 : b.Leaves S.tl?)
    (h2 : ∀ s rs gs s', b.decide s rs gs = .ok s' → s'.noneWaits = true) : LeavesFront b := by
  refine ⟨fun s rs gs s' h => ?_, fun s rs gs s' h => ?_, fun s rs gs s' h _ => h2 s rs gs s' h⟩
  · unfold keep
    rw [h1 s rs gs s' h]
  · unfold closedAt
    rw [h1 s rs gs s' h]

/-- **The block of an attention segment's own rounds pays what a block in front of the draw
owes**, for every list of runs of claims and every setting. It says something only where the
block's decision says yes. -/
theorem leavesFront_k5 {Cl : Type}
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) :
    LeavesFront (attentionKind seatSO claims p) :=
  leavesFront_of_tl_waits _ (k5_leaves_tl claims p)
    (fun _ _ _ _ h => k5_none_waits claims p h)

/-- The same of the block that `k5AtN` returns, conditional on its returning one. -/
theorem leavesFront_k5AtN {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)}
    {b' : Block S Claim} (hb : k5AtN W l g before = some b') : LeavesFront b' := by
  refine leavesFront_of_tl_waits _ (k5AtN_leaves_tl hb) ?_
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun _ _ gs _ h => k5_none_waits (gs := gs) (runsN p) _ h

/-- The same of every block of the lot of the attention segments' own rounds. -/
theorem leavesFront_lotN {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block S ProofFile.Cl}
    (h : b₁ ∈ (H2K5.lotN Z).blocks G) : LeavesFront b₁ := by
  refine leavesFront_of_tl_waits _ (lotN_leaves_tl h) ?_
  have h' : b₁ ∈ H2K5.k5OwnN Z G := by simpa [ProofFile.Lot.blocks, H2K5.lotN, ProofFile.asCl] using h
  unfold H2K5.k5OwnN at h'
  obtain ⟨x, _, e⟩ := List.mem_filterMap.1 h'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact fun _ _ gs _ hd => k5_none_waits (gs := gs) (runsN p) _ hd

/-- The same of every block whose yes is the same yes of a block of the lot, whatever its type of
claims. Conditional on u; whoever lays the lot's block into a chain pays it. -/
theorem leavesFront_under_lotN {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block S ProofFile.Cl}
    (h : b₁ ∈ (H2K5.lotN Z).blocks G) {Cl' : Type} {c : Block S Cl'} (u : c.Under b₁) :
    LeavesFront c :=
  (leavesFront_lotN h).under u

end H2K5.Honest

#print axioms H2K5.Honest.leavesFront_of_tl_waits
#print axioms H2K5.Honest.leavesFront_k5
#print axioms H2K5.Honest.leavesFront_k5AtN
#print axioms H2K5.Honest.leavesFront_lotN
#print axioms H2K5.Honest.leavesFront_under_lotN
