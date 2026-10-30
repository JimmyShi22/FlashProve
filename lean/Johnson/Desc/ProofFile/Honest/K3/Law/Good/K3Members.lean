-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Good/K3Members.lean: WHICH MEMBER OF THE LOOKUP'S SIDE IS WHICH
STAGE'S: member number j of the side is the row's own: stage number j's stretch of the
sub-protocol's declared rounds, its part, the form of a simulator beside it. On lists alone.
Theorems; no definition.

  `membersOf_spec` general in the row: a member that the frame's `membersOf` cuts is the row's entry
    at its number, with the stretch of rounds behind the moves of the entries in front
  `rowPairs_at` the lookup's row at a number: that stage's part, seated, and the form beside it
  `moves_front` the moves of the row's entries in front of stage number i are the stage's first
    round's number
  `member_k3` at the row's own side: a member's number names a stage; its rounds are that stage's
    stretch of the sub-protocol's rounds with their oracle messages; its part and form are that
    stage's

CONDITIONAL ON the side being there (`Side.seated` at the site's place and `rowPairs`); nothing
else.

Limits. It reads no coin and speaks of no play. What the stretch of rounds declares is not said
here. No instance of these hypotheses is exhibited in this file. Elsewhere:
Honest/K3/Law/Good/K3RowStatedGuards.lean [not in this library] (a test)
has ten such sides at a small made-up public part, by evaluation; and under the
head `P5J.AtMgA` a side is seated at every site, over whatever row: `seated_head`
(Honest/K3/Law/Thread/ExactKeptHead.lean).
Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3Lettered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Oracle)

variable {S Cl V W X Pb : Type}

/-- **A member that `membersOf` cuts is the row's entry at its number**, with the stretch of rounds
behind the moves of the entries in front. No premise. -/
theorem membersOf_spec : ∀ (row : List (Part V W X × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (u : Member V W X Pb), u ∈ membersOf row j rs →
    ∃ i x, row[i]? = some x ∧ u = ⟨j + i,
      (rs.drop ((row.take i).map fun y => y.1.moves.length).sum).take x.1.moves.length, x.1, x.2⟩
  | [], _, _, _, h => absurd h List.not_mem_nil
  | x :: l, j, rs, u, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨0, x, rfl, by simp⟩
    · obtain ⟨i, y, hy, rfl⟩ := membersOf_spec l (j + 1) _ u h'
      refine ⟨i + 1, y, by simpa using hy, ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_drop]
      congr 1
      omega

/-- **The lookup's row at a number**: that stage's part, seated, and the form beside it. -/
theorem rowPairs_at (A : Fill W) (s : Site) (i : Nat) (x : Part V W X × Sim Pb)
    (h : (rowPairs A s)[i]? = some x) :
    ∃ st, (stages s.at_.face)[i]? = some st ∧
      x.1 = (partOf (V := Unit) theReads (A.jobs s).asked s.at_ st i).lift (fun _ => ()) (A.wit s)
        (fun _ => ()) (fun y _ => y) ∧ x.2 = simOf s.at_ st i := by
  unfold rowPairs lookPairs proverSideOfLookupInChainAtOneOwner lookRow lookSims at h
  simp only [List.getElem?_zip_eq_some, List.getElem?_map, Option.map_eq_some_iff,
    List.getElem?_zipIdx, Nat.zero_add] at h
  obtain ⟨⟨p, ⟨y, ⟨st, hst, rfl⟩, rfl⟩, h1⟩, ⟨y', ⟨st', hst', rfl⟩, h2⟩⟩ := h
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst')
  exact ⟨st, hst, h1.symm, h2.symm⟩

/-- The moves of the row's entries in front of stage number i: the number of the stage's first
round. -/
theorem moves_front (A : Fill W) (s : Site) (i : Nat) (st : Stage)
    (h : (stages s.at_.face)[i]? = some st) :
    (((rowPairs (V := V) (X := X) (Pb := Pb) A s).take i).map fun y => y.1.moves.length).sum =
      firstRound s.at_.face st := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [firstRound_getElem s.at_.face i hi, List.map_take, List.map_take]
  have e : ((rowPairs (V := V) (X := X) (Pb := Pb) A s).map fun y => y.1.moves.length) =
      (stages s.at_.face).map (Stage.rounds s.at_.face) := by
    rw [← proverSideOfLookupInChainAtOneOwner_moves (V₁ := V) (X₁ := X) theReads (A.jobs s).asked (A.wit s) s.at_,
      ← rowPairs_parts (Pb := Pb) A s, List.map_map]
    rfl
  rw [e]

/-- **At the row's own side a member is its stage's.** Conditional on the side being there. -/
theorem member_k3 (A : Fill W) (s : Site) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl V W X Pb) (h : Side.seated bs s.at_.place (rowPairs A s) fs = some σ)
    (u : Member V W X Pb) (hu : u ∈ σ.members) :
    ∃ st, (stages s.at_.face)[u.number]? = some st ∧
      u.rounds = ((σ.block.rounds.zip σ.block.oracles).drop (firstRound s.at_.face st)).take
        (Stage.rounds s.at_.face st) ∧
      u.part = (partOf (V := Unit) theReads (A.jobs s).asked s.at_ st u.number).lift (fun _ => ())
        (A.wit s) (fun _ => ()) (fun y _ => y) ∧ u.sim = simOf s.at_ st u.number := by
  have hrow : σ.row = rowPairs A s := by
    unfold Side.seated at h
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  unfold Side.members at hu
  rw [hrow] at hu
  obtain ⟨i, x, hx, rfl⟩ := membersOf_spec _ 0 _ u hu
  obtain ⟨st, hst, h1, h2⟩ := rowPairs_at A s i x hx
  refine ⟨st, by simpa using hst, ?_, by simpa using h1, by simpa using h2⟩
  show ((σ.block.rounds.zip σ.block.oracles).drop _).take x.1.moves.length = _
  rw [moves_front A s i st hst, h1]
  congr 1
  rw [← partOf_moves (V := Unit) theReads (A.jobs s).asked s.at_ st i]
  simp [Part.lift]

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.membersOf_spec
#print axioms ProofFile.Honest.K3.Law.rowPairs_at
#print axioms ProofFile.Honest.K3.Law.moves_front
#print axioms ProofFile.Honest.K3.Law.member_k3
