-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Cut.lean: NOT a law on a part or on a distribution: CONDITIONAL
where it says so: HOW A ROW IS CUT INTO MEMBERS (`membersOf`, Honest/Side.lean) where the rounds lie
as stretches, one for each part: not membership alone (Honest/Small/Members.lean) but THE ORDER, THE
STRETCH AND THE NUMBER.

  `laid`   a row's parts laid beside stretches of rounds, numbered from j: a definition
  `membersOf_flatten`   CONDITIONAL: where each part has as many moves as its stretch has rounds,
                        `membersOf row j` at the stretches laid one behind the other IS `laid row j`
                        at the stretches
  `part_of_membersOf`   a member's part is a part of the row: no premise but the membership
  `zip_map_nil`   a small lemma on lists, general in their types: a list zipped with as many empty
                  lists (of use for rounds without oracle messages)

So whoever has a sub-protocol's declared rounds as stretches, EACH AS LONG AS ITS PART HAS MOVES,
has each member of its side written out: number, rounds, part, `Sim` term: and can lay a law on one
part at that member (Honest/K6/Law/Row.lean does so).

The frame's terms that are used here (part, side, row, member and the like): the head of
Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a caller opens it.

Limits. Where a part has another number of moves than its stretch has rounds nothing is said: the
cut then runs across the stretches. `laid` drops in silence what is left of the longer of its two
lists: under the premise they are of one length. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Oracle)

variable {V W Y Pb : Type}

/-- A row's parts laid beside stretches of rounds, numbered from j. -/
def laid : List (Part V W Y × Sim Pb) → Nat → List (List (Fmt.DeclaredRound × List Oracle)) →
    List (Member V W Y Pb)
  | x :: l, j, s :: ss => ⟨j, s, x.1, x.2⟩ :: laid l (j + 1) ss
  | _, _, _ => []

/-- CONDITIONAL. **Where each part has as many moves as its stretch has rounds, the row is cut at
the stretches**: order, stretch and number. -/
theorem membersOf_flatten : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (segs : List (List (Fmt.DeclaredRound × List Oracle))),
    row.map (·.1.moves.length) = segs.map (·.length) →
    membersOf row j segs.flatten = laid row j segs
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | x :: l, j, s :: ss, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    show (⟨j, (s ++ ss.flatten).take x.1.moves.length, x.1, x.2⟩ : Member V W Y Pb) ::
      membersOf l (j + 1) ((s ++ ss.flatten).drop x.1.moves.length) = _
    rw [List.take_left' h1.symm, List.drop_left' h1.symm, membersOf_flatten l (j + 1) ss h2]
    rfl

/-- A member's part is a part of the row. -/
theorem part_of_membersOf : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (u : Member V W Y Pb), u ∈ membersOf row j rs →
    u.part ∈ row.map (·.1)
  | [], _, _, _, h => absurd h (List.not_mem_nil)
  | x :: l, j, rs, u, h => by
    show u.part ∈ x.1 :: l.map (·.1)
    rcases List.mem_cons.1 h with rfl | h'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (part_of_membersOf l (j + 1) _ u h')

/-- A list zipped with as many empty lists is the list, each member beside an empty list. -/
theorem zip_map_nil {α β : Type} (l : List α) :
    l.zip (l.map fun _ => ([] : List β)) = l.map fun d => (d, []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (a, []) :: l.zip (l.map fun _ => ([] : List β)) = (a, []) :: l.map fun d => (d, [])
    rw [ih]

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.membersOf_flatten
#print axioms ProofFile.Honest.Small.part_of_membersOf
#print axioms ProofFile.Honest.Small.zip_map_nil
