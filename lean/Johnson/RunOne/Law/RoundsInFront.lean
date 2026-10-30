-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RoundsInFront.lean: THE DECLARED ROUNDS OF A CHAIN's FIRST n BLOCKS, IN A ROW, ARE THE FRONT OF THE CHAIN's DECLARED ROUNDS: a fact on lists, and its forms at a description's three chains. Statements with proofs.
OBJECT. `FileDescription.roundsDeclaredByBlocks` (Johnson/Desc/Block.lean): a chain's flat list of blocks, each block's declared rounds, in a row.
USER. Whoever must part a chain's declared rounds at a block: pre ++ (the block's ++ post). Wanted for two things: for "the place's first free own number is the number of roots declared in front" at a proximity test, and for "the trees told in front of a sending".
LETTERS. All free. No premise, but "the n-th block is b" where a block is named.

  flatMap_take, flatMap_drop: for every list l, function f into lists and number n: (l.take n).flatMap f is the front of l.flatMap f, as long as the first n members' lists together; (l.drop n).flatMap f is what is left behind it.
  inFront bs n: how many rounds the first n blocks declare.
  rounds_take, rounds_drop: the two at a list of blocks and their declared rounds.
  rounds_part: where the n-th block is b: the declared rounds in a row are pre ++ (b.rounds ++ post), pre := the first n blocks', post := those behind b; pre.length = inFront bs n.
  decl₁_take, decl₂_take, decl₃_take: rounds_take at a description's three chains.
Limits. On what a round declares nothing. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RoundsInFront
open VerifiableInference.Desc

theorem flatMap_take {α β : Type} (f : α → List β) : ∀ (l : List α) (n : Nat),
    (l.take n).flatMap f = (l.flatMap f).take ((l.take n).map fun a => (f a).length).sum
  | [], n => by simp
  | _ :: _, 0 => by simp
  | a :: l, n + 1 => by
    simp only [List.take_succ_cons, List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [List.take_length_add_append, flatMap_take f l n]

theorem flatMap_drop {α β : Type} (f : α → List β) : ∀ (l : List α) (n : Nat),
    (l.drop n).flatMap f = (l.flatMap f).drop ((l.take n).map fun a => (f a).length).sum
  | [], n => by simp
  | _ :: _, 0 => by simp
  | a :: l, n + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [List.drop_length_add_append, flatMap_drop f l n]

variable {S Cl : Type}

/-- How many rounds the first n blocks declare. -/
def inFront (bs : List (Block S Cl)) (n : Nat) : Nat := ((bs.take n).map fun b => b.rounds.length).sum

theorem rounds_take (bs : List (Block S Cl)) (n : Nat) :
    (bs.take n).flatMap (·.rounds) = (bs.flatMap (·.rounds)).take (inFront bs n) :=
  flatMap_take (·.rounds) bs n

theorem rounds_drop (bs : List (Block S Cl)) (n : Nat) :
    (bs.drop n).flatMap (·.rounds) = (bs.flatMap (·.rounds)).drop (inFront bs n) :=
  flatMap_drop (·.rounds) bs n

theorem length_inFront (bs : List (Block S Cl)) (n : Nat) :
    ((bs.take n).flatMap (·.rounds)).length = inFront bs n := by
  simp [inFront, List.length_flatMap]

/-- **The parting at the n-th block.** -/
theorem rounds_part (bs : List (Block S Cl)) (n : Nat) (b : Block S Cl) (h : bs[n]? = some b) :
    bs.flatMap (·.rounds) =
      (bs.take n).flatMap (·.rounds) ++ (b.rounds ++ (bs.drop (n + 1)).flatMap (·.rounds)) := by
  have hn : n < bs.length := (List.getElem?_eq_some_iff.1 h).1
  have hb : bs[n] = b := (List.getElem?_eq_some_iff.1 h).2
  have e : bs = bs.take n ++ b :: bs.drop (n + 1) := by
    rw [← hb, ← List.drop_eq_getElem_cons hn, List.take_append_drop]
  conv => lhs; rw [e]
  rw [List.flatMap_append, List.flatMap_cons]

variable {Xi : Type} (F : FileDescription Xi)

theorem decl₁_take (n : Nat) :
    (F.first.blocksInOrder.take n).flatMap (·.rounds) = F.roundsDeclaredByBlocks.1.take (inFront F.first.blocksInOrder n) :=
  rounds_take F.first.blocksInOrder n

theorem decl₂_take (n : Nat) :
    (F.shared.blocksInOrder.take n).flatMap (·.rounds) = F.roundsDeclaredByBlocks.2.1.take (inFront F.shared.blocksInOrder n) :=
  rounds_take F.shared.blocksInOrder n

theorem decl₃_take (n : Nat) :
    (F.second.blocksInOrder.take n).flatMap (·.rounds) = F.roundsDeclaredByBlocks.2.2.take (inFront F.second.blocksInOrder n) :=
  rounds_take F.second.blocksInOrder n

end Johnson.RunOne.Law.RoundsInFront

#print axioms Johnson.RunOne.Law.RoundsInFront.flatMap_take
#print axioms Johnson.RunOne.Law.RoundsInFront.flatMap_drop
#print axioms Johnson.RunOne.Law.RoundsInFront.rounds_take
#print axioms Johnson.RunOne.Law.RoundsInFront.rounds_drop
#print axioms Johnson.RunOne.Law.RoundsInFront.length_inFront
#print axioms Johnson.RunOne.Law.RoundsInFront.rounds_part
#print axioms Johnson.RunOne.Law.RoundsInFront.decl₁_take
#print axioms Johnson.RunOne.Law.RoundsInFront.decl₂_take
#print axioms Johnson.RunOne.Law.RoundsInFront.decl₃_take
