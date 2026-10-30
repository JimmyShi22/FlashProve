-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyStepLists.lean: the rounds of composed steps, as plain lists.

A step of OnBytes/Slice/KeyStep.lean holds its written rounds as a list. This file says what the
lists of the two families of steps are, in terms of ++, map and flatten and of one recursion,
`joinFrom`. So the list of a protocol that is built from steps can be compared, part by part, with a
list that is made elsewhere by recursion over the same loops, or its image under a map with the
image of such a list.

Main definitions.
 `joinFrom`   the lists f l, f (l + 1), and so on, n of them, joined.
Main theorems.
 `map_joinFrom`    a map goes inside.
 `joinFrom_of_rec` a recursion with a counter that lays one more element behind each list is a
                   `joinFrom`.
 `Step.seq_rds`, `Step.iter_rds`, `Step.iter_rds_from`, `Step.many_rds`   the rounds of one step
                   after another, of n steps in a row, and of a step for each member of a list.
Not claimed. Nothing on any one protocol.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyStep

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Run

/-- The lists f l, f (l + 1), and so on, n of them, joined. -/
def joinFrom {α : Type} (f : ℕ → List α) : ℕ → ℕ → List α
  | 0, _ => []
  | n + 1, l => f l ++ joinFrom f n (l + 1)

/-- A map over a list that is made by `joinFrom`. -/
theorem map_joinFrom {α β : Type} (g : α → β) (f : ℕ → List α) : ∀ n l,
    (joinFrom f n l).map g = joinFrom (fun i => (f i).map g) n l
  | 0, _ => rfl
  | n + 1, l => by
    show (f l ++ joinFrom f n (l + 1)).map g = (f l).map g ++ joinFrom _ n (l + 1)
    rw [List.map_append, map_joinFrom g f n (l + 1)]

/-- A recursion t on a number of turns and a counter, which in each turn lays down the list P at the
counter and then the element a, is a `joinFrom`. -/
theorem joinFrom_of_rec {α : Type} (P : ℕ → List α) (a : α) (t : ℕ → ℕ → List α)
    (h0 : ∀ l, t 0 l = []) (hs : ∀ n l, t (n + 1) l = P l ++ (a :: t n (l + 1))) : ∀ n l,
    t n l = joinFrom (fun i => P i ++ [a]) n l
  | 0, l => h0 l
  | n + 1, l => by
    show t (n + 1) l = (P l ++ [a]) ++ joinFrom _ n (l + 1)
    rw [hs, joinFrom_of_rec P a t h0 hs n (l + 1), List.append_assoc, List.singleton_append]

namespace Step

variable {X Y Z A : Type}

/-- The rounds of one step after another. -/
theorem seq_rds (S : Step X Y) (T : Step Y Z) : (S.seq T).rds = S.rds ++ T.rds := rfl

/-- The rounds of n steps in a row, where the rounds of step i are f (l + i). -/
theorem iter_rds_from (f : ℕ → List PQ.RD) : ∀ (n : ℕ) (X : ℕ → Type)
    (S : ∀ i, Step (X i) (X (i + 1))) (l : ℕ), (∀ i, (S i).rds = f (l + i)) →
    (iter n X S).rds = joinFrom f n l
  | 0, _, _, _, _ => rfl
  | n + 1, X, S, l, h => by
    show (S 0).rds ++ (iter n (fun i => X (i + 1)) fun i => S (i + 1)).rds =
      f l ++ joinFrom f n (l + 1)
    rw [h 0, iter_rds_from f n (fun i => X (i + 1)) (fun i => S (i + 1)) (l + 1) fun i => by
      rw [h (i + 1), Nat.add_right_comm, Nat.add_assoc]]
    rfl

/-- The rounds of n steps in a row. -/
theorem iter_rds (n : ℕ) (X : ℕ → Type) (S : ∀ i, Step (X i) (X (i + 1))) :
    (iter n X S).rds = joinFrom (fun i => (S i).rds) n 0 :=
  iter_rds_from (fun i => (S i).rds) n X S 0 fun i => by rw [Nat.zero_add]

/-- The rounds of a step for each member of a list. -/
theorem many_rds (S : A → Step X X) : ∀ l : List A,
    (many S l).rds = (l.map fun a => (S a).rds).flatten
  | [] => rfl
  | a :: l => by
    show (S a).rds ++ (many S l).rds = _
    rw [many_rds S l, List.map_cons, List.flatten_cons]

end Step

end OnBytes.Slice
