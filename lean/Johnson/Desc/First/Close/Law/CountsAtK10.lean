-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CountsAtK10.lean: K10's BLOCK TELLS OF NO TREE: SO THE PLAN's TWO
COUNTS ARE THE SAME AT ITS PLACE AND AT THE NEXT, UNDER THE TABLE's OWN TEST ON ITS NUMBERS.
Statements and proofs. A file BESIDE the table of joints: it turns nothing of it.

Why. What K10 hands on of the table's promise (ShapeBehind.lean, PromiseAt.lean, T2AtPiece.lean,
HandsOfK10.lean, beside this file) asks two equations on the plan's numbers: as many trees, and as
many oracle messages, are counted at the place behind K10's block as at its own. The table's files
have a test on its numbers (`bookFit N ps told`, Johnson/Desc/First/BookFit.lean: at every border
the two numbers are what the blocks in front tell) and the lemma that a block which tells nothing
adds nothing.
  `flatten_map_nil`; `kind_tells_none`, `closing_tells_none`: the kind K10, and its block over the
    first chain's state, tell no oracle message at any of their rounds.
  `counts_of_told`: under the test's yes, at a block number k that tells nothing: N.treesAt ps[k +
    1]? = N.treesAt ps[k]?, and the like for N.msgsAt.
  `k10_step_book_told`: so `bookAt` behind from `bookAt` in front along a `K10Step`, with the two
    equations drawn from the test.
  `kind_tells_none'`, `closing_tells_none'`: the same with `flatMap id` for `flatten`: "what a block
    tells" is written both ways in other files. (A general lemma,
    Johnson/Road/K4/TellsNothing.lean: `tells_nothing`, gives the second form at any shaped block
    that declares no root; here the sentence is read off the kind's own text.)
Limits. The test's yes is a premise; so is told[k]? = some []: that the list `told` is what the
description's own blocks tell, and that block number k is K10's, is the caller's. Nothing on
soundness.

-/
import Johnson.Desc.First.Close.Law.HandsOfK10
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Numbers bookFit bookFit_at told_succ_nil bookAt)

/-- A list of empty lists, flattened. -/
theorem flatten_map_nil {α β : Type} : ∀ l : List α, (l.map fun _ => ([] : List β)).flatten = []
  | [] => rfl
  | _ :: l => flatten_map_nil l

/-- The kind K10 tells no oracle message. -/
theorem kind_tells_none {Cl : Type} (Q : Par) : (kind (Cl := Cl) Q).oracles.flatten = [] :=
  flatten_map_nil _

/-- Nor does its block over the first chain's state. -/
theorem closing_tells_none {Cl : Type} (Q : Par) :
    (K9.closing (Cl := Cl) Q).oracles.flatten = [] := flatten_map_nil _

/-- The same in the other form in which "what a block tells" is written. -/
theorem kind_tells_none' {Cl : Type} (Q : Par) : (kind (Cl := Cl) Q).oracles.flatMap id = [] := by
  rw [List.flatMap_id]
  exact kind_tells_none Q

theorem closing_tells_none' {Cl : Type} (Q : Par) :
    (K9.closing (Cl := Cl) Q).oracles.flatMap id = [] := by
  rw [List.flatMap_id]
  exact closing_tells_none Q

/-- **The plan's two counts at a block that tells nothing.** -/
theorem counts_of_told (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (hf : bookFit N ps told = true) (k : ℕ) (hk : k < ps.length) (hn : told[k]? = some []) :
    N.treesAt ps[k + 1]? = N.treesAt ps[k]? ∧ N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? := by
  have a := bookFit_at N ps told hf k (Nat.le_of_lt hk)
  have b := bookFit_at N ps told hf (k + 1) hk
  have c := told_succ_nil told k hn
  exact ⟨by rw [b.1, a.1, c.1], by rw [b.2, a.2, c.2]⟩

/-- **Where the book stands behind K10's step**, the two equations drawn from the test. -/
theorem k10_step_book_told (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (hf : bookFit N ps told = true) (k : ℕ) (hk : k < ps.length) (hn : told[k]? = some [])
    {s s' : S} (h : K10Step s s') (hb : bookAt N ps[k]? s = true) :
    bookAt N ps[k + 1]? s' = true :=
  k10_step_book ps k N (counts_of_told N ps told hf k hk hn).1
    (counts_of_told N ps told hf k hk hn).2 h hb

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.kind_tells_none
#print axioms VerifiableInference.Desc.First.Close.closing_tells_none
#print axioms VerifiableInference.Desc.First.Close.closing_tells_none'
#print axioms VerifiableInference.Desc.First.Close.counts_of_told
#print axioms VerifiableInference.Desc.First.Close.k10_step_book_told
