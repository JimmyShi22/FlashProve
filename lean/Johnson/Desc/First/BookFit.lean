-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BookFit.lean: WHERE THE BOOK STANDS, BLOCK BY BLOCK: a test that ties the two
numbers by place of the table of joints (`Numbers.treesAt`, `Numbers.msgsAt`) to what the chain's
blocks tell of the trees that they send, and how `bookAt` rides past a block that sends nothing.
Small lemmas; no Mathlib. A file BESIDE the table: it turns nothing of it.

Why. The promise's fixed clause `bookAt` (Johnson/Desc/First/Borders.lean) holds the record's book
and its number of oracle messages against two numbers of the plan AT THE PLACE of the block behind
the border. Whoever carries it across a block owes, beside what the block leaves of the record, a
fact on the numbers at the two places. That fact is no kind's: it is paid here, once, from a test
that runs.

What is said. told: for each block of the chain, in order, the oracles beneath the roots that it
sends (`Block.oracles`, all rounds together). `treesTold`, `msgsTold`: how many roots, and how many
tenants under them, the first k blocks tell. `bookFit`: A TEST: at every border the two numbers are
these. `bookFit_at`: what its yes says. `told_succ_nil`: a block that tells nothing adds nothing.
`bookAt_rides`: the clause rides where the record's book and its messages' number stay and the two
numbers are the same at both places. `bookAt_step`: so, under the test's yes, past every block that
tells nothing.

Limits. (1) The test holds the numbers against THE DESCRIPTION's OWN TELLING; that a plan's numbers
are these is another test. (2) At a block that sends: nothing here: the sending kind's own.
(3) That a block which tells nothing leaves the book and the messages is its kind's to show.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- How many roots the first k blocks tell. -/
def treesTold (told : List (List Oracle)) (k : Nat) : Nat :=
  ((told.take k).map fun os => os.length).sum

/-- How many tenants stand under these roots. -/
def msgsTold (told : List (List Oracle)) (k : Nat) : Nat :=
  ((told.take k).map fun os => (os.map fun o => o.tenants.length).sum).sum

/-- A TEST ON THE NUMBERS: at every border, the chain's end among them, the two numbers by place are
what the blocks in front tell. -/
def bookFit (N : Numbers) (ps : List Place) (told : List (List Oracle)) : Bool :=
  (List.range (ps.length + 1)).all fun k =>
    N.treesAt ps[k]? == treesTold told k && N.msgsAt ps[k]? == msgsTold told k

theorem bookFit_at (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (h : bookFit N ps told = true) (k : Nat) (hk : k ≤ ps.length) :
    N.treesAt ps[k]? = treesTold told k ∧ N.msgsAt ps[k]? = msgsTold told k := by
  have h' := List.all_eq_true.1 h k (List.mem_range.2 (Nat.lt_succ_of_le hk))
  simpa using h'

/-- A block that tells nothing adds nothing. -/
theorem told_succ_nil (told : List (List Oracle)) (k : Nat) (h : told[k]? = some []) :
    treesTold told (k + 1) = treesTold told k ∧ msgsTold told (k + 1) = msgsTold told k := by
  unfold treesTold msgsTold
  rw [List.take_succ, h]
  simp

/-- **`bookAt` rides** where the book and the number of messages stay and the two numbers are the
same at both places. -/
theorem bookAt_rides (N : Numbers) (p p' : Option Place) (s s' : S)
    (hT : N.treesAt p' = N.treesAt p) (hM : N.msgsAt p' = N.msgsAt p)
    (hb : s'.book = s.book) (ho : s'.st.oracles.size = s.st.oracles.size)
    (h : bookAt N p s = true) : bookAt N p' s' = true := by
  unfold bookAt at h ⊢
  rw [hT, hM, hb, ho]
  exact h

/-- **Past every block that tells nothing**, under the test's yes. -/
theorem bookAt_step (N : Numbers) (ps : List Place) (told : List (List Oracle))
    (hf : bookFit N ps told = true) (k : Nat) (hk : k < ps.length) (hn : told[k]? = some [])
    (s s' : S) (hb : s'.book = s.book) (ho : s'.st.oracles.size = s.st.oracles.size)
    (h : bookAt N ps[k]? s = true) : bookAt N ps[k + 1]? s' = true := by
  have a := bookFit_at N ps told hf k (Nat.le_of_lt hk)
  have b := bookFit_at N ps told hf (k + 1) hk
  have c := told_succ_nil told k hn
  exact bookAt_rides N ps[k]? ps[k + 1]? s s' (by rw [b.1, a.1, c.1]) (by rw [b.2, a.2, c.2]) hb
    ho h

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.bookFit_at
#print axioms VerifiableInference.Desc.First.bookAt_step
