-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/BookAtBorder.lean: WHERE THE VERIFIER's BOOK STANDS AT A BORDER
OF THE FIRST CHAIN's THREAD: how many trees it holds, that it has a place for every oracle message
of the statement, and how many such messages there are: AS THE TABLE's NUMBERS COUNT THEM. Three
statements and their proofs; no definition. General in the first chain's letters
(Honest/Thread/First.lean: Letters) and in the letter Said; no kind is named.

Why. A sending's honest part reckons its answers at a statement of its own making, in which its
first new message has the number J.first (Honest/K1/Part.lean). That the chain's statement has just
so many messages in front of the member was asked as a premise "from the thread in front to the
state". It is none: the thread holds the library's promise (onAt, Johnson/Desc/First/Borders.lean),
whose book-keeping (bookAt, the same file) counts them.

  book_at_border    the three equations of bookAt, from the pair of the thread and what is said
  first_at_border   the number of the statement's messages, at a place p and a number n
  trees_at_border   the number of the book's trees, likewise

Whose. The road from the thread to the promise's clauses is partsAt_of_thrS
(Honest/Small/FormPartsS.lean, over FormParts.lean and PromiseParts.lean: three files that are not
the kind K1's). The library has the second and the third equation off the Bool as bookAt_sizes
(Johnson/Desc/First/Look/K3MaskOkTools.lean); it lacks the trees' and stands over heavy imports, so
the Bool is unfolded here anew.

Limits. Nothing proves that the thread holds at any run. That the table's numbers at a place are a
job's own number is not proved here: it is a public equation, asked where these are called. Nothing
on the statement's codes. The verifier's state and public numbers alone: no value of a run and no
value that is sent is named. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Small.FormPartsS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S bookAt)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.Small (partsAt_of_thrS)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **Where the book stands at a border of the thread**: the three equations of the library's
bookAt. -/
theorem book_at_border (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : ThrS L.thread Said b k s m E) :
    s.book.trees.size = L.N.treesAt L.ps[b]? ∧ s.book.place.size = s.st.oracles.size ∧
      s.st.oracles.size = L.N.msgsAt L.ps[b]? := by
  have h : bookAt L.N L.ps[b]? s = true := (partsAt_of_thrS L Said hT).2.book
  unfold bookAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The number**: at a border whose place is p, where the table's numbers count n messages in
front of p, the statement has n oracle messages. -/
theorem first_at_border (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : ThrS L.thread Said b k s m E)
    {p : Place} {n : Nat} (hp : L.ps[b]? = some p) (hn : L.N.msgsAt (some p) = n) :
    s.st.oracles.size = n := by
  rw [← hn, ← hp]
  exact (book_at_border L Said hT).2.2

/-- **The trees likewise**: the verifier's book has as many trees as the numbers count in front of
p. -/
theorem trees_at_border (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : ThrS L.thread Said b k s m E)
    {p : Place} {n : Nat} (hp : L.ps[b]? = some p) (hn : L.N.treesAt (some p) = n) :
    s.book.trees.size = n := by
  rw [← hn, ← hp]
  exact (book_at_border L Said hT).1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.book_at_border
#print axioms ProofFile.Honest.K1.first_at_border
#print axioms ProofFile.Honest.K1.trees_at_border
