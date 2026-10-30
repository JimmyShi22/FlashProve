-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWordOf.lean: WHERE EACH OF THE BOOK's ELEVEN OWN TESTS
(ProverCoinCounts.clauses, Honest/Frame.lean) ACCEPTS A BOOK AT A DESCRIPTION, NO TEST IS NAMED AS FAILING
(B.word F = none); AND WHERE bookRaw RETURNS SUCH A BOOK, bookWhole RETURNS IT
(Honest/BookWhole.lean). Written by the authors of the honest side of the linear claim's shared
rounds (K14), in the frame's folder, not by the frame's authors; the tests and the makers are
theirs. Six statements with their proofs; no definition. General in the description and the book.

  clauses_verdicts   the eleven verdicts of ProverCoinCounts.clauses, in the list's order, ARE the eleven Bools
                  that stand below as premises: an equation of lists, by unfolding alone (rfl)
  clauses_all_of_each   **the tie**: eleven premises, EACH ONE TEST's Bool AS IT STANDS IN THE LIST
                  of ProverCoinCounts.clauses, in the list's order, its eight local names written out (the three
                  chains' places; the order of places; all rows; the spending entries, numbered;
                  all entries, numbered; the sub-protocols' sizes): all eleven verdicts are true
  word_none_of_all   where all verdicts are true, no test is named: the converse of ProverCoinCounts.tests
                  (Honest/Law/Rule/Tests.lean)
  word_none_of_clauses   the two joined: eleven premises; no test is named
  checked_ok_of_word   then ProverCoinCounts.checked hands the book on
  bookWhole_returns_of   and where bookRaw returns that book, bookWhole returns it

What it is for. A law that concludes a test's Bool to the letter, or a test's Bool evaluated at one
book, is laid in as one premise, without a rewriting. THE ELEVEN ARE HELD TO THE LIST BY LEAN: BY
clauses_verdicts: its proof fails if a test is added, struck, written twice or moved, or if a test's
Bool is changed. IT DOES NOT SEE A TEST's NAME (the string). The proof of clauses_all_of_each alone
sees less: a test added, or a Bool changed; a change of the order or a test written twice it does
not see, and a test struck shows there only as a warning on an unused premise. (Each of these seven
cases was tried at Lean on copies of the list.)
Limits. NO TEST's VERDICT IS SHOWN BY IT, AT ANY BOOK: an equation and five implications.
Bookkeeping: no new mathematics. Kin, all of it the other way round, from a return or from "no test
is named": ProverCoinCounts.tests and the seven beside it (Honest/Law/Rule/Tests.lean), bookWhole_word
(Honest/AtPureLaw.lean), checked_ok (Honest/BookSharedLaw.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- **The eleven verdicts, in the list's order, are the eleven Bools that stand below as premises.**
By unfolding alone: the proof fails if a test is added, struck, written twice or moved, or if a
test's Bool is changed; a test's name it does not see. -/
theorem clauses_verdicts : (B.clauses F).map (fun c => c.2) =
     [(B.first.all (fun r => (F.first.blocksInOrder.map (·.place)).contains r.1.place) &&
        B.shared.all (fun r => (F.shared.blocksInOrder.map (·.place)).contains r.1.place) &&
        B.second.all fun r => (F.second.blocksInOrder.map (·.place)).contains r.1.place),
      ((B.first ++ B.shared ++ B.second).all fun r =>
        ((B.first ++ B.shared ++ B.second).filter fun q => q.1 == r.1).length == 1),
      (masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared &&
        masksOk F.second.blocksInOrder B.second),
      (B.ahead.all fun a =>
        decide (a.start.f + a.count.f ≤ (dueAt (B.first ++ B.shared ++ B.second) a.owner).f) &&
        decide (a.start.e + a.count.e ≤
        (dueAt (B.first ++ B.shared ++ B.second) a.owner).e)),
      (B.ahead.all fun a => (orderOf F).contains a.owner.place &&
        (orderOf F).contains a.spender.place && a.owner.before (orderOf F) a.spender),
      (B.ahead.all fun a => !((F.first.blocksInOrder.map (·.place)).contains a.owner.place &&
        (F.shared.blocksInOrder.map (·.place)).contains a.spender.place)),
      ((B.ahead.filter (·.once)).zipIdx.all fun p =>
        (B.ahead.filter (·.once)).zipIdx.all fun q => p.2 == q.2 || !p.1.shares q.1),
      (B.ahead.zipIdx.all fun p => !p.1.once || B.ahead.zipIdx.all fun q =>
        p.2 == q.2 || !p.1.shares q.1 ||
        !(q.1.spender.before (orderOf F) p.1.spender ||
        (q.1.spender == p.1.spender && !q.1.once))),
      (B.ahead.all fun a => !(a.once && (F.shared.blocksInOrder.map (·.place)).contains a.owner.place &&
        !(F.shared.blocksInOrder.map (·.place)).contains a.spender.place)),
      (B.cuts.all fun c =>
        (F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup c.1 ==
        some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
        (B.cuts.filter fun d => d.1 == c.1).length == 1),
      (B.ahead.all fun a => (B.ahead.filter fun b => b.name == a.name).length == 1)] :=
  rfl

/-- **THE TIE.** Each premise is one test's Bool as it stands in ProverCoinCounts.clauses, in the list's order,
the local names written out. Then all eleven verdicts are true. CONDITIONAL: the eleven. -/
theorem clauses_all_of_each
    (h1 : (B.first.all (fun r => (F.first.blocksInOrder.map (·.place)).contains r.1.place) &&
        B.shared.all (fun r => (F.shared.blocksInOrder.map (·.place)).contains r.1.place) &&
        B.second.all fun r => (F.second.blocksInOrder.map (·.place)).contains r.1.place) = true)
    (h2 : ((B.first ++ B.shared ++ B.second).all fun r =>
        ((B.first ++ B.shared ++ B.second).filter fun q => q.1 == r.1).length == 1) = true)
    (h3 : (masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared &&
        masksOk F.second.blocksInOrder B.second) = true)
    (h4 : (B.ahead.all fun a =>
        decide (a.start.f + a.count.f ≤ (dueAt (B.first ++ B.shared ++ B.second) a.owner).f) &&
          decide (a.start.e + a.count.e ≤
            (dueAt (B.first ++ B.shared ++ B.second) a.owner).e)) = true)
    (h5 : (B.ahead.all fun a => (orderOf F).contains a.owner.place &&
        (orderOf F).contains a.spender.place && a.owner.before (orderOf F) a.spender) = true)
    (h6 : (B.ahead.all fun a => !((F.first.blocksInOrder.map (·.place)).contains a.owner.place &&
        (F.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true)
    (h7 : ((B.ahead.filter (·.once)).zipIdx.all fun p =>
        (B.ahead.filter (·.once)).zipIdx.all fun q => p.2 == q.2 || !p.1.shares q.1) = true)
    (h8 : (B.ahead.zipIdx.all fun p => !p.1.once || B.ahead.zipIdx.all fun q =>
        p.2 == q.2 || !p.1.shares q.1 ||
          !(q.1.spender.before (orderOf F) p.1.spender ||
            (q.1.spender == p.1.spender && !q.1.once))) = true)
    (h9 : (B.ahead.all fun a => !(a.once && (F.shared.blocksInOrder.map (·.place)).contains a.owner.place &&
        !(F.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true)
    (h10 : (B.cuts.all fun c =>
        (F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
          F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
          F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup c.1 ==
            some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
          (B.cuts.filter fun d => d.1 == c.1).length == 1) = true)
    (h11 : (B.ahead.all fun a => (B.ahead.filter fun b => b.name == a.name).length == 1) = true) :
    (B.clauses F).all (fun c => c.2) = true := by
  unfold ProverCoinCounts.clauses
  simp only [List.all_cons, List.all_nil, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    Bool.and_self]

/-- Where all verdicts are true, no test is named as failing: the converse of ProverCoinCounts.tests.
CONDITIONAL: h. -/
theorem word_none_of_all (h : (B.clauses F).all (fun c => c.2) = true) : B.word F = none := by
  have hn : (B.clauses F).find? (fun c => !c.2) = none :=
    List.find?_eq_none.2 fun c hc => by
      show ¬ (!c.2) = true
      rw [List.all_eq_true.1 h c hc]
      decide
  unfold ProverCoinCounts.word
  rw [hn]
  rfl

/-- **Where each of the eleven tests accepts, no test is named as failing.** CONDITIONAL: the
eleven, as in clauses_all_of_each. -/
theorem word_none_of_clauses
    (h1 : (B.first.all (fun r => (F.first.blocksInOrder.map (·.place)).contains r.1.place) &&
        B.shared.all (fun r => (F.shared.blocksInOrder.map (·.place)).contains r.1.place) &&
        B.second.all fun r => (F.second.blocksInOrder.map (·.place)).contains r.1.place) = true)
    (h2 : ((B.first ++ B.shared ++ B.second).all fun r =>
        ((B.first ++ B.shared ++ B.second).filter fun q => q.1 == r.1).length == 1) = true)
    (h3 : (masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared &&
        masksOk F.second.blocksInOrder B.second) = true)
    (h4 : (B.ahead.all fun a =>
        decide (a.start.f + a.count.f ≤ (dueAt (B.first ++ B.shared ++ B.second) a.owner).f) &&
          decide (a.start.e + a.count.e ≤
            (dueAt (B.first ++ B.shared ++ B.second) a.owner).e)) = true)
    (h5 : (B.ahead.all fun a => (orderOf F).contains a.owner.place &&
        (orderOf F).contains a.spender.place && a.owner.before (orderOf F) a.spender) = true)
    (h6 : (B.ahead.all fun a => !((F.first.blocksInOrder.map (·.place)).contains a.owner.place &&
        (F.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true)
    (h7 : ((B.ahead.filter (·.once)).zipIdx.all fun p =>
        (B.ahead.filter (·.once)).zipIdx.all fun q => p.2 == q.2 || !p.1.shares q.1) = true)
    (h8 : (B.ahead.zipIdx.all fun p => !p.1.once || B.ahead.zipIdx.all fun q =>
        p.2 == q.2 || !p.1.shares q.1 ||
          !(q.1.spender.before (orderOf F) p.1.spender ||
            (q.1.spender == p.1.spender && !q.1.once))) = true)
    (h9 : (B.ahead.all fun a => !(a.once && (F.shared.blocksInOrder.map (·.place)).contains a.owner.place &&
        !(F.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true)
    (h10 : (B.cuts.all fun c =>
        (F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
          F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
          F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup c.1 ==
            some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
          (B.cuts.filter fun d => d.1 == c.1).length == 1) = true)
    (h11 : (B.ahead.all fun a => (B.ahead.filter fun b => b.name == a.name).length == 1) = true) :
    B.word F = none :=
  word_none_of_all (clauses_all_of_each h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)

/-- Where no test is named as failing, ProverCoinCounts.checked hands the book on. CONDITIONAL: h. -/
theorem checked_ok_of_word (h : B.word F = none) : ProverCoinCounts.checked F B = .ok B := by
  unfold ProverCoinCounts.checked
  rw [h]

/-- **Where bookRaw returns a book at which no test is named as failing, bookWhole returns it.**
CONDITIONAL: hR; h. -/
theorem bookWhole_returns_of {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (hR : bookRaw F p0 p1 p2 M = .ok B) (h : B.word F = none) :
    bookWhole F p0 p1 p2 M = .ok B := by
  unfold bookWhole
  rw [hR]
  exact checked_ok_of_word h

end ProofFile.Honest

#print axioms ProofFile.Honest.clauses_verdicts
#print axioms ProofFile.Honest.clauses_all_of_each
#print axioms ProofFile.Honest.word_none_of_all
#print axioms ProofFile.Honest.word_none_of_clauses
#print axioms ProofFile.Honest.checked_ok_of_word
#print axioms ProofFile.Honest.bookWhole_returns_of
