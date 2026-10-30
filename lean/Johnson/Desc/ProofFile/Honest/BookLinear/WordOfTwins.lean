-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/WordOfTwins.lean: WHERE THE TWINS OF THE FIFTH, THE
SEVENTH, THE EIGHTH AND THE ELEVENTH TEST OF ProverCoinCounts.clauses (Honest/Frame.lean) ACCEPT A BOOK's
ENTRIES AT A DESCRIPTION's ORDER OF PLACES, THAT ORDER HAS NO PLACE TWICE, THE ENTRIES' NAMES ARE
THE KEYS' NAMES, AND THE SEVEN OTHER TESTS ACCEPT THE BOOK, NO TEST IS NAMED AS FAILING (B.word F =
none). One statement; its proof is one term; no definition. General in the description, the book,
the function g that names a place's position, the sort's rounds, the two tables and the list of
keys. Written by the authors of the honest side of the linear claim's shared rounds (K14), in the
frame's folder, not by the frame's authors; the tests are theirs.

  word_none_of_twins   fifteen premises: hn: the order has no place twice · t5, t7, t8: clause5P,
                  clause7S, clause8Q accept (Fifth.lean, Seventh.lean, Eighth.lean of this folder) ·
                  hT, hI, hC, hK: the tables pass, every key lies in them, no code stands twice, the
                  names are the keys' names (NameKeys.lean) · h1 h2 h3 h4 h6 h9 h10: the seven other
                  tests' Bools, as they stand among the premises of word_none_of_clauses
                  (Honest/BookWordOf.lean). THE PROOF HANDS EACH TWIN's LAW's CONCLUSION TO
                  word_none_of_clauses AS THE PREMISE THAT IT IS: no rewriting. The seventh's twin
                  is spent twice: for the seventh test (clause7_of), and for the eighth's premise
                  "no two spending entries share a coin" (spent_apart)

What it is for. The four tests walk all pairs of entries, or the order of places at every entry;
their twins sort, or go by positions. Whoever has the twins' yes at a book, by evaluation or by a
law on the makers, and with it hn, hK and the seven other tests, has here what ProverCoinCounts.checked asks;
bookWhole_returns_of (Honest/BookWordOf.lean) goes on from there.

That the order of a description has no place twice: the frame's orderOf_nodup
(Honest/Law/Rule/Tests.lean), under the library's test FileDescription.placesOk: not called here: a
premise.

Kin. word_none_of_clauses (Honest/BookWordOf.lean): the same conclusion from the eleven Bools
themselves. Bookkeeping: no new mathematics.

Limits. NO PREMISE IS SHOWN HERE AT ANY BOOK: an implication. ONE DIRECTION ALONE: each twin rejects
lists that its test accepts (closed facts in Fifth.lean, Seventh.lean and Eighth.lean; for the
eleventh's: NameKeys.lean's Limits: argued). ONE LETTER d serves the seventh's twin, the eighth's
and the keys' nodupN: whoever has the three at different rounds cannot call it. Nothing on what an
evaluation costs. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWordOf
import Johnson.Desc.ProofFile.Honest.BookLinear.Fifth
import Johnson.Desc.ProofFile.Honest.BookLinear.Eighth
import Johnson.Desc.ProofFile.Honest.BookLinear.NameKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- **WHERE THE FOUR TWINS AND THE SEVEN OTHER TESTS ACCEPT, NO TEST IS NAMED AS FAILING.**
CONDITIONAL: the fifteen premises. -/
theorem word_none_of_twins {g : Place → Nat} {d : Nat} {owners uses : List String}
    {K : List NameKey}
    (hn : (orderOf F).Nodup)
    (t5 : clause5P g (orderOf F) B.ahead = true)
    (t7 : clause7S d B.ahead = true)
    (t8 : clause8Q g d (orderOf F) B.ahead = true)
    (hT : tablesOk owners uses = true)
    (hI : K.all (NameKey.inTables owners.length uses.length) = true)
    (hC : nodupN d (K.map NameKey.code) = true)
    (hK : B.ahead.map (·.name) = K.map (NameKey.name owners uses))
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
    (h6 : (B.ahead.all fun a => !((F.first.blocksInOrder.map (·.place)).contains a.owner.place &&
        (F.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true)
    (h9 : (B.ahead.all fun a => !(a.once && (F.shared.blocksInOrder.map (·.place)).contains a.owner.place &&
        !(F.shared.blocksInOrder.map (·.place)).contains a.spender.place)) = true)
    (h10 : (B.cuts.all fun c =>
        (F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
          F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
          F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup c.1 ==
            some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
          (B.cuts.filter fun d => d.1 == c.1).length == 1) = true) :
    B.word F = none :=
  word_none_of_clauses h1 h2 h3 h4 (clause5P_of hn t5) h6 (clause7_of t7)
    (clause8Q_of hn (spent_apart t7) t8) h9 h10 (clause11_of_keys hT hI hC hK)

end ProofFile.Honest

#print axioms ProofFile.Honest.word_none_of_twins
