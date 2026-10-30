-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookRawRows.lean: WHERE bookRaw (Honest/BookWhole.lean) RETURNS A BOOK
W: W's THREE LISTS OF ROWS AND ITS CUTS ARE THE MAKERS' RETURNS, FIELD BY FIELD; SO, WHERE THE
DESCRIPTION's TEST ON ITS PLACES ACCEPTS TOO, THE TENTH OF THE BOOK's OWN TESTS ACCEPTS W; and, at
every book, the second test accepts where no address has two rows. Written by the authors of the
honest side of the linear claim's shared rounds (K14), in the frame's folder, not by the frame's
authors; the makers are theirs. General in the description, the sendings and the merges; nothing is
evaluated. Four statements with their proofs; no definition.

  spendingBook_rows, bookRaw_rows   **the fields first, shared, second and cuts of what the two
                  makers return**
  clause10_at_raw   **the tenth member of ProverCoinCounts.clauses at W is true**: by clause10_of_places
                  (Honest/BookCutsLaw.lean)
  clause2_of_nodup   **the second member of ProverCoinCounts.clauses is true where the rows' addresses are all
                  different**: by one_each (Honest/BookLinear/Tool.lean)

Kin. spendingBook_ahead, bookRaw_ahead (Honest/BookSharedLaw.lean) walk the same two makers for the
field ahead: THE PROOFS HERE ARE THESE, STEP BY STEP, but for what is kept.
What is not claimed. THAT bookRaw RETURNS ANYWHERE. That F.placesOk accepts at any named
description. That a maker's rows have no address twice: in general rowsIn's need not (by a reading
of its text; no example is given: two sendings that are no switch could lie in one part of a place
of kind K12): so the second test at a written description is not had here. The nine other tests.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookCutsLaw
import Johnson.Desc.ProofFile.Honest.BookSharedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place KindName)
open ProofFile.Honest.BookShared

variable {Xi : Type}

/-- **What spendingBook returns**: its three lists of rows are what rowsIn returns at the three
chains; its cuts are the maker's. -/
theorem spendingBook_rows {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    rowsIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok B₀.first ∧
      rowsIn F.shared.blocksInOrder p1 = .ok B₀.shared ∧ rowsIn F.second.blocksInOrder p2 = .ok B₀.second ∧
      B₀.cuts = cutsOf F := by
  unfold spendingBook at h
  obtain ⟨r0, h0, h⟩ := ex_bind h
  obtain ⟨r1, h1, h⟩ := ex_bind h
  obtain ⟨r2, h2, h⟩ := ex_bind h
  rcases hidx : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
      "link 0, moment 0" isIndexMaskMsg with _ | idx
  · rw [hidx] at h
    obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  rw [hidx] at h
  obtain ⟨idx', -, h⟩ := ex_bind h
  obtain ⟨a, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨f0, -, h⟩ := ex_bind h
  obtain ⟨f1, -, h⟩ := ex_bind h
  obtain ⟨f2, -, h⟩ := ex_bind h
  have e := Except.ok.inj h
  subst e
  exact ⟨h0, h1, h2, rfl⟩

/-- **What bookRaw returns, as far as rows and cuts go**: each chain's rows are rowsIn's with
switchRows' behind them; at the shared chain the rows of the folds' own fresh tables behind these;
the cuts are the maker's. -/
theorem bookRaw_rows {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (h : bookRaw F p0 p1 p2 M = .ok W) :
    ∃ (r0 r1 r2 s0 s1 s2 : List (Addr × Due)) (tail : Nat),
      rowsIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok r0 ∧
      rowsIn F.shared.blocksInOrder p1 = .ok r1 ∧ rowsIn F.second.blocksInOrder p2 = .ok r2 ∧
      switchRows F.first.blocksInOrder p0 (firstCodes p0 p1) = .ok s0 ∧
      switchRows F.shared.blocksInOrder p1 (firstCodes p0 p1) = .ok s1 ∧
      switchRows F.second.blocksInOrder p2 (firstCodes p0 p1) = .ok s2 ∧
      due? "the shared chain's mask code" ((codesUnder p1 "Omega").map (·.2.r)) = .ok tail ∧
      W.first = r0 ++ s0 ∧
      W.shared = r1 ++ s1 ++ (ownFreshIn F.shared.blocksInOrder).map (·.row tail) ∧
      W.second = r2 ++ s2 ∧ W.cuts = cutsOf F := by
  unfold bookRaw at h
  obtain ⟨B₀, hB, h⟩ := ex_bind h
  obtain ⟨m0, -, h⟩ := ex_bind h
  obtain ⟨m1, -, h⟩ := ex_bind h
  obtain ⟨s0, hs0, h⟩ := ex_bind h
  obtain ⟨s1, hs1, h⟩ := ex_bind h
  obtain ⟨s2, hs2, h⟩ := ex_bind h
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨seg, -, h⟩ := ex_bind h
  obtain ⟨iF, -, h⟩ := ex_bind h
  obtain ⟨cF, -, h⟩ := ex_bind h
  obtain ⟨iO, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨cO, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨pq, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨tail, htail, h⟩ := ex_bind h
  have e := Except.ok.inj h
  obtain ⟨q0, q1, q2, q3⟩ := spendingBook_rows hB
  subst e
  exact ⟨B₀.first, B₀.shared, B₀.second, s0, s1, s2, tail, q0, q1, q2, hs0, hs1, hs2, htail, rfl,
    rfl, rfl, q3⟩

/-- **THE TENTH TEST ACCEPTS THE BOOK THAT bookRaw RETURNS**, where it returns one and the
description's test on the places accepts. -/
theorem clause10_at_raw {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (h : bookRaw F p0 p1 p2 M = .ok W) (hp : F.placesOk = true) :
    ((W.clauses F)[9]?).map (·.2) = some true := by
  obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := bookRaw_rows h
  have q := clause10_of_places hp hc
  simp only [ProverCoinCounts.clauses, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some]
  exact congrArg some q

/-- **THE SECOND TEST, AS IT STANDS IN ProverCoinCounts.clauses, FROM "NO ADDRESS HAS TWO ROWS".** -/
theorem clause2_of_nodup (F : FileDescription Xi) {B : ProverCoinCounts}
    (h : ((B.first ++ B.shared ++ B.second).map (·.1)).Nodup) :
    ((B.clauses F)[1]?).map (·.2) = some true := by
  have q := one_each (fun r : Addr × Due => r.1) (B.first ++ B.shared ++ B.second) h
  simp only [ProverCoinCounts.clauses, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some]
  exact congrArg some q

end ProofFile.Honest

#print axioms ProofFile.Honest.spendingBook_rows
#print axioms ProofFile.Honest.bookRaw_rows
#print axioms ProofFile.Honest.clause10_at_raw
#print axioms ProofFile.Honest.clause2_of_nodup
