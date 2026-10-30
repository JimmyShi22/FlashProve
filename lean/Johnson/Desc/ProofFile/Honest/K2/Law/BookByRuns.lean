-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/BookByRuns.lean: the kind "the code switch" (K2): THE KIND's
TEST ON THE BOOK (`bookFits`, Honest/K2/Fresh.lean) AT ONE OWNER, FOR EVERY ADDRESS, FROM ONE PUBLIC
TEST ON A LIST OF THE OWNER's ENTRIES AS TUPLES (spender, start, count, mark). GENERAL: at any book,
order, owner and sending; nothing is evaluated here and no book is named. WHY: the field book of
`FreshAsks` asks `bookFits` at the two lists that a book gives (`ProverCoinCounts.spentBy`, `ProverCoinCounts.knownBy`,
Honest/Frame.lean) FOR EVERY ADDRESS q; a closed fact on a written book comes as a list of tuples.
Definitions with code: public tests; statements with their proofs.

  `bookFitsR`, `bookFits_runs`   the test reads of an entry its run alone (start and count): the
                    same text on runs; the two are one
  `entryTuple`      an entry as (spender, start, count, mark)
  `spentIn`, `knownIn`, `fitsIn`   of a list of tuples, at an address q and a test "stands before":
                    the runs that q spends; the runs that are known; `bookFitsR` at the two
  `book_by_tuples`  where L is the list of the owner's entries as tuples, in the book's order:
                    `bookFits` at the book's two lists at q IS `fitsIn` at L and q
  `tupleWithin`, `spendersIn`   a tuple lies within the sending's count; the addresses that spend
  `ownerOk`         THE ONE TEST: each tuple lies within the sending's count; at each address that
                    spends, `fitsIn` says yes
  `fitsIn_congr`    `fitsIn` reads "stands before" at the list's spenders against q alone
  `all_of_ownerOk`  where it passes, `fitsIn` says yes AT EVERY ADDRESS
  `book_of_ownerOk`   THE END: the field book's own text at that owner

Limits. GENERAL LAWS ON LISTS: no book, plan or order is named; that a list of tuples IS a book's is
a premise (hL). `ownerOk` is shown of no list here. No coin occurs: starts and counts are numbers.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Fresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Place)

/-- `bookFits`' own text, on runs. es: what one part spends. ks: what is known. -/
def bookFitsR (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (es ks : List Run) : Bool :=
  (es ++ ks).all (fun e =>
      decide (e.1.f + e.2.f ≤ (sendingDue codes sent fresh).f) &&
        decide (e.1.e + e.2.e ≤ (sendingDue codes sent fresh).e)) &&
    es.all (fun e => ks.all fun k => !e.meets k) &&
    es.zipIdx.all (fun x => es.zipIdx.all fun y => x.2 == y.2 || !x.1.meets y.1) &&
    (es.isEmpty ||
      fresh.any (fun x =>
        es.length == 1 &&
          es.all (fun e => e.inside (coefficientsRun codes sent fresh x.1 x.2) &&
            (coefficientsRun codes sent fresh x.1 x.2).inside e) &&
          ks.all fun k => !k.meets (freshTailsRun codes sent fresh x.1 x.2)) ||
      (List.range sent.size).any fun n =>
        (foldAt fresh n).isNone && (sent.getD n default).shape.answers != 0 &&
          es.all (fun e => e.inside (freeRun codes sent fresh n)) &&
          ks.all fun k => !k.meets (wholeRun codes sent fresh n) ||
            k.inside (freeRun codes sent fresh n))

/-- **The test reads of an entry its run alone.** -/
theorem bookFits_runs (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (es ks : List Ahead) :
    bookFits codes sent fresh es ks = bookFitsR codes sent fresh (es.map runOf) (ks.map runOf) := by
  unfold bookFits bookFitsR
  rw [← List.map_append]
  simp only [List.all_map, List.zipIdx_map, List.isEmpty_map, List.length_map,
    Function.comp_def, Prod.map, id, runOf]
  rfl

/-- An entry as (spender, start, count, mark). -/
def entryTuple (e : Ahead) : Addr × Due × Due × Bool := (e.spender, e.start, e.count, e.once)

/-- Of a list of tuples: the runs that q spends. -/
def spentIn (L : List (Addr × Due × Due × Bool)) (q : Addr) : List Run :=
  (L.filter fun t => t.1 == q && t.2.2.2).map fun t => (t.2.1, t.2.2.1)

/-- Of a list of tuples: the other runs that are given to q, or to an address that stands before q.
-/
def knownIn (bef : Addr → Addr → Bool) (L : List (Addr × Due × Due × Bool)) (q : Addr) :
    List Run :=
  (L.filter fun t => !(t.1 == q && t.2.2.2) && (t.1 == q || bef t.1 q)).map fun t =>
    (t.2.1, t.2.2.1)

/-- The test at a list of tuples and an address. -/
def fitsIn (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (bef : Addr → Addr → Bool)
    (L : List (Addr × Due × Due × Bool)) (q : Addr) : Bool :=
  bookFitsR codes sent fresh (spentIn L q) (knownIn bef L q)

/-- **`bookFits` at the book's two lists is `fitsIn` at the owner's tuples.** -/
theorem book_by_tuples (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) {B : ProverCoinCounts} (ord : List Place) {o : Addr}
    {L : List (Addr × Due × Due × Bool)}
    (hL : (B.ahead.filter fun e => e.owner == o).map entryTuple = L) (q : Addr) :
    bookFits codes sent fresh (B.spentBy o q) (B.knownBy ord o q) =
      fitsIn codes sent fresh (Addr.before ord) L q := by
  subst hL
  have h1 : B.spentBy o q =
      (B.ahead.filter fun e => e.owner == o).filter fun e => e.spender == q && e.once := by
    unfold ProverCoinCounts.spentBy
    rw [List.filter_filter]
    congr 1
    funext e
    cases (e.owner == o) <;> cases (e.spender == q) <;> cases e.once <;> rfl
  have h2 : B.knownBy ord o q =
      (B.ahead.filter fun e => e.owner == o).filter fun e =>
        !(e.spender == q && e.once) && (e.spender == q || e.spender.before ord q) := by
    unfold ProverCoinCounts.knownBy
    rw [List.filter_filter]
    congr 1
    funext e
    cases (e.owner == o) <;> cases (e.spender == q) <;> cases e.once <;>
      cases (e.spender.before ord q) <;> rfl
  rw [bookFits_runs, h1, h2]
  unfold fitsIn spentIn knownIn
  rw [List.filter_map, List.filter_map, List.map_map, List.map_map]
  rfl

/-- A tuple lies within the sending's count. -/
def tupleWithin (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (t : Addr × Due × Due × Bool) : Bool :=
  decide (t.2.1.f + t.2.2.1.f ≤ (sendingDue codes sent fresh).f) &&
    decide (t.2.1.e + t.2.2.1.e ≤ (sendingDue codes sent fresh).e)

/-- The addresses that spend, each once. -/
def spendersIn (L : List (Addr × Due × Due × Bool)) : List Addr :=
  ((L.filter fun t => t.2.2.2).map (·.1)).eraseDups

/-- **THE ONE TEST** on a list of tuples. -/
def ownerOk (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (bef : Addr → Addr → Bool)
    (L : List (Addr × Due × Due × Bool)) : Bool :=
  L.all (tupleWithin codes sent fresh) && (spendersIn L).all (fitsIn codes sent fresh bef L)

/-- `fitsIn` reads "stands before" at the list's spenders against q alone. -/
theorem fitsIn_congr (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) {bef bef' : Addr → Addr → Bool}
    {L : List (Addr × Due × Due × Bool)} {q : Addr} (h : ∀ t ∈ L, bef t.1 q = bef' t.1 q) :
    fitsIn codes sent fresh bef L q = fitsIn codes sent fresh bef' L q := by
  unfold fitsIn knownIn
  rw [List.filter_congr fun t ht => by rw [h t ht]]

/-- **Where the one test passes, `fitsIn` says yes at every address.** -/
theorem all_of_ownerOk {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)} {bef : Addr → Addr → Bool} {L : List (Addr × Due × Due × Bool)}
    (h : ownerOk codes sent fresh bef L = true) (q : Addr) :
    fitsIn codes sent fresh bef L q = true := by
  unfold ownerOk at h
  rw [Bool.and_eq_true] at h
  by_cases hq : q ∈ spendersIn L
  · exact List.all_eq_true.1 h.2 q hq
  · have he : spentIn L q = [] := by
      unfold spentIn
      rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro t ht hc
      rw [Bool.and_eq_true] at hc
      refine hq ?_
      unfold spendersIn
      rw [List.mem_eraseDups]
      exact List.mem_map.2 ⟨t, List.mem_filter.2 ⟨ht, hc.2⟩, beq_iff_eq.1 hc.1⟩
    unfold fitsIn bookFitsR
    rw [he]
    simp only [List.nil_append, List.all_nil, List.zipIdx_nil, List.isEmpty_nil, Bool.true_or,
      Bool.and_true]
    unfold knownIn
    rw [List.all_map]
    refine List.all_eq_true.2 fun t ht => ?_
    exact List.all_eq_true.1 h.1 t (List.mem_filter.1 ht).1

/-- **THE FIELD book's OWN TEXT AT AN OWNER, FROM THE ONE TEST ON ITS TUPLES.** bef: a test that
agrees with the order's "stands before" at the list's spenders. -/
theorem book_of_ownerOk {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)} {B : ProverCoinCounts} {ord : List Place} {o : Addr}
    {L : List (Addr × Due × Due × Bool)} {bef : Addr → Addr → Bool}
    (hL : (B.ahead.filter fun e => e.owner == o).map entryTuple = L)
    (hb : ∀ t ∈ L, ∀ q ∈ spendersIn L, Addr.before ord t.1 q = bef t.1 q)
    (h : ownerOk codes sent fresh bef L = true) :
    ∀ q : Addr, bookFits codes sent fresh (B.spentBy o q) (B.knownBy ord o q) = true := by
  have h' : ownerOk codes sent fresh (Addr.before ord) L = true := by
    unfold ownerOk at h ⊢
    rw [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, List.all_eq_true.2 fun q hq => ?_⟩
    rw [fitsIn_congr codes sent fresh fun t ht => hb t ht q hq]
    exact List.all_eq_true.1 h.2 q hq
  intro q
  rw [book_by_tuples codes sent fresh ord hL q]
  exact all_of_ownerOk h' q

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.bookFitsR
#print axioms ProofFile.Honest.K2.Law.bookFits_runs
#print axioms ProofFile.Honest.K2.Law.entryTuple
#print axioms ProofFile.Honest.K2.Law.spentIn
#print axioms ProofFile.Honest.K2.Law.knownIn
#print axioms ProofFile.Honest.K2.Law.fitsIn
#print axioms ProofFile.Honest.K2.Law.book_by_tuples
#print axioms ProofFile.Honest.K2.Law.tupleWithin
#print axioms ProofFile.Honest.K2.Law.spendersIn
#print axioms ProofFile.Honest.K2.Law.ownerOk
#print axioms ProofFile.Honest.K2.Law.fitsIn_congr
#print axioms ProofFile.Honest.K2.Law.all_of_ownerOk
#print axioms ProofFile.Honest.K2.Law.book_of_ownerOk
