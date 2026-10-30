-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Seventh.lean: WHERE THE TEST clause7S ACCEPTS A LIST OF
ENTRIES, THE SEVENTH TEST OF ProverCoinCounts.clauses (Honest/Frame.lean: "a coin stands in two entries that
spend it") ACCEPTS THAT LIST (clause7_of). ONE DIRECTION ALONE: where clause7S rejects, nothing
follows. The test as it stands looks at all pairs of spending entries; the twin sorts twice and
looks at neighbours. One definition with code; statements with their proofs; one closed fact on
small lists. Written by the authors of the honest side of the linear claim's shared rounds (K14), in
the frame's folder, not by the frame's authors; Ahead, Ahead.shares, meets and the test are the
frame's (Honest/Frame.lean).

  clause7S d l    the twin: of the spending entries, each run as a stretch on one line of numbers:
    the owner's code (Addr.code, Honest/BookLinear/Tool.lean) times 2 ^ 40, and the run's start; the
    runs of the base field and those of the extension field each by apartN d (the same file). d: the
    sort's rounds
  spent_apart     **clause7S d l = true → no two spending entries share a coin** (pairwise,
                  Ahead.shares … = false): by apartN_apart twice. Equal owners have one code, and
                  meets does not see a common shift (meets_shift); at unequal owners Ahead.shares is
                  false by its first clause, whatever the codes are: SO NOTHING IS ASKED OF
                  Addr.code
  clause7_of      **clause7S d l = true → the seventh test's Bool at l is true**: THE CONCLUSION IS
                  THE TEST's Bool AS IT STANDS IN ProverCoinCounts.clauses, with the list as a letter: at l :=
                  B.ahead it is the seventh premise of clauses_all_of_each (Honest/BookWordOf.lean),
                  to the letter. By all_pairs (Tool.lean) and shares_comm
  apart_of_clause7   the way back from the test's Bool to "pairwise" (pairwise_of_all, Tool.lean):
                  the eighth test's twin takes the seventh in that form. Nothing in this folder
                  calls it yet: where the seventh's own twin has accepted, spent_apart gives that
                  form
  shares_comm     Ahead.shares is symmetric
  meets_shift     meets at two stretches shifted by one number is meets at the stretches

Kin. Beside Honest/BookApart.lean (below) no law with Ahead.shares in its statement was found in the
frame's files; of the linear claim's kind spent_not_known (Honest/K14/OwnerWhole.lean) has it as a
premise: the eighth test drawn out of "no test is named as failing". On meets: the frame's meets_iff
(Honest/BookGuard.lean); meets_false_of_front and meets_false_of_back (Honest/BookFreeOf.lean, by
authors of this kind); meets_comm, meets_of_le, meets_zero (Tool.lean): none is the shift. No law
that concludes the seventh test was found; none that draws it out of a book's return, beside these:
NEAR KIN, BY THE FRAME's AUTHORS' OWN ACCOUNT (the file was not seen by these authors):
Honest/BookApart.lean: ProverCoinCounts.spentApart: from "no test is named as failing" to "two entries at two
positions of the list of spending entries share no coin", in both orders of the positions;
ProverCoinCounts.spentApart_parts, shares_false_iff; and, in Honest/BookApartWhole.lean, the two at bookWhole's
return. It begins at a book, where apart_of_clause7 begins at the Bool, and holds inside its proof
the step that pairwise_of_all states; it has no law on symmetry. (Closed facts of this kind evaluate
all eleven verdicts at small books: Honest/K14/FreshToy.lean and its fellows: evaluations, no laws.)
By its make, "the same position, or apart" over all pairs of positions, two more tests are kin of
the seventh: the frame's wantsFree (Honest/BookEntries.lean) and the library's apartB
(Johnson/Desc/K12/Law/FirstOk.lean): pairwise_of_all and all_pairs (Tool.lean) are general in the
relation.

Limits. THE TWIN REJECTS LISTS THAT THE TEST ACCEPTS (the closed fact's last four clauses: the kind:
the twin's no and the test's yes; the rounds: the twin's no at 0 rounds and its yes at 20, whence
the test's yes by clause7_of): two owners that differ in the place's kind alone have one code, so
runs of theirs that overlap as numbers are rejected; and with too few rounds a good list can be
rejected. (Among the places of a description that passes the library's FileDescription.placesOk,
Johnson/Desc/Block.lean, no two differ in the kind alone: it counts the triples chain, link, piece.
No law here says so.) A run that ends beyond 2 ^ 40 can reach into the next code's stretch, and two
owners can share a code where link + 1, piece or part reaches 2 ^ 20: then too the twin can only
reject more. No book is named: that a book's entries pass clause7S is shown nowhere here. The closed
fact is an evaluation in Lean's kernel (decide +kernel). Nothing on what an evaluation costs.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookLinear.Tool

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- `Ahead.shares` is symmetric. -/
theorem shares_comm (p q : Ahead) : p.shares q = q.shares p := by
  unfold Ahead.shares
  rw [meets_comm p.start.f, meets_comm p.start.e, BEq.comm (a := p.owner)]

/-- `meets` does not see a common shift. -/
theorem meets_shift (c a n b m : Nat) : meets (c + a) n (c + b) m = meets a n b m := by
  unfold meets
  congr 1
  · congr 1
    exact decide_eq_decide.2 (by omega)
  · exact decide_eq_decide.2 (by omega)

/-- The seventh test's twin: the spending entries' runs as stretches on one line of numbers, by the
  owner's code; those of the base field and those of the extension field each by `apartN`. -/
def clause7S (d : Nat) (l : List Ahead) : Bool :=
  let s := l.filter (·.once)
  apartN d (s.map fun a => (a.owner.code * 2 ^ 40 + a.start.f, a.count.f)) &&
    apartN d (s.map fun a => (a.owner.code * 2 ^ 40 + a.start.e, a.count.e))

/-- **Where the twin accepts, no two spending entries share a coin.** -/
theorem spent_apart {d : Nat} {l : List Ahead} (h : clause7S d l = true) :
    (l.filter (·.once)).Pairwise fun a b => a.shares b = false := by
  unfold clause7S at h
  rw [Bool.and_eq_true] at h
  have h1 := List.pairwise_map.1 (apartN_apart h.1)
  have h2 := List.pairwise_map.1 (apartN_apart h.2)
  refine (h1.and h2).imp ?_
  intro a b hab
  obtain ⟨e1, e2⟩ := hab
  unfold Ahead.shares
  by_cases c : a.owner = b.owner
  · rw [c] at e1 e2
    rw [meets_shift] at e1 e2
    rw [e1, e2]
    simp
  · rw [beq_eq_false_iff_ne.2 c]
    rfl

/-- **TWIN → SEVENTH**: where the twin accepts, the seventh test of `ProverCoinCounts.clauses` accepts. -/
theorem clause7_of {d : Nat} {l : List Ahead} (h : clause7S d l = true) :
    ((l.filter (·.once)).zipIdx.all fun p => (l.filter (·.once)).zipIdx.all fun q =>
      p.2 == q.2 || !p.1.shares q.1) = true :=
  all_pairs (fun a b => !a.shares b) (fun a b => by
    show (!a.shares b) = (!b.shares a)
    rw [shares_comm]) _
    ((spent_apart h).imp fun {a b} hab => by
      show (!a.shares b) = true
      rw [hab]
      rfl)

/-- From the seventh test's Bool to "no two spending entries share a coin". -/
theorem apart_of_clause7 {l : List Ahead}
    (h : ((l.filter (·.once)).zipIdx.all fun p => (l.filter (·.once)).zipIdx.all fun q =>
      p.2 == q.2 || !p.1.shares q.1) = true) :
    (l.filter (·.once)).Pairwise fun a b => a.shares b = false :=
  (pairwise_of_all (fun a b => !a.shares b) _ h).imp fun hab => by simpa using hab

/-! ## Small lists: what the twin must accept, and what it must reject -/

/-- Accepted: two spent runs end to end at one owner, and a carried run over the first. Rejected, by
the twin and by the test: two spent runs that overlap. Rejected by the twin, accepted by the test:
two owners that differ in the kind alone, with runs that overlap as numbers. And three good runs
whose starts fall: rejected by the twin with no round of the sort, accepted at 20. -/
theorem clause7S_small :
    clause7S 20 [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 3⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 2⟩, false⟩] = true ∧
    clause7S 20 [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩] = false ∧
    ((([⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩] : List
        Ahead).filter (·.once)).zipIdx.all fun p =>
      (([⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩] : List
        Ahead).filter (·.once)).zipIdx.all fun q =>
        p.2 == q.2 || !p.1.shares q.1) = false ∧
    clause7S 20 [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K2⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩] = false ∧
    ((([⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K2⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩] : List
        Ahead).filter (·.once)).zipIdx.all fun p =>
      (([⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 3⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K2⟩, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩] : List
        Ahead).filter (·.once)).zipIdx.all fun q =>
        p.2 == q.2 || !p.1.shares q.1) = true ∧
    clause7S 0 [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 6⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 3⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 2⟩, true⟩] = false ∧
    clause7S 20 [⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 6⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 3⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 1⟩, true⟩,
      ⟨"x", ⟨⟨1, none, 0, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨⟨1, none, 1, .K2⟩, 2⟩, true⟩] = true := by
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.shares_comm
#print axioms ProofFile.Honest.meets_shift
#print axioms ProofFile.Honest.spent_apart
#print axioms ProofFile.Honest.clause7_of
#print axioms ProofFile.Honest.apart_of_clause7
#print axioms ProofFile.Honest.clause7S_small
