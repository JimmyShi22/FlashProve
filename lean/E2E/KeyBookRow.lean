-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookRow.lean: which ranges of other parts' coins the prover's part at each span of a lookup
has to state, by name and count, to agree with the entries that E2E/KeyBookFace.lean builds for the
book of coins. The book (`ProverCoinCounts`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is the
public table of how many coins each part (`Part`) of an honest prover has. An entry of the book
(`Ahead`) names a range of the coins of one part, the owner (`Ahead.owner`), that one other part,
the spender (`Ahead.spender`), is given too. A span (`Span`, E2E/KeyBookFace.lean) is a range of a
lookup's rounds that is one part in the list of parts at the lookup's place (`Place`: where in a
protocol description a sub-protocol is): one round that sends nothing, or one masked sumcheck. A
`Seat` (same file) holds the lookup's place and the two owners, each with its address and its name.
The owners are the parts that send the two oracle messages whose mask entries the lookup uses
(below: the first and the second message). `layFrom S ps p a b` (same file) is the list of the
entries for a list of spans ps at the `Seat` S, where the first span is part number p of the place
and a and b are the two owners' next unused coins. The file has four definitions and four theorems,
general in S, ps, p, a and b. They are about public data only: no part and no prover is defined.

Why. The frame gives a part a range of another part's coins only if the part states the range under
the name and the count of the book's entry, and states its ranges in the book's order (`lend`,
`lendPart`, in the frame). At the full size (`keyFull`) the key file's two lookups have 935 and 920
spans (a `#guard`, a test that Lean's evaluator runs, in E2E/KeyBookAtWritten.lean). This file says
what the parts have to state, and shows that the entries have just these names and counts.

  `named_lay`: if s is span number j of ps, the entries of `layFrom S ps p a b` that name part
    number p + j of the place as their spender have, in the list's order, just the names and counts
    of `Span.spends` at s: `namedAt S (layFrom S ps p a b) (p + j) = s.spends S (p + j)`
  `lay_once`: every entry of `layFrom S ps p a b` is marked as spent (`Ahead.once` is true). So, of
    these entries, the filter of `lendPart` for the ranges that a part spends keeps all, and its
    filter for the ranges that a part carries keeps none
  `lay_spender`: every entry of `layFrom S ps p a b` names as its spender a part at the place of S
    whose number is at least p
  `namedAt_none`: so no entry of it names a part of that place whose number is below p
  `Span.spends S p`: a definition: the names and counts, in order, that part number p has to state
    in its field `spends` if it is the part at the span. At a round that sends nothing: none. At a
    masked sumcheck with the call k: the first range (`sumName`, `ownRun k` coins) and, if the call
    has end values, the second (`endName`, one coin for each end value). All are coins of the
    extension field. This is the form of the field `spends` of the part for a masked sumcheck
    (`sumPart`, Johnson/Desc/ProofFile/Honest/Sum.lean) at these two names and a job of the shape k
  `sumName S p`, `endName S second p`: definitions: the names of the two ranges of the masked
    sumcheck at part number p: `runName` at an owner's name, the part's address and the use "sum"
    or "ends". The first range has the first owner's name. The second has the second owner's name
    if the span's flag second is true (the mask entries of its end values are in the second
    message), and the first owner's name if not
  `namedAt S es q`: a definition: the names and counts (`Ahead.named`) of the entries of es whose
    spender is part number q at the place of S, in the order of es

By what. No theorem of another file of the library is called. The proofs go by induction on the list
of spans, unfold `layFrom` and use general lemmas on lists; `named_lay` calls `namedAt_none`, which
calls `lay_spender`. The definitions of other files: `Span`, `Seat`, `layFrom`
(E2E/KeyBookFace.lean); `Ahead`, `Ahead.named`, `Addr`, `Due` (the frame); `runName`
(Johnson/Desc/ProofFile/Honest/ForKinds.lean); `ownRun`, `endRuns`
(Johnson/Desc/ProofFile/Honest/Sum.lean).

Limits.
- The theorems speak of the entries for one list of spans. A lookup's entries at the face f
  (`K3.Face`: the lookup's public numbers), `bookEntries S f a b` (E2E/KeyBookFace.lean), are
  `layFrom S (spansOf f) 0 a b` by definition; no theorem is stated at `bookEntries`.
- Whether a whole book has no other entry that names a part at the lookup's place depends on that
  book. At `keyBook` (E2E/KeyBook.lean) it can be read off the definitions: each lookup has a place
  of its own (`lookPlace`, E2E/KeyPlaces.lean), and the entries that are not the lookups' name parts
  at other places. It is not shown.
- That a list of parts states just these names and counts has to be shown by whoever defines the
  list. None is defined here.
- The list of a lookup's honest parts `lookRow`
  (Johnson/Desc/ProofFile/Honest/K3/Row.lean) states these counts (`stated_counts` with
  `spans_of_stages`, E2E/KeyBookHeldK3.lean, the second at faces with at least two planes) but other
  names: that file's own `sumName` and `endName` name every range after a segment's mask row
  (`maskRowRun`, Johnson/Desc/ProofFile/Honest/ForKinds.lean). At the key file's book the two
  owners' names are others (`seatOfLookup`, E2E/KeyBook.lean). So the frame rejects that list at a key
  file's book, by the first test of `lend`. That it is rejected is read off the definitions; no
  theorem states it. A list that takes the owners' names as a parameter is defined in
  Johnson/Desc/ProofFile/Honest/K3/RowOwned.lean (`lookRowOwned`; `keyOwners` is its value for a
  key file's two lookups). This file does not import it. That it states the names of the entries of
  `keyBook` is not shown. See also the limits of E2E/KeyBookHeldK3.lean.
- Whether the owner's coins are available, which is the third test of `lend`, is not shown here. The
  matching test on a book is the fourth of `ProverCoinCounts.clauses` (in the frame): an entry's range lies
  within its owner's count.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookFace

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (Face)
open ProofFile.Honest (Addr Ahead Due runName ownRun endRuns)

/-- The name of the first range of the masked sumcheck at part number p: the first owner's name, the
part's address, the use "sum". -/
def sumName (S : Seat) (p : Nat) : String := runName S.ownName ⟨S.place, p⟩ "sum"

/-- The name of its second range, with the use "ends". second: the mask entries of its end values
are in the second message; the name then has the second owner's name, else the first owner's. -/
def endName (S : Seat) (second : Bool) (p : Nat) : String :=
  runName (if second then S.keyName else S.ownName) ⟨S.place, p⟩ "ends"

/-- The names and counts, in order, that part number p has to state in its field `spends` if it is
the part at the span. -/
def Span.spends (S : Seat) (p : Nat) : Span → List (String × Due)
  | .draw _ _ => []
  | .sum k second => (sumName S p, ⟨0, ownRun k⟩) :: endRuns (endName S second p) k.ends

/-! ## The book's entries have these names and counts -/

/-- Every entry for a list of spans names as its spender a part at the place of S whose number is at
least p, the number of the first span's part. -/
theorem lay_spender (S : Seat) (ps : List Span) (p a b : Nat) :
    ∀ e ∈ layFrom S ps p a b, e.spender.place = S.place ∧ p ≤ e.spender.part := by
  induction ps generalizing p a b with
  | nil => intro e he; cases he
  | cons s l ih =>
    intro e he
    cases s with
    | draw n m =>
      obtain ⟨h1, h2⟩ := ih (p + 1) a b e he
      exact ⟨h1, by omega⟩
    | sum k second =>
      simp only [layFrom, List.mem_append, List.mem_singleton] at he
      rcases he with (rfl | he) | he
      · exact ⟨rfl, Nat.le_refl _⟩
      · split at he
        · cases he
        · split at he <;> (rw [List.mem_singleton] at he; subst he; exact ⟨rfl, Nat.le_refl _⟩)
      · obtain ⟨h1, h2⟩ := ih _ _ _ e he
        exact ⟨h1, by omega⟩

/-- Every entry for a list of spans is marked as spent. -/
theorem lay_once (S : Seat) (ps : List Span) (p a b : Nat) :
    ∀ e ∈ layFrom S ps p a b, e.once = true := by
  induction ps generalizing p a b with
  | nil => intro e he; cases he
  | cons s l ih =>
    intro e he
    cases s with
    | draw n m => exact ih (p + 1) a b e he
    | sum k second =>
      simp only [layFrom, List.mem_append, List.mem_singleton] at he
      rcases he with (rfl | he) | he
      · rfl
      · split at he
        · cases he
        · split at he <;> (rw [List.mem_singleton] at he; subst he; rfl)
      · exact ih _ _ _ e he

/-- The names and counts of the entries of es whose spender is part number q at the place of S, in
the order of es. -/
def namedAt (S : Seat) (es : List Ahead) (q : Nat) : List (String × Due) :=
  (es.filter fun e => e.spender == ⟨S.place, q⟩).map Ahead.named

theorem namedAt_none (S : Seat) (ps : List Span) (p a b q : Nat) (h : q < p) :
    namedAt S (layFrom S ps p a b) q = [] := by
  unfold namedAt
  rw [List.filter_eq_nil_iff.2, List.map_nil]
  intro e he hq
  have h2 := (lay_spender S ps p a b e he).2
  have : e.spender = ⟨S.place, q⟩ := by simpa using hq
  rw [this] at h2
  exact absurd h2 (by simpa using h)

/-- **The entries that name part number p + j have the names and counts of `Span.spends` at span
number j.** -/
theorem named_lay (S : Seat) (ps : List Span) (p a b j : Nat) (s : Span) (hs : ps[j]? = some s) :
    namedAt S (layFrom S ps p a b) (p + j) = s.spends S (p + j) := by
  induction ps generalizing p a b j with
  | nil => cases hs
  | cons t l ih =>
    cases j with
    | zero =>
      obtain rfl : t = s := by simpa using hs
      cases t with
      | draw n m => exact namedAt_none S l (p + 1) a b p (Nat.lt_succ_self p)
      | sum k second =>
        have h0 := namedAt_none S l (p + 1)
          (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
          (b + if second then (k.ends.map (·.n)).getD 0 else 0) p (Nat.lt_succ_self p)
        unfold namedAt at h0 ⊢
        simp only [layFrom, List.filter_append, List.map_append, h0, List.append_nil, Nat.add_zero]
        cases he : k.ends with
        | none => simp [Span.spends, sumName, endRuns, Ahead.named, he]
        | some e => cases second <;> simp [Span.spends, sumName, endName, endRuns, Ahead.named, he]
    | succ j =>
      have hs' : l[j]? = some s := by simpa using hs
      have e : p + (j + 1) = (p + 1) + j := by omega
      cases t with
      | draw n m =>
        rw [e]
        exact ih (p + 1) a b j hs'
      | sum k second =>
        have ih' := ih (p + 1) (a + ownRun k + if second then 0 else (k.ends.map (·.n)).getD 0)
          (b + if second then (k.ends.map (·.n)).getD 0 else 0) j hs'
        rw [← e] at ih'
        unfold namedAt at ih' ⊢
        simp only [layFrom, List.filter_append, List.map_append, ih']
        cases k.ends with
        | none => simp
        | some e => cases second <;> simp

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.lay_once
#print axioms AtPublicFiles.KeyBook.named_lay
#print axioms AtPublicFiles.KeyBook.sumName
#print axioms AtPublicFiles.KeyBook.endName
#print axioms AtPublicFiles.KeyBook.Span.spends
#print axioms AtPublicFiles.KeyBook.lay_spender
#print axioms AtPublicFiles.KeyBook.namedAt
#print axioms AtPublicFiles.KeyBook.namedAt_none
