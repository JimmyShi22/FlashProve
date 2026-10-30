-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookLends.lean: sufficient conditions under which the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written, and the
functions that run it) gives the parts of a prover their coins. The main theorem, `lendRow_ok`: if
every part in the list of parts at a place states exactly what a book of coins has for it, and the
coins in question are available, then the frame's `lendRow` returns coins and not an error. A second
theorem, `look_due`, says how many coins each chain may be given at an address. Both are general in
the book, the parts and the coins. Definitions and theorems. `key_lends`
(E2E/KeyBookLendsNamed.lean) applies both theorems to the key file's book at the full size.

Terms, of the frame unless another file is named. Coins are the prover's random field elements. A
count (`Due`) is a number of coins in each of the two fields; `Cs d` is the type of coins at the
count d. A part (`Part`) is the prover's side of some consecutive rounds of a sub-protocol. It
states its own count (`takes`) and the names and counts of the blocks of other parts' coins that it
spends (`spends`) and carries (`carries`). A place (`Place`, Johnson/Desc/Block.lean) is a
sub-protocol's label; an address (`Addr`) is a place and a part's number, from 0, in the list of
parts there. A book (`ProverCoinCounts`) is the public table of coins. It has, for each of the three chains of
sub-protocols (the first, the shared, the second), a table whose rows are an address and a count; a
list of entries; and cuts, which this file does not read. An entry (`Ahead`) is a named block of the
coins of one part, its owner (the field `owner`): the range of `count` coins from number `start` on.
One part, its spender (the field `spender`), is given that block too; the field `once` marks the
entry as spent (true) or as carried (false). The parameter look is a function from an address to the
coins that are available there, with their count.

Why. The frame's `run` returns an error unless `lendRow` returns coins at every place at which a
prover's side is defined (through `ready` and `chainSteps`). `lendRow` calls `lendPart` for each
part, and `lendPart` calls `lend` twice: for `spends` with the entries marked as spent, and for
`carries` with those marked as carried. An error is returned in four cases: the part's own count is
not the count at its address in the table rows; the part's own coins are not available; the names
and counts that the part states are not, one by one and in the book's order, those of the entries
that name it as their spender; an entry's range is not within those of its owner's coins that are
available. The theorems give hypotheses that exclude the four cases.

  `lendRow_ok`: at a book B, a table rows, a function look and a place a, under the three hypotheses
    below: for every list ps of parts and every number j, `lendRow B rows look a ps j` returns
    coins. j is the number of the first part of ps
  `lendPart_ok`: the same for one part p at one address a: `lendPart B rows look a p` returns coins,
    if p is `Stated` at a, the count at a in rows is, in each field, at most the count of `look a`,
    and every entry with the spender a is `Within look`
  `look_due`: at every book B, coins c of a run (`Coins B`), number ch and address a: the coins
    `c.look ch a`, which are what chain number ch, from 0, may be given at a, have the count
    `dueAt (seen B ch) a`. That is the count in the first row at a in the tables that the chain
    sees, and 0 in both fields if there is no such row
  `hasFor B rows a`: a definition: what the book has for the part at the address a, a triple: the
    count at a in rows (`dueAt`); the names and counts (`Ahead.named`) of the entries with the
    spender a that are marked as spent, in the book's order; the same for those marked as carried
  `Stated B rows a p`: a definition: the part p states exactly that:
    `(p.takes, p.spends, p.carries)` is `hasFor B rows a`
  `Within look e`: a definition: the range of the entry e lies within the coins that look returns at
    the owner of e: in each field, `start` plus `count` is at most their count
  `seen B ch`: a definition: the tables that chain number ch sees: `B.first` at 0; `B.shared` at 1;
    at every other ch, which the frame counts as the second chain, the three tables appended in the
    order first, shared, second
  `lend_ok`, `lend_ok'`: for a list of entries that are all `Within look`, `lend` returns coins at
    the entries' own names and counts; in `lend_ok'` the list of names and counts is a variable,
    with a hypothesis that it is equal to the entries' own
  `cut_some`: `Cs.cut` returns coins where, in each field, the first number plus the length is at
    most the count
  `find_due`, `getD_due`: the count of what `Purse.find?` returns at an address of a table is what
    `List.lookup` returns there; and for an optional value o of coins with their count: the count of
    o, with no coin as the default, is the count in o, with 0 in both fields as the default

By what. No lemma of another file of this library is called: the proofs unfold the frame's
definitions `Cs.cut`, `lend`, `lendPart`, `lendRow`, `Coins.look`, `sharedLook`, `Purse.find?` and
`dueAt`. `lendRow_ok` goes through the list and calls `lendPart_ok` for each part. `lendPart_ok`
gets the part's own coins by `cut_some` and the two lists of blocks by `lend_ok'`. `look_due` goes
by cases on ch, by `getD_due` and `find_due`.

Hypotheses of `lendRow_ok`. hown: at every address at the place a, not only at the addresses of the
parts of ps, the count in rows is, in each field, at most the count of what look returns there. hw:
every entry of the book whose spender is at the place a is `Within look`. The third has no name in
the statement: the part at position i of ps is `Stated` at the address `⟨a, j + i⟩`.

Limits.
- Coins only. Before it calls `lendRow`, `chainSteps` makes other tests, on which nothing is shown
  here: that the sub-protocol has as many lists of oracle messages as rounds, that the list of parts
  has as many rounds as the sub-protocol, that it is cut into parts as the book says, and that it
  has a part for every row and every entry that the book has at its place.
- The hypotheses are proved of no book and of no part here. The proof of `key_lends` shows hown and
  hw at its book. Statements that a part is `Stated` are in E2E/KeyBookHeldK1.lean,
  E2E/KeyBookHeldK1Jobs.lean and E2E/KeyBookHeldHash.lean.
- `look_due` gives a count in `seen B ch`, while the frame calls `lendRow` at the table
  `B.rowsOf ch`. The two are the same table at ch = 0 and 1. From 2 on `B.rowsOf ch` is `B.second`
  only: there the two counts at an address are equal if the address has no row in `B.first` and
  `B.shared`, which is not shown here.
- Nothing on what a part does with its coins.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place)
open ProofFile.Honest

variable {V W X : Type}

/-! ## 1 What the book has for a part -/

/-- What the book has for the part at the address a: its count in rows; the names and counts of the
entries that it spends; those of the entries that it carries. rows: a table of addresses and counts;
the frame passes the book's table for the part's chain (`ProverCoinCounts.rowsOf`). -/
def hasFor (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : Addr) :
    Due × List (String × Due) × List (String × Due) :=
  (dueAt rows a, ((B.ahead.filter fun e => e.spender == a).filter (·.once)).map Ahead.named,
    ((B.ahead.filter fun e => e.spender == a).filter (!·.once)).map Ahead.named)

/-- The part states exactly what the book has for it. -/
def Stated (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : Addr) (p : Part V W X) : Prop :=
  (p.takes, p.spends, p.carries) = hasFor B rows a

/-- The entry's range lies within the coins that `look` returns at the entry's owner. -/
def Within (look : Addr → (d : Due) × Cs d) (e : Ahead) : Prop :=
  e.start.f + e.count.f ≤ (look e.owner).1.f ∧ e.start.e + e.count.e ≤ (look e.owner).1.e

/-! ## 2 The frame gives the parts their coins -/

theorem cut_some {d : Due} (c : Cs d) (a n : Due) (h : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e) :
    ∃ x, c.cut a n = some x := by
  unfold Cs.cut
  rw [dif_pos h]
  exact ⟨_, rfl⟩

theorem lend_ok (look : Addr → (d : Due) × Cs d) : ∀ l : List Ahead, (∀ e ∈ l, Within look e) →
    ∃ c, lend look (l.map Ahead.named) l = .ok c
  | [], _ => ⟨(), rfl⟩
  | a :: l, h => by
    obtain ⟨x, hx⟩ := cut_some (look a.owner).2 a.start a.count (h a List.mem_cons_self)
    obtain ⟨y, hy⟩ := lend_ok look l fun e he => h e (List.mem_cons_of_mem _ he)
    refine ⟨(x, y), ?_⟩
    show lend look (a.named :: l.map Ahead.named) (a :: l) = _
    unfold lend
    have h1 : (a.name != a.named.1) = false := by simp
    have h2 : (a.count != a.named.2) = false := by simp
    simp only [h1, h2, Bool.false_eq_true, if_false]
    rw [hx, hy]
    rfl

theorem lend_ok' (look : Addr → (d : Due) × Cs d) (l : List Ahead) (ds : List (String × Due))
    (e : ds = l.map Ahead.named) (h : ∀ e ∈ l, Within look e) : ∃ c, lend look ds l = .ok c := by
  subst e
  exact lend_ok look l h

/-- A part that states exactly what the book has for it is given its coins, if `look` returns at
least its own count of coins at its address (hown) and every entry that names it as its spender is
`Within look` (hw). -/
theorem lendPart_ok (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) (hs : Stated B rows a p)
    (hown : (dueAt rows a).f ≤ (look a).1.f ∧ (dueAt rows a).e ≤ (look a).1.e)
    (hw : ∀ e ∈ B.ahead, e.spender = a → Within look e) :
    ∃ c, lendPart B rows look a p = .ok c := by
  unfold Stated hasFor at hs
  obtain ⟨h1, h2, h3⟩ : p.takes = dueAt rows a ∧ p.spends = _ ∧ p.carries = _ := by
    have e1 := congrArg (·.1) hs
    have e2 := congrArg (·.2.1) hs
    have e3 := congrArg (·.2.2) hs
    exact ⟨e1, e2, e3⟩
  have hm : ∀ e ∈ B.ahead.filter (fun e => e.spender == a), Within look e := fun e he =>
    hw e (List.mem_filter.1 he).1 (beq_iff_eq.1 (List.mem_filter.1 he).2)
  obtain ⟨own, ho⟩ := cut_some (look a).2 ⟨0, 0⟩ p.takes (by
    rw [h1]
    exact ⟨by simpa using hown.1, by simpa using hown.2⟩)
  obtain ⟨sp, hsp⟩ := lend_ok' look _ p.spends h2 fun e he => hm e (List.mem_filter.1 he).1
  obtain ⟨ca, hca⟩ := lend_ok' look _ p.carries h3 fun e he => hm e (List.mem_filter.1 he).1
  refine ⟨(own, sp, ca), ?_⟩
  unfold lendPart
  have ht : (p.takes != dueAt rows a) = false := by simp [h1]
  simp only [ht, Bool.false_eq_true, if_false]
  rw [ho]
  show ((lend look p.spends _).bind fun sp =>
    (lend look p.carries _).map fun ca => (own, sp, ca)) = _
  rw [hsp, hca]
  rfl

/-- **A list of parts that each state exactly what the book has for them is given its coins.** j:
the first part's number. The comment at the top of this file lists the hypotheses. -/
theorem lendRow_ok (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place)
    (hown : ∀ j, (dueAt rows ⟨a, j⟩).f ≤ (look ⟨a, j⟩).1.f ∧
      (dueAt rows ⟨a, j⟩).e ≤ (look ⟨a, j⟩).1.e)
    (hw : ∀ e ∈ B.ahead, e.spender.place = a → Within look e) :
    ∀ (ps : List (Part V W X)) (j : Nat),
      (∀ i p, ps[i]? = some p → Stated B rows ⟨a, j + i⟩ p) →
      ∃ r, lendRow B rows look a ps j = .ok r
  | [], _, _ => ⟨(), rfl⟩
  | p :: ps, j, hs => by
    obtain ⟨c, hc⟩ := lendPart_ok B rows look ⟨a, j⟩ p (hs 0 p rfl) (hown j)
      fun e he hsp => hw e he (by rw [hsp])
    obtain ⟨r, hr⟩ := lendRow_ok B rows look a hown hw ps (j + 1) fun i q hq => by
      have := hs (i + 1) q hq
      rwa [Nat.add_comm i 1, ← Nat.add_assoc] at this
    refine ⟨(c, r), ?_⟩
    unfold lendRow
    rw [hc, hr]
    rfl

/-! ## 3 How many coins a chain may be given -/

/-- The tables that chain number ch, from 0, sees: its own at 0 and 1, all three at any other ch. -/
def seen (B : ProverCoinCounts) (ch : Nat) : List (Addr × Due) :=
  if ch == 0 then B.first else if ch == 1 then B.shared else B.first ++ B.shared ++ B.second

theorem find_due : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr),
    (Purse.find? l c a).map (·.1) = l.lookup a
  | [], _, _ => rfl
  | r :: l, c, a => by
    unfold Purse.find?
    rw [List.lookup_cons]
    by_cases h : r.1 = a
    · simp [h]
    · have h' : (a == r.1) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
      have h'' : (r.1 == a) = false := beq_eq_false_iff_ne.2 h
      simp only [h', h'', Bool.false_eq_true, if_false]
      exact find_due l c.2 a

theorem getD_due (o : Option ((d : Due) × Cs d)) :
    (o.getD ⟨⟨0, 0⟩, Cs.empty⟩).1 = (o.map (·.1)).getD ⟨0, 0⟩ := by
  cases o <;> rfl

/-- **The coins that a chain may be given at an address have the count of the first row at that
address in the tables that the chain sees**; 0 in both fields if there is no such row. -/
theorem look_due {B : ProverCoinCounts} (c : Coins B) (ch : Nat) (a : Addr) :
    (c.look ch a).1 = dueAt (seen B ch) a := by
  unfold Coins.look seen dueAt
  by_cases h0 : ch = 0
  · simp only [h0, beq_self_eq_true, if_true]
    rw [getD_due, find_due]
  · by_cases h1 : ch = 1
    · subst h1
      simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, if_false,
        beq_self_eq_true, if_true]
      unfold sharedLook
      rw [getD_due, find_due]
    · have e0 : (ch == 0) = false := beq_eq_false_iff_ne.2 h0
      have e1 : (ch == 1) = false := beq_eq_false_iff_ne.2 h1
      simp only [e0, e1, Bool.false_eq_true, if_false]
      rw [getD_due, List.lookup_append, List.lookup_append, ← find_due B.first c.first,
        ← find_due B.shared c.shared, ← find_due B.second c.second]
      cases Purse.find? B.first c.first a <;> cases Purse.find? B.shared c.shared a <;>
        cases Purse.find? B.second c.second a <;> rfl

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.lend_ok
#print axioms AtPublicFiles.KeyBook.lendPart_ok
#print axioms AtPublicFiles.KeyBook.lendRow_ok
#print axioms AtPublicFiles.KeyBook.look_due
#print axioms AtPublicFiles.KeyBook.hasFor
#print axioms AtPublicFiles.KeyBook.Stated
#print axioms AtPublicFiles.KeyBook.Within
#print axioms AtPublicFiles.KeyBook.cut_some
#print axioms AtPublicFiles.KeyBook.lend_ok'
#print axioms AtPublicFiles.KeyBook.seen
#print axioms AtPublicFiles.KeyBook.find_due
#print axioms AtPublicFiles.KeyBook.getD_due
