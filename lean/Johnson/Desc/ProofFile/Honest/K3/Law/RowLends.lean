-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/RowLends.lean: the book's lending (`lendRow`,
Honest/Frame.lean) at a lookup's seated row. Conditional on a test on the book. Definitions with
code, two statements, and theorems.

Terms. Honest/K3/GLOSSARY.md ("book, coins", "half", "part, stretch", "row"). The seated row is the
row of `proverSideOfLookupInChainAtOneOwner` (Honest/K3/Row.lean).

What is shown, by the file's sections.
  1. `lentE`, `coinsE_cut`, `lend_ok`, `PartBook`, `lendPart_ok`, `RowBook`, `lendRow_ok`: for every
     part: a part that takes no coin of its own and carries none, at a book whose entries for it
     are, by name and count, the stretches that it states, each inside its owner's coins, is lent
     these stretches.
  2. `entriesAt`, `runsAt`, `bookFits`: the hypothesis on the book, as a test with code.
  3. `RowLends`, `rowLends`: the statement and its proof. `rowSpent_unlift`: what a lifted row's
     parts spend is what the row's parts spend.
  4. `look_due_first`, `RowLendsFirst`, `rowLendsFirst`: in the first chain the number of coins at
     hand at an address is the book's own. So the hypothesis is a test on public data alone, and the
     lending returns at every run's coins.
  5. `placeFits`, `place_tests`: the three further tests that `chainSteps` (Frame.lean) asks of the
     book at the place.
  Helpers: `Inside` (in 1); `seatPart_facts`, `rowBook_of_fits` (in 3); `find_due` (in 4).
Two texts. `lentE` has, to the letter, the text of `ProofFile.Honest.sliceE` (Honest/Law/Rule/Spent.lean;
this file does not import it). No lemma of this file ties the two.

Hypotheses that remain.
  `bookFits` accepts (in `RowLends` and `RowLendsFirst`); `placeFits` accepts (`h`, in
    `place_tests`).
  `h`: (in `lendPart_ok`) `PartBook`; (in `coinsE_cut`) the cut returns.
  Without a name in front of arrows: the two of `lend_ok` (the entries' names and counts are the
    stated ones; each entry lies inside its owner's coins), `RowBook` in `lendRow_ok`, and the
    test's acceptance in `rowBook_of_fits`.

Imported. Honest/Frame.lean lies beneath this file.

Users. Honest/K3/Law/MasksBook.lean and Honest/K3/Law/RowLendsToy.lean [not in this library] import
this file.

Limits. Conditional: nothing here says that a book passes the test; no theorem of this file shows
it. Honest/K3/Law/RowLendsToy.lean [not in this library] evaluates it at a synthetic book.
Honest/K3/Law/BookAtSites.lean [not in this library] takes it at a book that a maker in other files
makes of a description. By evaluation it
was seen to accept at all ten sites of the shipped small example, at the real small book of the
frame's files (in a printed run, not in this tree). At the full
size no printed run in which it accepts was known to this file's writers when this was written
(searched: their own two folders of printed runs and papers, for the test's own headline; no other
writers').
The test asks nothing on the order of owner and spender in the chain (the book's own tests do:
`ProverCoinCounts.clauses`, Frame.lean) and nothing on which of the owner's coins an entry names: which coin
lies under which hidden value is not spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.RowParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open VerifiableInference.Desc (Place)

variable {V W X : Type}

/-! ## 1 For every part -/

/-- The coins of an entry: of its owner's, from its start on, as many as its count. -/
def lentE (look : Addr → (d : Due) × Cs d) (e : Ahead) : List E :=
  ((coinsE (look e.owner).2).drop e.start.e).take e.count.e

theorem coinsE_cut {d : Due} (c : Cs d) (a n : Due) (x : Cs n) (h : c.cut a n = some x) :
    coinsE x = ((coinsE c).drop a.e).take n.e := by
  unfold Cs.cut at h
  split at h
  · rename_i hle
    obtain rfl := Option.some.inj h
    unfold coinsE
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_take, List.length_drop]
      omega
    · intro i h1 h2
      simp [List.getElem_take, List.getElem_drop]
  · exact nomatch h

/-- An entry lies inside its owner's coins. -/
def Inside (look : Addr → (d : Due) × Cs d) (e : Ahead) : Prop :=
  e.start.f + e.count.f ≤ (look e.owner).1.f ∧ e.start.e + e.count.e ≤ (look e.owner).1.e

theorem lend_ok (look : Addr → (d : Due) × Cs d) : ∀ (l : List Ahead) (ds : List (String × Due)),
    l.map Ahead.named = ds → (∀ e ∈ l, Inside look e) →
    ∃ x, lend look ds l = .ok x ∧ csAllE ds x = l.map (lentE look)
  | [], ds, h, _ => by
    subst h
    exact ⟨(), rfl, rfl⟩
  | a :: l, ds, h, hi => by
    subst h
    obtain ⟨y, hy, hy'⟩ := lend_ok look l _ rfl fun e he => hi e (List.mem_cons_of_mem _ he)
    have hin : a.start.f + a.count.f ≤ (look a.owner).1.f ∧
        a.start.e + a.count.e ≤ (look a.owner).1.e := hi a List.mem_cons_self
    have hcut : ∃ x, (look a.owner).2.cut a.start a.count = some x := by
      unfold Cs.cut
      rw [dif_pos hin]
      exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := hcut
    refine ⟨(x, y), ?_, ?_⟩
    · show lend look ((a.name, a.count) :: l.map Ahead.named) (a :: l) = _
      unfold lend
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false, hx, hy, Except.map]
      rfl
    · show coinsE x :: csAllE _ y = lentE look a :: l.map (lentE look)
      rw [hy', coinsE_cut _ _ _ x hx]
      rfl

/-- **What is asked of the book at one part.** -/
structure PartBook (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (p : Part V W X) (a : Addr) : Prop where
  takes : p.takes = ⟨0, 0⟩
  carries : p.carries = []
  own : dueAt rows a = ⟨0, 0⟩
  once : ∀ e ∈ B.ahead.filter (fun e => e.spender == a), e.once = true
  named : (B.ahead.filter fun e => e.spender == a).map Ahead.named = p.spends
  inside : ∀ e ∈ B.ahead.filter (fun e => e.spender == a), Inside look e

theorem lendPart_ok (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (p : Part V W X) (a : Addr) (h : PartBook B rows look p a) :
    ∃ c, lendPart B rows look a p = .ok c ∧
      csAllE p.spends c.2.1 = (B.ahead.filter fun e => e.spender == a).map (lentE look) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨takes, spends, carries, bad, hid, bs, hs, moves⟩ := p
  simp only at h1 h2 h5
  subst h1
  subst h2
  have f1 : (B.ahead.filter fun e => e.spender == a).filter (·.once) =
      B.ahead.filter fun e => e.spender == a := List.filter_eq_self.2 h4
  have f2 : (B.ahead.filter fun e => e.spender == a).filter (!·.once) = [] :=
    List.filter_eq_nil_iff.2 fun e he => by simp [h4 e he]
  obtain ⟨x, hx, hx'⟩ := lend_ok look _ spends h5 h6
  have hcut : ∃ o, (look a).2.cut ⟨0, 0⟩ ⟨0, 0⟩ = some o := by
    unfold Cs.cut
    rw [dif_pos ⟨Nat.zero_le _, Nat.zero_le _⟩]
    exact ⟨_, rfl⟩
  obtain ⟨o, ho⟩ := hcut
  refine ⟨(o, x, ()), ?_, hx'⟩
  unfold lendPart
  simp only [h3, bne_self_eq_false, Bool.false_eq_true, if_false, ho, f1, f2, hx, Except.bind]
  rfl

/-- The like at every part of a row, from the number j on. -/
def RowBook (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (a : Place) :
    List (Part V W X) → Nat → Prop
  | [], _ => True
  | p :: ps, j => PartBook B rows look p ⟨a, j⟩ ∧ RowBook B rows look a ps (j + 1)

theorem lendRow_ok (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) : ∀ (ps : List (Part V W X)) (j : Nat), RowBook B rows look a ps j →
    ∃ c, lendRow B rows look a ps j = .ok c ∧
      rowSpent ps c = (List.range' j ps.length).map fun i =>
        (B.ahead.filter fun e => e.spender == ⟨a, i⟩).map (lentE look)
  | [], _, _ => ⟨(), rfl, rfl⟩
  | p :: ps, j, h => by
    obtain ⟨c₁, h1, h1'⟩ := lendPart_ok B rows look p ⟨a, j⟩ h.1
    obtain ⟨c₂, h2, h2'⟩ := lendRow_ok B rows look a ps (j + 1) h.2
    refine ⟨(c₁, c₂), ?_, ?_⟩
    · unfold lendRow
      simp only [h1, h2, Except.mapError, Except.bind, Except.map]
    · show csAllE p.spends c₁.2.1 :: rowSpent ps c₂ = _
      rw [h1', h2', List.length_cons, List.range'_succ, List.map_cons]

/-! ## 2 The hypothesis -/

/-- The entries of a book that name the part number i at a place as the part that is handed them. -/
def entriesAt (B : ProverCoinCounts) (p : Place) (i : Nat) : List Ahead :=
  B.ahead.filter fun e => e.spender == ⟨p, i⟩

/-- The stretches that the part of a stage states, by name and count. i: its number in the row.
`runsOf` (Honest/K3/Law/RowPlays.lean) is the text of the field spends of `sumPart`
(Honest/Sum.lean); that the seated part states just these is `seatPart_facts`. -/
def runsAt (a : At) (s : Stage) (i : Nat) : List (String × Due) :=
  match s.call a.face with
  | some k => runsOf (sumName a.place i) (endName a.place i) k
  | none => []

/-- **The hypothesis on the book, as a test with code.** rows: the book's table for the chain. due:
how many coins are at hand at an address. At each part of the lookup's row: the book has no coin of
the part's own; every entry that names it as the part that is given the run is one that is spent;
these entries are, in the book's order, by name and count, the stretches that the part states; and
each lies inside its owner's coins. -/
def bookFits (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : At) : Bool :=
  (stages a.face).zipIdx.all fun x =>
    dueAt rows ⟨a.place, x.2⟩ == ⟨0, 0⟩ && (entriesAt B a.place x.2).all (·.once) &&
      (entriesAt B a.place x.2).map Ahead.named == runsAt a x.1 x.2 &&
      (entriesAt B a.place x.2).all fun e =>
        decide (e.start.f + e.count.f ≤ (due e.owner).f) &&
          decide (e.start.e + e.count.e ≤ (due e.owner).e)

/-! ## 3 The statement -/

/-- **Conditional on `bookFits`: the book lends the seated row its coins**: `lendRow` returns, and
what each part is lent to spend is, stretch by stretch, its entries' own coins. `bookFits` is a
hypothesis on a book that other files make; no theorem of this file shows it.
Honest/K3/Law/BookAtSites.lean [not in this library] takes it at a book that a maker in other files
makes of a description, for a program to
evaluate. A lemma's statement, none of the library's goals. -/
def RowLends : Prop :=
  ∀ (V₁ W₁ X₁ W : Type) (J : LookJobs W) (wit : W₁ → W) (a : At) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d),
    bookFits B rows (fun o => (look o).1) a = true →
    ∃ c, lendRow B rows look a.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts 0 = .ok c ∧
      rowSpent _ c = (List.range (stages a.face).length).map fun i =>
        (entriesAt B a.place i).map (lentE look)

theorem seatPart_facts {V₁ W₁ X₁ W : Type} (J : LookJobs W) (wit : W₁ → W) (a : At)
    (x : Stage × Nat) :
    ((partOf (V := Unit) Rd J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit (fun _ => ())
      fun y _ => y).takes = ⟨0, 0⟩ ∧
    ((partOf (V := Unit) Rd J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit (fun _ => ())
      fun y _ => y).carries = [] ∧
    ((partOf (V := Unit) Rd J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit (fun _ => ())
      fun y _ => y).spends = runsAt a x.1 x.2 := by
  cases hk : x.1.call a.face with
  | none =>
    rw [partOf_none J a x.1 x.2 hk]
    simp only [runsAt, hk]
    exact ⟨rfl, rfl, rfl⟩
  | some k =>
    rw [partOf_some J a x.1 x.2 k hk]
    simp only [runsAt, hk]
    exact ⟨rfl, rfl, rfl⟩

theorem rowBook_of_fits {V₁ W₁ X₁ W : Type} (J : LookJobs W) (wit : W₁ → W) (a : At) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) :
    ∀ (ss : List Stage) (off : Nat),
    ((ss.zipIdx off).all fun x =>
      dueAt rows ⟨a.place, x.2⟩ == ⟨0, 0⟩ && (entriesAt B a.place x.2).all (·.once) &&
        (entriesAt B a.place x.2).map Ahead.named == runsAt a x.1 x.2 &&
        (entriesAt B a.place x.2).all fun e =>
          decide (e.start.f + e.count.f ≤ (look e.owner).1.f) &&
            decide (e.start.e + e.count.e ≤ (look e.owner).1.e)) = true →
    RowBook B rows look a.place ((ss.zipIdx off).map fun x =>
      (partOf (V := Unit) Rd J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit (fun _ => ())
        fun y _ => y) off
  | [], _, _ => trivial
  | s :: ss, off, h => by
    rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h0, hrest⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h0
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h0
    obtain ⟨f1, f2, f3⟩ := seatPart_facts (V₁ := V₁) (X₁ := X₁) J wit a (s, off)
    exact ⟨⟨f1, f2, g1, g2, g3.trans f3.symm, g4⟩, rowBook_of_fits J wit a B rows look ss (off + 1)
      hrest⟩

/-- What a lifted row's parts spend is what the row's parts spend: the coins are the same. -/
theorem rowSpent_unlift {V' W' : Type} (see : V → V') (wit : W → W') :
    ∀ (ps : List (Part V' W' Unit)) (c : RowCoins (ps.map (liftU (X := X) see wit))),
      rowSpent ps (unlift see wit ps c) = rowSpent (ps.map (liftU (X := X) see wit)) c
  | [], _ => rfl
  | p :: ps, c => by
    let c' : p.Coins × RowCoins (ps.map (liftU (X := X) see wit)) := c
    show csAllE p.spends c'.1.2.1 :: rowSpent ps (unlift see wit ps c'.2) =
      csAllE p.spends c'.1.2.1 :: rowSpent (ps.map (liftU (X := X) see wit)) c'.2
    rw [rowSpent_unlift see wit ps c'.2]

/-- **The proof of `RowLends`.** -/
theorem rowLends : RowLends := by
  intro V₁ W₁ X₁ W J wit a B rows look h
  have e : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts =
      ((stages a.face).zipIdx 0).map fun x =>
        (partOf (V := Unit) Rd J a x.1 x.2).lift (fun _ => ()) wit (fun _ => ()) fun x _ => x := by
    simp [proverSideOfLookupInChainAtOneOwner, lookRow, List.map_map, Function.comp_def]
  have key : ∀ (ps : List (Part V₁ W₁ X₁)), ps = ((stages a.face).zipIdx 0).map (fun x =>
      (partOf (V := Unit) Rd J a x.1 x.2).lift (fun _ => ()) wit (fun _ => ()) fun x _ => x) →
      ∃ c, lendRow B rows look a.place ps 0 = .ok c ∧
        rowSpent ps c = (List.range (stages a.face).length).map fun i =>
          (entriesAt B a.place i).map (lentE look) := by
    intro ps hps
    subst hps
    obtain ⟨c, h1, h2⟩ := lendRow_ok B rows look a.place _ 0
      (rowBook_of_fits (V₁ := V₁) (X₁ := X₁) J wit a B rows look (stages a.face) 0 h)
    refine ⟨c, h1, ?_⟩
    rw [h2, List.length_map, List.length_zipIdx, List.range_eq_range']
    rfl
  exact key _ e

/-! ## 4 In the first chain: the hypothesis reads the book alone -/

theorem find_due : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr),
    ((Purse.find? l c a).getD ⟨⟨0, 0⟩, Cs.empty⟩).1 = dueAt l a
  | [], _, _ => rfl
  | (r₁, r₂) :: l, c, a => by
    by_cases h : r₁ = a
    · subst h
      simp [Purse.find?, dueAt]
    · have h1 : (r₁ == a) = false := beq_false_of_ne h
      have h2 : (a == r₁) = false := beq_false_of_ne fun e => h e.symm
      have ih := find_due l c.2 a
      simp only [Purse.find?, h1, Bool.false_eq_true, if_false, dueAt, List.lookup_cons, h2] at ih ⊢
      exact ih

/-- How many coins the first chain may be given at an address is the book's own number: it depends
on no coin. -/
theorem look_due_first (B : ProverCoinCounts) (k : Coins B) (a : Addr) : (k.look 0 a).1 = dueAt B.first a := by
  simp only [Coins.look, beq_self_eq_true, if_true]
  exact find_due B.first k.first a

/-- **Conditional on `bookFits` at the book's own numbers: in the first chain the book lends the
seated row its coins at every run's coins.** The hypothesis is a test on public data alone. This is
a lemma's statement, none of the library's goals. -/
def RowLendsFirst : Prop :=
  ∀ (V₁ W₁ X₁ W : Type) (J : LookJobs W) (wit : W₁ → W) (a : At) (B : ProverCoinCounts),
    bookFits B (B.rowsOf 0) (dueAt B.first) a = true → ∀ k : Coins B,
    ∃ c, lendRow B (B.rowsOf 0) (k.look 0) a.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts 0 = .ok c ∧
      rowSpent _ c = (List.range (stages a.face).length).map fun i =>
        (entriesAt B a.place i).map (lentE (k.look 0))

/-- **The proof of `RowLendsFirst`.** -/
theorem rowLendsFirst : RowLendsFirst := by
  intro V₁ W₁ X₁ W J wit a B h k
  have e : (fun o => (k.look 0 o).1) = dueAt B.first := funext (look_due_first B k)
  exact rowLends V₁ W₁ X₁ W J wit a B (B.rowsOf 0) (k.look 0) (by rw [e]; exact h)

/-! ## 5 The player's other tests on the book at a place -/

/-- **The three further tests that `chainSteps` (Honest/Frame.lean) asks of the book at a place at
which a half stands**, at the lookup's row, as a test with code: the book's cut is the stages'
rounds; the book has no row, and no entry's spender, at a part's number that the row does not have.
-/
def placeFits (B : ProverCoinCounts) (rows : List (Addr × Due)) (a : At) : Bool :=
  B.cuts.lookup a.place == some ((stages a.face).map (Stage.rounds a.face)) &&
    !(rows.any fun r => r.1.place == a.place && decide ((stages a.face).length ≤ r.1.part)) &&
    !(B.ahead.any fun e =>
      e.spender.place == a.place && decide ((stages a.face).length ≤ e.spender.part))

/-- Conditional on `placeFits`: these three tests of `chainSteps` do not reject the seated row. -/
theorem place_tests {V₁ W₁ X₁ W : Type} (J : LookJobs W) (wit : W₁ → W) (a : At) (B : ProverCoinCounts)
    (rows : List (Addr × Due)) (h : placeFits B rows a = true) :
    (B.cuts.lookup a.place != some ((proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts.map
      (·.moves.length))) = false ∧
    (rows.any fun r => r.1.place == a.place &&
      decide ((proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts.length ≤ r.1.part)) = false ∧
    (B.ahead.any fun e => e.spender.place == a.place &&
      decide ((proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts.length ≤ e.spender.part)) =
      false := by
  have hl : (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) Rd J wit a).parts.length = (stages a.face).length := by
    have := congrArg List.length (proverSideOfLookupInChainAtOneOwner_moves (V₁ := V₁) (X₁ := X₁) Rd J wit a)
    simpa using this
  simp only [placeFits, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rw [proverSideOfLookupInChainAtOneOwner_moves, hl]
  exact ⟨by rw [h.1.1]; simp, h.1.2, h.2⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.place_tests
#print axioms ProofFile.Honest.K3.Law.look_due_first
#print axioms ProofFile.Honest.K3.Law.rowLendsFirst
#print axioms ProofFile.Honest.K3.Law.lend_ok
#print axioms ProofFile.Honest.K3.Law.lendPart_ok
#print axioms ProofFile.Honest.K3.Law.lendRow_ok
#print axioms ProofFile.Honest.K3.Law.rowSpent_unlift
#print axioms ProofFile.Honest.K3.Law.rowLends
#print axioms ProofFile.Honest.K3.Law.coinsE_cut
#print axioms ProofFile.Honest.K3.Law.seatPart_facts
#print axioms ProofFile.Honest.K3.Law.rowBook_of_fits
#print axioms ProofFile.Honest.K3.Law.find_due
