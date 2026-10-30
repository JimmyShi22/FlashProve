-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/OwnedLends.lean: the honest side of the kind "lookup" (K3):
THE
BOOK'S LENDING (`lendRow`, Honest/Frame.lean) AT THE SEATED ROW WITH A LETTER FOR THE OWNERS OF ITS
STRETCHES (Honest/K3/RowOwned.lean): CONDITIONAL ON A TEST ON THE BOOK. Definitions with code and
theorems.

  `runsAtOwned`, `runsAtOwned_one`     the stretches that a stage's part states, by name and count;
  at one
                                    owner they are those of Honest/K3/Law/RowLends.lean
  `bookFitsOwned`, `bookFitsOwned_one`   THE PREMISE, as a test with code; at one owner it is that
  file's
  `ownedPart_facts`, `rowBook_owned`   what the general law on a part's lending asks
  `rowLendsOwned`                   **the book lends the owned seated row its coins**

It stands over Honest/K3/Law/RowLends.lean's laws `lendRow_ok`, `PartBook`, `RowBook`, which are
general in
the part.

Limits. CONDITIONAL ON `bookFitsOwned`. HERE IT IS NOT SEEN TO ACCEPT AT A REAL BOOK OF THE KEY
FILE (see `keyBookFitsTheOwnedRow`, E2E/Lookup/Key/LookupSidePaysAtTheKeyBook.lean): no
book that a maker makes of that chain is at hand here. A synthetic book of this side's own making
would
be no member that counts. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.RowOwned
import Johnson.Desc.ProofFile.Honest.K3.Law.RowLends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open ProofFile.Honest.K3.Law

/-! ## 1 The premise -/

/-- The stretches that the part of a stage states, by name and count. i: its number in the row. -/
def runsAtOwned (o : Owners) (a : At) (s : Stage) (i : Nat) : List (String × Due) :=
  match s.call a.face with
  | some k => runsOf (sumNameBy o s a.place i) (endNameBy o s a.place i) k
  | none => []

/-- At one owner they are those of Honest/K3/Law/RowLends.lean. -/
theorem runsAtOwned_one (a : At) (s : Stage) (i : Nat) :
    runsAtOwned oneOwner a s i = runsAt a s i := rfl

/-- **THE PREMISE ON THE BOOK, as a test with code**: Honest/K3/Law/RowLends.lean's `bookFits`, with
the
stretches' names by the letter. -/
def bookFitsOwned (o : Owners) (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : At) :
    Bool :=
  (stages a.face).zipIdx.all fun x =>
    dueAt rows ⟨a.place, x.2⟩ == ⟨0, 0⟩ && (entriesAt B a.place x.2).all (·.once) &&
      (entriesAt B a.place x.2).map Ahead.named == runsAtOwned o a x.1 x.2 &&
      (entriesAt B a.place x.2).all fun e =>
        decide (e.start.f + e.count.f ≤ (due e.owner).f) &&
          decide (e.start.e + e.count.e ≤ (due e.owner).e)

/-- At one owner it is that file's test. -/
theorem bookFitsOwned_one (B : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : At) :
    bookFitsOwned oneOwner B rows due a = bookFits B rows due a := rfl

/-! ## 2 The lending -/

/-- A seated part of the owned row takes no coin of its own, carries none, and states just these
stretches. -/
theorem ownedPart_facts {V₁ W₁ X₁ W : Type} (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W)
    (a : At) (x : Stage × Nat) :
    ((partOfOwned (V := Unit) o R J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit
      (fun _ => ()) fun y _ => y).takes = ⟨0, 0⟩ ∧
    ((partOfOwned (V := Unit) o R J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit
      (fun _ => ()) fun y _ => y).carries = [] ∧
    ((partOfOwned (V := Unit) o R J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit
      (fun _ => ()) fun y _ => y).spends = runsAtOwned o a x.1 x.2 := by
  unfold partOfOwned runsAtOwned
  cases x.1.call a.face with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some k => exact ⟨rfl, rfl, rfl⟩

/-- What the general law on a row's lending asks, from the test. CONDITIONAL ON the test, stage by
stage. -/
theorem rowBook_owned {V₁ W₁ X₁ W : Type} (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W)
    (a : At) (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) :
    ∀ (ss : List Stage) (off : Nat),
    ((ss.zipIdx off).all fun x =>
      dueAt rows ⟨a.place, x.2⟩ == ⟨0, 0⟩ && (entriesAt B a.place x.2).all (·.once) &&
        (entriesAt B a.place x.2).map Ahead.named == runsAtOwned o a x.1 x.2 &&
        (entriesAt B a.place x.2).all fun e =>
          decide (e.start.f + e.count.f ≤ (look e.owner).1.f) &&
            decide (e.start.e + e.count.e ≤ (look e.owner).1.e)) = true →
    RowBook B rows look a.place ((ss.zipIdx off).map fun x =>
      (partOfOwned (V := Unit) o R J a x.1 x.2).lift (V := V₁) (X := X₁) (fun _ => ()) wit
        (fun _ => ()) fun y _ => y) off
  | [], _, _ => trivial
  | s :: ss, off, h => by
    rw [List.zipIdx_cons, List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h0, hrest⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h0
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := h0
    obtain ⟨f1, f2, f3⟩ := ownedPart_facts (V₁ := V₁) (X₁ := X₁) o R J wit a (s, off)
    exact ⟨⟨f1, f2, g1, g2, g3.trans f3.symm, g4⟩,
      rowBook_owned o R J wit a B rows look ss (off + 1) hrest⟩

/-- **THE BOOK LENDS THE OWNED SEATED ROW ITS COINS**: `lendRow` returns, and what each part is lent
to
spend is, stretch by stretch, its entries' own coins. CONDITIONAL ON `bookFitsOwned`: A PREMISE ON A
BOOK
THAT ANOTHER HAND MAKES; seen to accept at no real book. No member is typed. -/
theorem rowLendsOwned {V₁ W₁ X₁ W : Type} (o : Owners) (R : Reads) (J : LookJobs W) (wit : W₁ → W)
    (a : At) (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (h : bookFitsOwned o B rows (fun x => (look x).1) a = true) :
    ∃ c, lendRow B rows look a.place
        (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts 0 = .ok c ∧
      rowSpent _ c = (List.range (stages a.face).length).map fun i =>
        (entriesAt B a.place i).map (lentE look) := by
  have e : (proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) o R J wit a).parts =
      ((stages a.face).zipIdx 0).map fun x =>
        (partOfOwned (V := Unit) o R J a x.1 x.2).lift (fun _ => ()) wit (fun _ => ())
          fun x _ => x := by
    simp [proverSideOfLookupInChain, lookRowOwned, List.map_map, Function.comp_def]
  have key : ∀ (ps : List (Part V₁ W₁ X₁)), ps = ((stages a.face).zipIdx 0).map (fun x =>
      (partOfOwned (V := Unit) o R J a x.1 x.2).lift (fun _ => ()) wit (fun _ => ())
        fun x _ => x) →
      ∃ c, lendRow B rows look a.place ps 0 = .ok c ∧
        rowSpent ps c = (List.range (stages a.face).length).map fun i =>
          (entriesAt B a.place i).map (lentE look) := by
    intro ps hps
    subst hps
    obtain ⟨c, h1, h2⟩ := lendRow_ok B rows look a.place _ 0
      (rowBook_owned (V₁ := V₁) (X₁ := X₁) o R J wit a B rows look (stages a.face) 0 h)
    refine ⟨c, h1, ?_⟩
    rw [h2, List.length_map, List.length_zipIdx, List.range_eq_range']
    rfl
  exact key _ e

#print axioms ProofFile.Honest.K3.Parts.runsAtOwned_one
#print axioms ProofFile.Honest.K3.Parts.bookFitsOwned_one
#print axioms ProofFile.Honest.K3.Parts.ownedPart_facts
#print axioms ProofFile.Honest.K3.Parts.rowBook_owned
#print axioms ProofFile.Honest.K3.Parts.rowLendsOwned

end ProofFile.Honest.K3.Parts
