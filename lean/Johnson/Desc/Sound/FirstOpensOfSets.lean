-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/FirstOpensOfSets.lean: FROM TWO SETS THAT AGREE TO TWO LISTS THAT AGREE: what a
  round of
the last chain opens, by number over the file, is the list of the numbers of the trees at given
  places
of a book, IN ORDER.

Why. A law of a proximity test on the last chain promises of its first switch: "the trees that the
declared openings name are, in turn, those at the places ts of the book, each sent in front of the
stretch". The last chain's own test on taken sources gives two SETS of pairs (sending chain, number
there) that agree; not the order, not how often. The order comes from two sides: the tests on the
plan say that in every declared round the opened trees' places rise strictly
(`BookPlan.opened_trees_in_order`, Johnson/Desc/BookPlanLaws.lean; `treeSharingOk` is a clause of
  `planOk`);
the book's places ts rise. Two lists that rise strictly and have the same members are one list.
  `earlier_asymm`     of two places at most one stands before the other
  `rising_eq`         two strictly rising lists of places with the same members are equal (the
    library's
                      `List.Pairwise.eq_of_mem_iff`)
  `numAt_place`       a source's number over the file is the makers' number of its place
  `opens_eq_places`   the numbers: from the two risings and the sets
  `sets_of_tied`      the sets, from what the test on taken sources says and a law on the plan's
    list
  `firstOpens_lists`  **both halves of the promise, at lists as letters**: from `F.data`'s yes, the
                      rising of the openings, and three named premises
  `firstOpens_round`  the same where the openings are one declared round's: the rising is paid by
                      `F.treeSharingOk = true`
THE NAMED PREMISES. (α) `up`: along ts the places pl z rise strictly (a fact on the book's make: the
first chain's trees in their order of sending, then the shared chain's). (β) `taken`: every one of
the openings is of a tree that is taken over. `sets`: the openings' places and the places pl z, z
in ts, are the same as sets.
  Three `example`s: the lists' rule at a toy list; a control: the same openings in another order.
Limits. Combinatorics on lists of numbers; nothing on soundness. The three premises are not paid
  here;
THAT THEY HOLD TOGETHER AT THE RELEASE's PLAN AND A RECORD THAT RUNS HAS NOT BEEN TESTED.
pl is a letter: that pl z is the place of the tree at z in a record's book is the caller's.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TakenBelowOfData
import Johnson.Desc.BookPlanLaws
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (wholeNo)
open BookPlan (treePlace earlierPlace)

/-- "Stands before", as a relation. -/
abbrev Before (a b : ℕ × ℕ) : Prop := earlierPlace a b = true

theorem before_iff (a b : ℕ × ℕ) : Before a b ↔ a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
  unfold Before earlierPlace
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]

theorem earlier_asymm {a b : ℕ × ℕ} (h : Before a b) (h' : Before b a) : False := by
  rw [before_iff] at h h'
  omega

theorem earlier_irrefl {a : ℕ × ℕ} (h : Before a a) : False := earlier_asymm h h

instance : Std.Antisymm Before := ⟨fun _ _ h h' => (earlier_asymm h h').elim⟩
instance : Std.Irrefl Before := ⟨fun _ h => earlier_irrefl h⟩

/-- **Two strictly rising lists of places with the same members are equal**: the library's
`List.Pairwise.eq_of_mem_iff` at "stands before". -/
theorem rising_eq {l m : List (ℕ × ℕ)} (hl : l.Pairwise Before) (hm : m.Pairwise Before)
    (h : ∀ x, x ∈ l ↔ x ∈ m) : l = m :=
  List.Pairwise.eq_of_mem_iff hl hm h

/-- A source's number over the file, met on the last chain, is the makers' number of its place. -/
theorem numAt_place (t₁ t₂ : ℕ) : ∀ s : Fmt.TreeSource, numAt t₁ t₂ 2 s = wholeNo t₁ t₂ (treePlace 2 s)
  | .own _ => rfl
  | .taken 0 _ => rfl
  | .taken 1 _ => rfl
  | .taken (_ + 2) _ => rfl

/-- **The numbers, in order**: from the two risings and the sets. -/
theorem opens_eq_places (t₁ t₂ : ℕ) (opens : List (Fmt.Shape × Fmt.TreeSource)) (ts : List ℕ)
    (pl : ℕ → ℕ × ℕ) (rise : (opens.map fun o => treePlace 2 o.2).Pairwise Before)
    (up : (ts.map pl).Pairwise Before)
    (sets : ∀ x, x ∈ (opens.map fun o => treePlace 2 o.2) ↔ x ∈ ts.map pl) :
    (opens.map fun o => numAt t₁ t₂ 2 o.2) = ts.map fun z => wholeNo t₁ t₂ (pl z) := by
  have e := congrArg (List.map (wholeNo t₁ t₂)) (rising_eq rise up sets)
  rw [List.map_map, List.map_map] at e
  refine Eq.trans (List.map_congr_left fun o _ => ?_) e
  exact numAt_place t₁ t₂ o.2

/-- **The sets**, from what the test on taken sources says of all the rounds of a block ((a), (b)),
and a law on the plan's list: the openings in hand are among these rounds' openings (`part`), are
all of trees that are taken over (`taken`), and hold every such opening of these rounds (`all`).
tk: the pairs that the test has read off the book. -/
theorem sets_of_tied (rounds : List Fmt.DeclaredRound) (opens : List (Fmt.Shape × Fmt.TreeSource))
    (tk : List (ℕ × ℕ))
    (a : ∀ x ∈ tk, ∃ r ∈ rounds, ∃ o ∈ r.opens, o.2 = .taken x.1 x.2)
    (b : ∀ r ∈ rounds, ∀ o ∈ r.opens, ∀ c n, o.2 = .taken c n → (c, n) ∈ tk)
    (part : ∀ o ∈ opens, ∃ r ∈ rounds, o ∈ r.opens)
    (taken : ∀ o ∈ opens, ∃ c n, o.2 = .taken c n)
    (all : ∀ r ∈ rounds, ∀ o ∈ r.opens, (∃ c n, o.2 = .taken c n) → o ∈ opens) :
    ∀ x, x ∈ (opens.map fun o => treePlace 2 o.2) ↔ x ∈ tk := by
  intro x
  constructor
  · intro hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r, hr, hor⟩ := part o ho
    obtain ⟨c, n, e⟩ := taken o ho
    rw [e]
    exact b r hr o hor c n e
  · intro hx
    obtain ⟨r, hr, o, ho, e⟩ := a x hx
    refine List.mem_map.2 ⟨o, all r hr o ho ⟨_, _, e⟩, ?_⟩
    rw [e]
    rfl

variable {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}

/-- **Both halves of the promise, at lists as letters.** -/
theorem firstOpens_lists (h : F.data file = .ok D) (opens : List (Fmt.Shape × Fmt.TreeSource))
    (decl : ∀ o ∈ opens, ∃ r ∈ F.roundsDeclaredByBlocks.2.2, o ∈ r.opens)
    (rise : (opens.map fun o => treePlace 2 o.2).Pairwise Before)
    (ts : List ℕ) (pl : ℕ → ℕ × ℕ) (up : (ts.map pl).Pairwise Before)
    (taken : ∀ o ∈ opens, ∃ c n, o.2 = .taken c n)
    (sets : ∀ x, x ∈ (opens.map fun o => treePlace 2 o.2) ↔ x ∈ ts.map pl)
    (base : ℕ) (hb : F.t₁ + F.t₂ ≤ base) :
    (opens.map fun o => numAt F.t₁ F.t₂ 2 o.2) = ts.map (fun z => wholeNo F.t₁ F.t₂ (pl z)) ∧
      ∀ z ∈ ts, wholeNo F.t₁ F.t₂ (pl z) < base := by
  refine ⟨opens_eq_places _ _ opens ts pl rise up sets, fun z hz => ?_⟩
  obtain ⟨o, ho, e⟩ := List.mem_map.1 ((sets (pl z)).2 (List.mem_map.2 ⟨z, hz, rfl⟩))
  obtain ⟨r, hr, hor⟩ := decl o ho
  obtain ⟨c, n, e'⟩ := taken o ho
  have k := taken_below_of_data h r hr o hor c n e'
  rw [numAt_place, e] at k
  exact Nat.lt_of_lt_of_le k hb

/-- **The same where the openings are one declared round's**: the rising is paid by the tests on the
plan. -/
theorem firstOpens_round (h : F.data file = .ok D) (hk : F.treeSharingOk = true) (r : Fmt.DeclaredRound)
    (hr : r ∈ F.roundsDeclaredByBlocks.2.2) (ts : List ℕ) (pl : ℕ → ℕ × ℕ) (up : (ts.map pl).Pairwise Before)
    (taken : ∀ o ∈ r.opens, ∃ c n, o.2 = .taken c n)
    (sets : ∀ x, x ∈ (r.opens.map fun o => treePlace 2 o.2) ↔ x ∈ ts.map pl)
    (base : ℕ) (hb : F.t₁ + F.t₂ ≤ base) :
    (r.opens.map fun o => numAt F.t₁ F.t₂ 2 o.2) = ts.map (fun z => wholeNo F.t₁ F.t₂ (pl z)) ∧
      ∀ z ∈ ts, wholeNo F.t₁ F.t₂ (pl z) < base :=
  firstOpens_lists h r.opens (fun _ ho => ⟨r, hr, ho⟩)
    ((BookPlan.opened_trees_in_order hk).2.2 r hr) ts pl up taken sets base hb

/-! ## The lists' rule is not empty, and its first premise can fail -/

/-- Three openings: two trees of the first chain, one of the shared chain. -/
def toyOpens : List (Fmt.Shape × Fmt.TreeSource) :=
  [(⟨0, 1, false, 3⟩, .taken 0 3), (⟨0, 1, false, 5⟩, .taken 0 5), (⟨0, 1, false, 0⟩, .taken 1 0)]

/-- A book's places 2, 4, 7 hold these trees. -/
def toyPl : ℕ → ℕ × ℕ
  | 2 => (0, 3)
  | 4 => (0, 5)
  | _ => (1, 0)

/-- At ten and four trees: the numbers over the file are 3, 5 and 10, in the book's order. -/
example : (toyOpens.map fun o => numAt 10 4 2 o.2) = [3, 5, 10] ∧
    ([2, 4, 7].map fun z => wholeNo 10 4 (toyPl z)) = [3, 5, 10] :=
  ⟨rfl, rfl⟩

example :
    (toyOpens.map fun o => numAt 10 4 2 o.2) = [2, 4, 7].map fun z => wholeNo 10 4 (toyPl z) :=
  opens_eq_places 10 4 toyOpens [2, 4, 7] toyPl (by decide) (by decide) fun _ => Iff.rfl

/-- A CONTROL: the same three openings in another order have the same members and do not rise: the
sets alone do not give the list. -/
example : ¬ ((toyOpens.reverse.map fun o => treePlace 2 o.2).Pairwise Before) ∧
    (toyOpens.reverse.map fun o => numAt 10 4 2 o.2) ≠
      [2, 4, 7].map fun z => wholeNo 10 4 (toyPl z) :=
  ⟨by decide, by decide⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.rising_eq
#print axioms VerifiableInference.Desc.opens_eq_places
#print axioms VerifiableInference.Desc.sets_of_tied
#print axioms VerifiableInference.Desc.firstOpens_lists
#print axioms VerifiableInference.Desc.firstOpens_round
