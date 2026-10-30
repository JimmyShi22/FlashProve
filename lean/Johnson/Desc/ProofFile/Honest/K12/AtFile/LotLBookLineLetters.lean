-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLineLetters.lean

It states no goal. No property of the protocol is claimed.

What the maker's text lays for a part of the
first chain to carry (`segmentCarriesAt`, Honest/BookCarryKit.lean), parted in two: what reads the
chain's plan (for each fresh table of a link: is the part the fold behind it; is it the part that sends
what the fold leaves: two Booleans) and what reads the messages alone. At letters: no written value.

  `foldFlagsAt`                     the two Booleans at a round and an address
  `foldFlagsAtTwo`                  the same at two addresses, with one call of `behindFold`
  `foldFlagsAtTwo_eq`               it is the pair of the two
  `carriesByFlags`                  `segmentCarriesAt`'s text with a list of such Booleans for the plan
  `segmentCarriesAt_by_flags`       **the equation**
  `carriedEntriesTest`              the text of `wordsBookB` (ClosingWordsBook.lean) on two lists
  `wordsBookB_of_carriedEntriesTest`  its yes at the two parts' carrying entries gives `wordsBookB`

Why. A closed line over `segmentCarriesAt` at the written plan makes Lean's kernel hold the plan's 48
thousand rounds and the 184 entries at once. Parted, the plan is read once, into 26 times four
Booleans, and the entries are compared without the plan.

Limits.
- Definitions and equations on texts. Nothing at any description or book.
- Where `behindFold` finds nothing the Booleans are false: as `segmentCarriesAt` lays nothing there.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookCarryKit
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingWordsBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest (carryE)

/-! ## 1 What reads the plan -/

/-- **Is the part at `a` the fold behind round number i; is it the part that sends what that fold
leaves.** Both false where `behindFold` finds nothing. -/
def foldFlagsAt (here : List PlanB) (a : Addr) (i : ℕ) : Bool × Bool :=
  match behindFold here i with
  | some (p, q) => (p == a, q == a)
  | none => (false, false)

/-- The same at two addresses, with one call of `behindFold`. -/
def foldFlagsAtTwo (here : List PlanB) (a₁ a₂ : Addr) (i : ℕ) : (Bool × Bool) × (Bool × Bool) :=
  match behindFold here i with
  | some (p, q) => ((p == a₁, q == a₁), (p == a₂, q == a₂))
  | none => ((false, false), (false, false))

theorem foldFlagsAtTwo_eq (here : List PlanB) (a₁ a₂ : Addr) (i : ℕ) :
    foldFlagsAtTwo here a₁ a₂ i = (foldFlagsAt here a₁ i, foldFlagsAt here a₂ i) := by
  unfold foldFlagsAtTwo foldFlagsAt
  generalize behindFold here i = o
  rcases o with _ | ⟨p, q⟩ <;> rfl

/-! ## 2 What reads the messages -/

/-- **`segmentCarriesAt`'s text, with a list of Booleans in the plan's stead**: one pair for each
fresh table of a link, in the order of sending. -/
def carriesByFlags (flags : List (Bool × Bool)) (ms : List SentMsg) (a : Addr) : List Ahead :=
  ((ms.filter fun m => m.fresh && (linkOf m.label).isSome).zip flags).flatMap fun x =>
    match linkOf x.1.label with
    | some l =>
      (if x.2.1 then (ms.filter fun m => !m.masks && ((linkOf m.label).any fun j =>
          decide (j < l) || (j == l && !m.fresh))).map (·.carry a) else []) ++
      (if x.2.2 then (ms.filter fun m => !m.masks && ((linkOf m.label).any fun j =>
          decide (j ≤ l))).map (·.carry a) else [])
    | none => []

theorem flatMap_zip_map {α β γ : Type} (h : α → β) (F : α → List γ) (G : α × β → List γ)
    (e : ∀ x, F x = G (x, h x)) : ∀ l : List α, l.flatMap F = (l.zip (l.map h)).flatMap G
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons, e x,
      flatMap_zip_map h F G e l]

/-- **The equation**: the plan is read at the rounds of the links' fresh tables alone, and of each
answer two Booleans. -/
theorem segmentCarriesAt_by_flags (here : List PlanB) (ms : List SentMsg) (a : Addr) :
    segmentCarriesAt here ms a =
      carriesByFlags (((ms.filter fun m => m.fresh && (linkOf m.label).isSome).map (·.round)).map
        (foldFlagsAt here a)) ms a := by
  unfold segmentCarriesAt carriesByFlags
  rw [List.map_map]
  refine flatMap_zip_map _ _ _ (fun f => ?_) _
  dsimp only [Function.comp_apply, foldFlagsAt]
  generalize behindFold here f.round = o
  generalize linkOf f.label = ol
  rcases o with _ | ⟨p, q⟩ <;> rcases ol with _ | l <;> rfl

/-! ## 3 The test on two lists -/

/-- **`wordsBookB`'s text on two lists of entries.** l₁: what the switch's part carries. l₂: what the
later part carries. a₁: the switch's part. n: how many stretches the switch carries. -/
def carriedEntriesTest (l₁ l₂ : List Ahead) (a₁ : Addr) (n : ℕ) : Bool :=
  Nat.ble n l₁.length &&
    ((l₁.take n).map (fun e => (e.owner, e.start, e.count)) ==
      (l₂.take n).map fun e => (e.owner, e.start, e.count)) &&
    ((l₂[n]?).map (fun e => (e.owner, e.start)) == some (a₁, (⟨0, 0⟩ : Due)))

/-- Its yes at the two parts' carrying entries gives the test on the book. -/
theorem wordsBookB_of_carriedEntriesTest {Bk : ProverCoinCounts} {a₁ a₂ : Addr} {n : ℕ}
    (h : carriedEntriesTest (carryE Bk a₁) (carryE Bk a₂) a₁ n = true) :
    wordsBookB Bk a₁ a₂ n = true := by
  unfold carriedEntriesTest at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold wordsBookB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨Nat.le_of_ble_eq_true h1, h2⟩, h3⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.foldFlagsAtTwo_eq
#print axioms ProofFile.Honest.K12.AtProof.flatMap_zip_map
#print axioms ProofFile.Honest.K12.AtProof.segmentCarriesAt_by_flags
#print axioms ProofFile.Honest.K12.AtProof.wordsBookB_of_carriedEntriesTest
