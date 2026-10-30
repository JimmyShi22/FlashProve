-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/TestsHold.lean: the two tests on a file's data that OnBytes/Maker/Page/FitAt.lean
and FitPass.lean ask (`kindsAndWorkBelow256`, `rootsOK`) hold at the data at which a file's reduction stands
(OnBytes/Maker/Files.lean, `dataAt`): they are no premises there.

Statements and proofs; no definition.
  `rootsOK`: OnBytes/Three/Data.lean lays a round's trees as one shape for each item "root" of its
    message (`rdOf`): so every round of `Three.Whole.of R₁ R₂ R₃` has as many items "root" as trees,
    whatever the three lists of rounds are.
  `kindsAndWorkBelow256`: a kind's number is below 256 (`kind_small`); where the tests `okAt` pass, every round
    has at most 64 bits of work (`WholeD.workFit`); where they do not, the data are those of three
    empty lists.

Main names: `nRoots_eq`, `rootsOK_of`, `rootsOK_dataAt`, `kind_small`, `smallD_of_work`,
`smallD_dataAt`.
Under "there is" stand, in the tool `mem_zipWith`: a and b, fixed by x = f a b.

To be minded. Where `okAt` fails the data are three empty lists, and both tests hold of nothing:
that the data are those of the meant rounds is `okAt`'s yes, which is not shown here.

What is not claimed. That `okAt` passes at any rounds. Nothing on any hash. Nothing on soundness.


-/
import OnBytes.Maker.Page.FitPass
import OnBytes.Maker.Files

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Fmt (Item)
open OnBytes.Params (Rounds)
open OnBytes.Maker

/-- The items "root" of a message, counted the library's way. -/
theorem nRoots_eq : ∀ l : List Item, nRoots l = l.countP (· == .root)
  | [] => rfl
  | .root :: l => by simp [nRoots, nRoots_eq l]
  | .f :: l => by simp [nRoots, nRoots_eq l]
  | .e :: l => by simp [nRoots, nRoots_eq l]
  | .word :: l => by simp [nRoots, nRoots_eq l]
  | .answer :: l => by simp [nRoots, nRoots_eq l]

theorem mem_zipWith {α β γ : Type} (f : α → β → γ) : ∀ (l : List α) (l' : List β) (x : γ),
    x ∈ List.zipWith f l l' → ∃ a b, x = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: l', x, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, b, rfl⟩
    · exact mem_zipWith f l l' x h

/-- Every round's data of a chain have as many items "root" as trees. -/
theorem rdsFromL_roots (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    (R : Rounds) (d : Three.RDL) (hd : d ∈ Three.rdsFromL all t₁ t₂ here base first R) :
    nRoots d.items = d.trees.length := by
  obtain ⟨r, s, rfl⟩ := mem_zipWith _ _ _ _ hd
  show nRoots r.1.items = ((List.range (r.1.items.countP (· == .root))).map _).length
  rw [List.length_map, List.length_range, nRoots_eq]

/-- **`rootsOK` holds at the data of any three lists of rounds.** -/
theorem rootsOK_of (a : ℕ) (R₁ R₂ R₃ : Rounds) :
    rootsOK (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) = true := by
  unfold rootsOK
  rw [List.all_eq_true]
  intro d hd
  rw [beq_iff_eq]
  rcases List.mem_append.1 hd with h | h
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      exact rdsFromL_roots _ _ _ _ _ _ _ e (List.mem_of_mem_dropLast he)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
      exact rdsFromL_roots _ _ _ _ _ _ _ e he
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact rdsFromL_roots _ _ _ _ _ _ _ e he

/-- **At the data at which a file's reduction stands.** -/
theorem rootsOK_dataAt (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) :
    rootsOK (WholeD.of a (dataAt a R)) = true := by
  by_cases h : okAt a R = true
  · rw [dataAt_of_ok h]
    cases R with
    | none => exact rootsOK_of a [] [] []
    | some R => exact rootsOK_of a R.1 R.2.1 R.2.2
  · rw [dataAt_of_not h]
    exact rootsOK_of a [] [] []

theorem kind_small (k : Fmt.Kind) : k.num < 256 := by cases k <;> decide

/-- `kindsAndWorkBelow256` from the test on the bits of work. -/
theorem smallD_of_work (D : WholeD) (h : D.workFit = true) : kindsAndWorkBelow256 D = true := by
  unfold WholeD.workFit at h
  unfold kindsAndWorkBelow256
  rw [List.all_eq_true] at h ⊢
  intro d hd
  have w := h d (by rw [← List.append_assoc]; exact hd)
  rw [decide_eq_true_eq] at w
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨kind_small _, by omega⟩

/-- **`kindsAndWorkBelow256` holds at the data at which a file's reduction stands.** -/
theorem smallD_dataAt (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) :
    kindsAndWorkBelow256 (WholeD.of a (dataAt a R)) = true := by
  by_cases h : okAt a R = true
  · rw [dataAt_of_ok h]
    cases R with
    | none => cases h
    | some R => exact smallD_of_work _ (okAt_parts h).work
  · rw [dataAt_of_not h]
    rfl

end OnBytes.Maker.Page
