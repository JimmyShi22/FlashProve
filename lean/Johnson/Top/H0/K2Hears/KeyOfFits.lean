-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeyOfFits.lean: under which key the first chain's view has a tree of the
file, where the makers' test on the written rounds (`Three.Whole.fits`, OnBytes/Three/Data.lean)
says yes: a tree of the first chain under its own number; A TREE OF THE SECOND CHAIN UNDER ITS
NUMBER IN THAT CHAIN, so under the key of a tree of the first chain. Statements and proofs; no
definition.

  `fits_label`     the test's clause on the number in an opened tree's label
  `shapeAt_none`   a tree that no round opens has the stand-in's shape
  `key_first`      (Whole.of R₁ R₂ R₃).key 0 j = j, for j below the first chain's number of trees
  `key_second`     (Whole.of R₁ R₂ R₃).key 0 (t₁ + j) = j, for j below the second chain's
  `keys_meet`      so, where both chains send a tree, tree 0 and tree t₁ have one key in the first
                   chain's view: THE KEYS OF ALL THE FILE's TREES ARE NOT APART THERE
Limits. Nothing on the third chain's trees. Nothing says of which rounds a description's data are
made. No soundness is claimed.

-/
import OnBytes.Tie.Pv.Keeps.Fits34OfOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open OnBytes.Tie.Pv.Keeps.OkOf.Proved OnBytes.Tie.Pv.Keeps.OkOf.Rows

variable {R₁ R₂ R₃ : Rounds} {m : Nat}

/-- The clause on the number in an opened tree's label. -/
theorem fits_label (h : Three.Whole.fits R₁ R₂ R₃ m = true) (t : Three.Tree) (j : Nat)
    (ht : (Three.Whole.of R₁ R₂ R₃).table[j]? = some t) :
    t.openedAt.isEmpty = true ∨
      t.shape.tree = (match t.chain with
        | 0 => j
        | 1 => j - (Three.Whole.of R₁ R₂ R₃).t₁
        | _ => Three.first₃ (Three.Whole.of R₁ R₂ R₃).t₁ +
            (j - ((Three.Whole.of R₁ R₂ R₃).t₁ + (Three.Whole.of R₁ R₂ R₃).t₂))) := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, c4⟩, -⟩, -⟩ := h
  have hm : (t, j) ∈ (Three.Whole.of R₁ R₂ R₃).table.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact ht
  have h1 := List.all_eq_true.1 c4 (t, j) hm
  rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (eq_of_beq h2)

/-- A tree that no round opens has the stand-in's shape. -/
theorem shapeAt_none (all : List (Nat × Fmt.Shape × Nat × Nat)) (j : Nat) (dflt : Fmt.Shape)
    (h : ((all.filter (·.1 == j)).map (·.2.2)).isEmpty = true) :
    Three.shapeAt all j dflt = dflt := by
  have h1 : all.filter (·.1 == j) = [] := by
    simpa using h
  have h2 : all.find? (·.1 == j) = none := by
    rw [List.find?_eq_none]
    intro x hx hp
    have : x ∈ all.filter (·.1 == j) := List.mem_filter.2 ⟨hx, hp⟩
    rw [h1] at this
    cases this
  unfold Three.shapeAt
  rw [h2]
  rfl

/-- **A tree of the first chain stands under its own number.** -/
theorem key_first (h : Three.Whole.fits R₁ R₂ R₃ m = true) (j : Nat)
    (hj : j < Three.rootsIn R₁) : (Three.Whole.of R₁ R₂ R₃).key 0 j = j := by
  obtain ⟨i, k, e, -⟩ := fits34_of_opens_table_get R₁ R₂ R₃ (0, j) (by omega) hj
  have w : Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (0, j) = j := Nat.zero_add j
  rw [w] at e
  have hl : (Three.shapeAt (Three.Whole.of R₁ R₂ R₃).opens j
      (Three.bareShape (firstOf (Three.rootsIn R₁) 0) j)).tree = j := by
    rcases fits_label h _ j e with h1 | h1
    · rw [shapeAt_none _ _ _ h1]
      exact Nat.zero_add j
    · exact h1
  unfold Three.Whole.key
  rw [e]
  simp only [Option.map_some, Option.getD_some]
  rw [hl]
  rfl

/-- **A tree of the second chain stands, in the first chain's view, under its number in its own
chain.** -/
theorem key_second (h : Three.Whole.fits R₁ R₂ R₃ m = true) (j : Nat)
    (hj : j < Three.rootsIn R₂) :
    (Three.Whole.of R₁ R₂ R₃).key 0 (Three.rootsIn R₁ + j) = j := by
  obtain ⟨i, k, e, -⟩ := fits34_of_opens_table_get R₁ R₂ R₃ (1, j) (by omega) hj
  have w : Three.wholeNo (Three.rootsIn R₁) (Three.rootsIn R₂) (1, j) = Three.rootsIn R₁ + j := rfl
  rw [w] at e
  have hl : (Three.shapeAt (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁ + j)
      (Three.bareShape (firstOf (Three.rootsIn R₁) 1) j)).tree = j := by
    rcases fits_label h _ _ e with h1 | h1
    · rw [shapeAt_none _ _ _ h1]
      exact Nat.zero_add j
    · have h2 : (Three.shapeAt (Three.Whole.of R₁ R₂ R₃).opens (Three.rootsIn R₁ + j)
          (Three.bareShape (firstOf (Three.rootsIn R₁) 1) j)).tree =
          Three.rootsIn R₁ + j - Three.rootsIn R₁ := h1
      rw [h2]
      omega
  unfold Three.Whole.key
  rw [e]
  simp only [Option.map_some, Option.getD_some]
  rw [hl]
  rfl

/-- **Where both chains send a tree, two trees of the file have one key in the first chain's
view.** -/
theorem keys_meet (h : Three.Whole.fits R₁ R₂ R₃ m = true) (h1 : 0 < Three.rootsIn R₁)
    (h2 : 0 < Three.rootsIn R₂) :
    (Three.Whole.of R₁ R₂ R₃).key 0 0 = (Three.Whole.of R₁ R₂ R₃).key 0 (Three.rootsIn R₁) ∧
      0 ≠ Three.rootsIn R₁ := by
  refine ⟨?_, by omega⟩
  rw [key_first h 0 h1]
  exact (key_second h 0 h2).symm

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.key_first
#print axioms VerifiableInference.Desc.First.K2.key_second
#print axioms VerifiableInference.Desc.First.K2.keys_meet
