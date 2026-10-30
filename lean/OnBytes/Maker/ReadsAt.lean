-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadsAt.lean: which positions of the prover's oracles the reduction of a whole file
(OnBytes/Maker/Whole.lean) reads, said by tree and leaf.

The reduction reads the positions of its wants: from the verifier's messages each chain's rounds
give a list "the tree with the number j over the whole file, at leaf x", and a want is turned into
a position of the chain that sent the tree. This file turns that round: a position of a chain's
stretch is read exactly if the list of all three chains' wants holds its tree's number over the
whole file and its leaf.

  `wantsAll`                    the wants of the three chains in a row.
  `treeAt_lt`                   a position's tree is one of the stretch's trees.
  `i₁_inj` .. `i₂_ne_i₃`        the three maps from a stretch's positions to the positions of the
                                whole are one-to-one, and their images are apart.
  `ownPos₁`, `ownPos₂`, `ownPos₃` a want's position is a given position of a stretch exactly if the
                                want names that position's tree and leaf.
  `reads₁`, `reads₂`, `reads₃`    **a position is read exactly if its tree and leaf are wanted.**
  `mem_extReads`                a place of the stored table is read exactly if it is wanted.

Not claimed. Nothing on what the verifier's messages are; nothing on soundness.


-/
import OnBytes.Maker.Whole
import OnBytes.Maker.TypingTLaws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ Compile.Joined

/-- A position's tree is one of the stretch's trees. -/
theorem treeAt_lt (C : CK) :
    ∀ (ds : List RDT) (q : OPos (uLT C ds)), treeAt C ds q < (ds.map (·.trees.length)).sum
  | d :: ds, .inl p => by
      show treeIn d.trees p < d.trees.length + (ds.map (·.trees.length)).sum
      exact Nat.lt_of_lt_of_le (treeIn_lt d.trees p) (Nat.le_add_right _ _)
  | d :: ds, .inr q => by
      show d.trees.length + treeAt C ds q < d.trees.length + (ds.map (·.trees.length)).sum
      exact Nat.add_lt_add_left (treeAt_lt C ds q) _

/-! ## The three maps into the positions of the whole -/

section Maps
variable (G : Chains)

theorem i₁_inj {p q : OPos G.s₁} (h : G.i₁ p = G.i₁ q) : p = q :=
  OPos.left_injective (Sum.inr.inj h)

theorem i₂_inj {p q : OPos G.s₂} (h : G.i₂ p = G.i₂ q) : p = q :=
  OPos.left_injective (Sum.inr.inj (OPos.right_injective (s := G.s₁) (Sum.inr.inj h)))

theorem i₃_inj {p q : OPos G.s₃} (h : G.i₃ p = G.i₃ q) : p = q :=
  Sum.inr.inj (OPos.right_injective (s := G.s₂)
    (Sum.inr.inj (OPos.right_injective (s := G.s₁) (Sum.inr.inj h))))

theorem i₁_ne_i₂ (p : OPos G.s₁) (q : OPos G.s₂) : G.i₁ p ≠ G.i₂ q := fun h =>
  OPos.left_ne_right _ _ (Sum.inr.inj h)

theorem i₁_ne_i₃ (p : OPos G.s₁) (q : OPos G.s₃) : G.i₁ p ≠ G.i₃ q := fun h =>
  OPos.left_ne_right _ _ (Sum.inr.inj h)

theorem i₂_ne_i₃ (p : OPos G.s₂) (q : OPos G.s₃) : G.i₂ p ≠ G.i₃ q := fun h =>
  OPos.left_ne_right _ _ (Sum.inr.inj (OPos.right_injective (s := G.s₁) (Sum.inr.inj h)))

end Maps

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- The wants of the three chains in a row. -/
def wantsAll (ρ : Rho (chainsOf C D tF tJ t3).sh) : List Want :=
  wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)

/-! ## A want's position -/

theorem ownPosOf_tree (j x : ℕ) :
    ownPosOf C D tF tJ t3 (.tree j x) =
      if j < D.t₁ then (posAtST C D.ds₁ j x).map (chainsOf C D tF tJ t3).i₁
      else if j - D.t₁ < D.t₂ then
        (posAtST C D.ds₂ (j - D.t₁) x).map (chainsOf C D tF tJ t3).i₂
      else (posAtST C D.ds₃ (j - D.t₁ - D.t₂) x).map (chainsOf C D tF tJ t3).i₃ := rfl

theorem ownPos₁ (j x : ℕ) (q : OPos (uLT C D.ds₁)) :
    ownPosOf C D tF tJ t3 (.tree j x) = some ((chainsOf C D tF tJ t3).i₁ q) ↔
      j = treeAt C D.ds₁ q ∧ x = leafAt C D.ds₁ q := by
  constructor
  · intro h
    rw [ownPosOf_tree] at h
    by_cases c1 : j < D.t₁
    · rw [if_pos c1] at h
      obtain ⟨q', hq, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl := i₁_inj _ e
      have hp := place_posAtST C D.ds₁ j x q' hq
      exact ⟨(congrArg Prod.fst hp).symm, (congrArg Prod.snd hp).symm⟩
    · rw [if_neg c1] at h
      by_cases c2 : j - D.t₁ < D.t₂
      · rw [if_pos c2] at h
        obtain ⟨q', _, e⟩ := Option.map_eq_some_iff.1 h
        exact absurd e.symm (i₁_ne_i₂ _ _ _)
      · rw [if_neg c2] at h
        obtain ⟨q', _, e⟩ := Option.map_eq_some_iff.1 h
        exact absurd e.symm (i₁_ne_i₃ _ _ _)
  · rintro ⟨rfl, rfl⟩
    rw [ownPosOf_tree]
    rw [if_pos (show treeAt C D.ds₁ q < D.t₁ from treeAt_lt C D.ds₁ q)]
    have e : posAtST C D.ds₁ (treeAt C D.ds₁ q) (leafAt C D.ds₁ q) = some q :=
      posAtST_place C D.ds₁ q
    rw [e]
    rfl

theorem ownPos₂ (j x : ℕ) (q : OPos (uLT C D.ds₂)) :
    ownPosOf C D tF tJ t3 (.tree j x) = some ((chainsOf C D tF tJ t3).i₂ q) ↔
      j = D.t₁ + treeAt C D.ds₂ q ∧ x = leafAt C D.ds₂ q := by
  constructor
  · intro h
    rw [ownPosOf_tree] at h
    by_cases c1 : j < D.t₁
    · rw [if_pos c1] at h
      obtain ⟨q', _, e⟩ := Option.map_eq_some_iff.1 h
      exact absurd e (i₁_ne_i₂ _ _ _)
    · rw [if_neg c1] at h
      by_cases c2 : j - D.t₁ < D.t₂
      · rw [if_pos c2] at h
        obtain ⟨q', hq, e⟩ := Option.map_eq_some_iff.1 h
        obtain rfl := i₂_inj _ e
        have hp := place_posAtST C D.ds₂ (j - D.t₁) x q' hq
        have h1 : treeAt C D.ds₂ q' = j - D.t₁ := congrArg Prod.fst hp
        exact ⟨by omega, (congrArg Prod.snd hp).symm⟩
      · rw [if_neg c2] at h
        obtain ⟨q', _, e⟩ := Option.map_eq_some_iff.1 h
        exact absurd e.symm (i₂_ne_i₃ _ _ _)
  · rintro ⟨rfl, rfl⟩
    rw [ownPosOf_tree]
    have c2 : D.t₁ + treeAt C D.ds₂ q - D.t₁ < D.t₂ := by
      rw [Nat.add_sub_cancel_left]
      exact treeAt_lt C D.ds₂ q
    rw [if_neg (by omega), if_pos c2, Nat.add_sub_cancel_left]
    have e : posAtST C D.ds₂ (treeAt C D.ds₂ q) (leafAt C D.ds₂ q) = some q :=
      posAtST_place C D.ds₂ q
    rw [e]
    rfl

theorem ownPos₃ (j x : ℕ) (q : OPos (uLT C D.ds₃)) :
    ownPosOf C D tF tJ t3 (.tree j x) = some ((chainsOf C D tF tJ t3).i₃ q) ↔
      j = D.t₁ + D.t₂ + treeAt C D.ds₃ q ∧ x = leafAt C D.ds₃ q := by
  constructor
  · intro h
    rw [ownPosOf_tree] at h
    by_cases c1 : j < D.t₁
    · rw [if_pos c1] at h
      obtain ⟨q', _, e⟩ := Option.map_eq_some_iff.1 h
      exact absurd e (i₁_ne_i₃ _ _ _)
    · rw [if_neg c1] at h
      by_cases c2 : j - D.t₁ < D.t₂
      · rw [if_pos c2] at h
        obtain ⟨q', _, e⟩ := Option.map_eq_some_iff.1 h
        exact absurd e (i₂_ne_i₃ _ _ _)
      · rw [if_neg c2] at h
        obtain ⟨q', hq, e⟩ := Option.map_eq_some_iff.1 h
        obtain rfl := i₃_inj _ e
        have hp := place_posAtST C D.ds₃ (j - D.t₁ - D.t₂) x q' hq
        have h1 : treeAt C D.ds₃ q' = j - D.t₁ - D.t₂ := congrArg Prod.fst hp
        exact ⟨by omega, (congrArg Prod.snd hp).symm⟩
  · rintro ⟨rfl, rfl⟩
    rw [ownPosOf_tree]
    rw [if_neg (by omega), if_neg (by omega),
      show D.t₁ + D.t₂ + treeAt C D.ds₃ q - D.t₁ - D.t₂ = treeAt C D.ds₃ q by omega]
    have e : posAtST C D.ds₃ (treeAt C D.ds₃ q) (leafAt C D.ds₃ q) = some q :=
      posAtST_place C D.ds₃ q
    rw [e]
    rfl

/-! ## What is read -/

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem mem_reads (ρ : Rho (chainsOf C D tF tJ t3).sh) (p : OPos (chainsOf C D tF tJ t3).sh) :
    p ∈ (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ ↔
      ∃ j x, Want.tree j x ∈ wantsAll C D tF tJ t3 ρ ∧
        ownPosOf C D tF tJ t3 (.tree j x) = some p := by
  show p ∈ ((wantsAll C D tF tJ t3 ρ).filterMap (ownPosOf C D tF tJ t3)).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨w, hw, hp⟩
    cases w with
    | table item x => cases hp
    | tree j x => exact ⟨j, x, hw, hp⟩
  · rintro ⟨j, x, hw, hp⟩
    exact ⟨_, hw, hp⟩

/-- A place of the stored table is read exactly if it is wanted, under whichever item. -/
theorem mem_extReads (ρ : Rho (chainsOf C D tF tJ t3).sh) (p : (oneExternalString (2 ^ D.a) SgX).Pos) :
    p ∈ (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ ↔
      ∃ item, Want.table item p.val ∈ wantsAll C D tF tJ t3 ρ := by
  show p ∈ ((wantsAll C D tF tJ t3 ρ).filterMap (extPosOf D)).toFinset ↔ _
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨w, hw, hp⟩
    cases w with
    | tree j x => cases hp
    | table item x =>
      have h0 : (if h : x < 2 ^ D.a then some (⟨x, h⟩ : Fin (2 ^ D.a)) else none) = some p := hp
      by_cases hx : x < 2 ^ D.a
      · rw [dif_pos hx] at h0
        obtain rfl := Option.some.inj h0
        exact ⟨item, hw⟩
      · rw [dif_neg hx] at h0
        cases h0
  · rintro ⟨item, hw⟩
    exact ⟨_, hw, dif_pos p.isLt⟩

/-- **A position of the first stretch is read exactly if its tree and leaf are wanted.** -/
theorem reads₁ (ρ : Rho (chainsOf C D tF tJ t3).sh) (q : OPos (uLT C D.ds₁)) :
    (chainsOf C D tF tJ t3).i₁ q ∈ (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ ↔
      Want.tree (treeAt C D.ds₁ q) (leafAt C D.ds₁ q) ∈ wantsAll C D tF tJ t3 ρ := by
  rw [mem_reads]
  constructor
  · rintro ⟨j, x, hw, hp⟩
    obtain ⟨rfl, rfl⟩ := (ownPos₁ C D tF tJ t3 j x q).1 hp
    exact hw
  · exact fun hw => ⟨_, _, hw, (ownPos₁ C D tF tJ t3 _ _ q).2 ⟨rfl, rfl⟩⟩

/-- The same for the second stretch. -/
theorem reads₂ (ρ : Rho (chainsOf C D tF tJ t3).sh) (q : OPos (uLT C D.ds₂)) :
    (chainsOf C D tF tJ t3).i₂ q ∈ (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ ↔
      Want.tree (D.t₁ + treeAt C D.ds₂ q) (leafAt C D.ds₂ q) ∈ wantsAll C D tF tJ t3 ρ := by
  rw [mem_reads]
  constructor
  · rintro ⟨j, x, hw, hp⟩
    obtain ⟨rfl, rfl⟩ := (ownPos₂ C D tF tJ t3 j x q).1 hp
    exact hw
  · exact fun hw => ⟨_, _, hw, (ownPos₂ C D tF tJ t3 _ _ q).2 ⟨rfl, rfl⟩⟩

/-- The same for the third stretch. -/
theorem reads₃ (ρ : Rho (chainsOf C D tF tJ t3).sh) (q : OPos (uLT C D.ds₃)) :
    (chainsOf C D tF tJ t3).i₃ q ∈ (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ ↔
      Want.tree (D.t₁ + D.t₂ + treeAt C D.ds₃ q) (leafAt C D.ds₃ q) ∈
        wantsAll C D tF tJ t3 ρ := by
  rw [mem_reads]
  constructor
  · rintro ⟨j, x, hw, hp⟩
    obtain ⟨rfl, rfl⟩ := (ownPos₃ C D tF tJ t3 j x q).1 hp
    exact hw
  · exact fun hw => ⟨_, _, hw, (ownPos₃ C D tF tJ t3 _ _ q).2 ⟨rfl, rfl⟩⟩

end

end OnBytes.Maker
