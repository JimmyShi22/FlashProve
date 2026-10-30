-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TilesMaker.lean: the whole `Three` of its parts, its pieces the maker's
(`cutRow`, Johnson/Desc/Sound/Tiles.lean): so that `Three.IsCut` has a member at all blocks, and
`Three.Fits` is had of a value that is written out. Two definitions, two theorems.
  `Beside`: what a `Three` holds beside its pieces and the three numbers ft.
  `Three.ofCuts`: the value. `ofCuts_isCut`: its pieces are the maker's (by unfolding).
  `FitsOfCuts`, `fitsOfCuts`: at every description F and the data that `FileDescription.data` makes of it.
Limits: those of Tiles.lean. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesDataProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)

/-- What a `Three` holds beside its pieces and the three numbers ft: the fields' words are
FileRule.lean's. -/
structure Beside (Y S₁ S₂ S₃ X₁ X₂ W : Type) where
  n₁ : String
  n₂ : String
  n₃ : String
  in₁ : Y → S₁
  out₁ : Y → S₁ → X₁
  in₂ : X₁ → S₂
  out₂ : X₁ → S₂ → X₂
  in₃ : X₂ → Option S₃
  fin : X₂ → S₃ → Bool
  d : W
  wEnd : W

variable {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}

/-- **The three chains' blocks with their stretches, cut by the maker.** r: the sealing round that
is put back behind the first chain. -/
def Three.ofCuts (C : CK) (D : WholeD) (all : List LeftT) (ft₁ ft₂ ft₃ : ℕ)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₁ ft₁) S₁ W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₂ ft₂) S₂ W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₃ ft₃) S₃ W ds)
    (r : Fmt.RoundView) (E : Beside Y S₁ S₂ S₃ X₁ X₂ W) : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W where
  ft₁ := ft₁
  ft₂ := ft₂
  ft₃ := ft₃
  p₁ := (cutRow rest₁ [r] 0 0 D.ds₁ b₁ l₁).1
  l₁ := (cutRow rest₁ [r] 0 0 D.ds₁ b₁ l₁).2
  p₂ := (cutRow rest₂ [] 0 D.t₁ D.ds₂ b₂ l₂).1
  l₂ := (cutRow rest₂ [] 0 D.t₁ D.ds₂ b₂ l₂).2
  p₃ := (cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ b₃ l₃).1
  l₃ := (cutRow rest₃ [] 0 (D.t₁ + D.t₂) D.ds₃ b₃ l₃).2
  n₁ := E.n₁
  n₂ := E.n₂
  n₃ := E.n₃
  in₁ := E.in₁
  out₁ := E.out₁
  in₂ := E.in₂
  out₂ := E.out₂
  in₃ := E.in₃
  fin := E.fin
  d := E.d
  wEnd := E.wEnd

/-- Its pieces are the maker's. -/
theorem ofCuts_isCut (C : CK) (D : WholeD) (all : List LeftT) (ft₁ ft₂ ft₃ : ℕ)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₁ ft₁) S₁ W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₂ ft₂) S₂ W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₃ ft₃) S₃ W ds)
    (r : Fmt.RoundView) (E : Beside Y S₁ S₂ S₃ X₁ X₂ W) :
    (Three.ofCuts C D all ft₁ ft₂ ft₃ b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r E).IsCut b₁ l₁ b₂ l₂
      b₃ l₃ rest₁ rest₂ rest₃ r :=
  ⟨rfl, rfl, rfl⟩

/-- **The value's three rows of pieces are the file's three chains**, at every description. -/
def FitsOfCuts : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sealLast = true →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (ft₁ ft₂ ft₃ : ℕ)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl))
      (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ ft₁) S₁ W ds)
      (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ ft₂) S₂ W ds)
      (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ ft₃) S₃ W ds)
      (r : Fmt.RoundView) (E : Beside Y S₁ S₂ S₃ X₁ X₂ W),
      (b₁ :: l₁).map (·.rounds) = F.first.blocksInOrder.map (·.rounds) →
      (b₂ :: l₂).map (·.rounds) = F.shared.blocksInOrder.map (·.rounds) →
      (b₃ :: l₃).map (·.rounds) = F.second.blocksInOrder.map (·.rounds) →
      (Three.ofCuts C D (allOf D) ft₁ ft₂ ft₃ b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r E).Fits

theorem fitsOfCuts : FitsOfCuts :=
  fun Xi F file D h hs C Y S₁ S₂ S₃ X₁ X₂ Cl W ft₁ ft₂ ft₃ b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r E
      g₁ g₂ g₃ =>
    fitsOfData Xi F file D h hs C Y S₁ S₂ S₃ X₁ X₂ Cl W _ b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r
      g₁ g₂ g₃ (ofCuts_isCut C D (allOf D) ft₁ ft₂ ft₃ b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r E)

end VerifiableInference.Desc.Sound
