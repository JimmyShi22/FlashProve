-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ToldHalves.lean (it imports
Johnson/Desc/AtSeats/ShapeAtWritten.lean): THE FIELD told OF
PlanAt (Johnson/Desc/K1/Law/NewAtSending.lean), AND THE BINDER hTold OF k01_fifty_atBase, CUT IN TWO
HALVES THAT MEET AT ONE WRITTEN TABLE: laidFull (TreesOpened.lean): for each of the first
chain's 83 trees, in order, the depth and the width of its layout.

  DataHalf ds i₀ base   what the file's data give: of the two rounds that stand at i₀ in the list
                   ds, tree number n has laidFull[base + n]'s depth and width.
  DeclHalf G base m   what the IOP as written in Lean declares: FOR n BELOW m: where it tells of the
                   tree number base + n through the file, and the table has that number, it tells
                   the table's depth and width. m: how many trees the place declares.
  CountTie ds i₀ m  the two rounds send m trees at most.
  told_of_halves   THE GLUE: the three give hTold's own end, at any ds, i₀, base, m, G.

WHY m. A DeclHalf that bound every n at which the table has a number would reach into the places
behind, and ask more than hTold spends or a place's own declaration gives.
Neither half names the other's letters: the data's half reads the lists of rounds alone; the
declared half reads the sub-protocols' declarations alone.
What is not claimed. Any of the three at anything. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.ShapeAtWritten
import Johnson.G.TestsFlat
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (FileDescription)

/-- What the file's data give. -/
def DataHalf (ds : List RDT) (i₀ base : ℕ) : Prop :=
  ∀ d₁ d₂ : RDT, (ds.drop i₀).take 2 = [d₁, d₂] → ∀ n sh, treeShT [d₁, d₂] n = some sh →
    laidFull[base + n]? = some (sh.a, sh.W)

/-- What the IOP as written in Lean declares, of the place's m trees. -/
def DeclHalf {Xi : Type} (G : FileDescription Xi) (base m : ℕ) : Prop :=
  ∀ n, n < m → ∀ o, G.oracleAt (base + n) = some o → ∀ a W, laidFull[base + n]? = some (a, W) →
    o.logLength = a ∧ o.words = W

/-- The two rounds send m trees at most. -/
def CountTie (ds : List RDT) (i₀ m : ℕ) : Prop :=
  ∀ d₁ d₂ : RDT, (ds.drop i₀).take 2 = [d₁, d₂] → d₁.trees.length + d₂.trees.length ≤ m

/-- **The glue.** -/
theorem told_of_halves {Xi : Type} {ds : List RDT} {i₀ base m : ℕ} {G : FileDescription Xi}
    (hD : DataHalf ds i₀ base) (hG : DeclHalf G base m) (hC : CountTie ds i₀ m) :
    ∀ d₁ d₂ : RDT, (ds.drop i₀).take 2 = [d₁, d₂] → ∀ n sh, treeShT [d₁, d₂] n = some sh →
      ∀ o, G.oracleAt (base + n) = some o → o.logLength = sh.a ∧ o.words = sh.W := by
  intro d₁ d₂ e n sh h o ho
  refine hG n ?_ o ho _ _ (hD d₁ d₂ e n sh h)
  have h' := h
  rw [Johnson.G.treeSh_flat] at h'
  have hl := (List.getElem?_eq_some_iff.1 h').1
  have := hC d₁ d₂ e
  simp at hl
  omega

end HashBuild
