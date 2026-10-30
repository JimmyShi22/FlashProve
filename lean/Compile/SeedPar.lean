-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedPar.lean: what the prover keeps of a Merkle tree, with its tokens renumbered (words of
this library: lean/GLOSSARY.md).

`upS N₀ δ` puts both tokens of a leaf's entry (salt, tail) through `Life2.up N₀ δ`
(Compile/Step1_life2_Virt.lean: a number below N₀ stays, every other one goes up by δ).
`upTree N₀ δ t` is the tree t (`TreeH`, Compile/Bcs.lean) with `upS N₀ δ` at every entry of its
field `salts`. The lemmas: `upTree` keeps the root (`upTree_root`); `upS` and `upTree` go through
`getD` and `headD` of a mapped list (`getD_upS`, `headD_upTree`, `getD_upTree`). The token language
(tokens: `Tok`, `Step`, Rom/Defer.lean; stores: `erase`, Compile/Star.lean) is a device of this
library.
-/
import Compile.SeedKit
import Compile.Spec

open Rom Iop

namespace Compile
namespace Seed

open Life2 (up)

variable {I X : Type} {lam K : ℕ} (N₀ δ : ℕ)

/-- tokens, shown through `up` -/
def upS : Option (Tok × Tok) → Option (Tok × Tok) := Option.map (Prod.map (up N₀ δ) (up N₀ δ))
def upTree (t : TreeH lam) : TreeH lam := ⟨t.levels, t.salts.map (upS N₀ δ)⟩

variable {N₀ δ}

theorem getD_upS (l : List (Option (Tok × Tok))) (j : ℕ) :
    (l.map (upS N₀ δ)).getD j none = upS N₀ δ (l.getD j none) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

theorem upTree_root (t : TreeH lam) : (upTree N₀ δ t).root = t.root := rfl

theorem headD_upTree (l : List (TreeH lam)) :
    (l.map (upTree N₀ δ)).headD ⟨[], []⟩ = upTree N₀ δ (l.headD ⟨[], []⟩) := by
  cases l <;> rfl

theorem getD_upTree (l : List (TreeH lam)) (j : ℕ) :
    (l.map (upTree N₀ δ)).getD j ⟨[], []⟩ = upTree N₀ δ (l.getD j ⟨[], []⟩) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[j]? <;> rfl

end Seed
end Compile
