-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what a row owes to `BudDebts`, kind by kind.
/-
Johnson/M1/BudShareCore.lean: `BudDebts`'s three fields (Honest/Law/OwedRule.lean), list by list: each
kind hands in its rows' clause, and `budDebts_of` gathers. No property of the protocol is claimed here.
-/
import Johnson.Desc.ProofFile.Honest.Law.OwedRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest VerifiableInference.Desc

variable {Xi V W Y Pb : Type}

/-- **What one list on the first chain owes to `BudDebts`.** -/
def BudOwed (F : FileDescription Xi) {Bk : ProverCoinCounts} (L : Lettered Bk F.S₁ F.Cl V W Y Pb) : Prop :=
  ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    F.first.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    L.bud u.number ((ρ.first.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
        (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum)

/-- What one list on the shared chain owes to `BudDebts`. -/
def BudOwed₂ (F : FileDescription Xi) {Bk : ProverCoinCounts} (L : Lettered Bk F.S₂ F.Cl V W Y Pb) : Prop :=
  ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    F.shared.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
        (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum)

/-- What one list on the last chain owes to `BudDebts`. -/
def BudOwed₃ (F : FileDescription Xi) {Bk : ProverCoinCounts} (L : Lettered Bk F.S₃ F.Cl V W Y Pb) : Prop :=
  ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    F.second.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    L.bud u.number ((ρ.second.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
        (((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length)).sum)

/-- **`BudDebts`, gathered list by list.** -/
theorem budDebts_of {W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} (h₁ : ∀ L ∈ G.first, BudOwed F L)
    (h₂ : ∀ L ∈ G.shared, BudOwed₂ F L) (h₃ : ∀ L ∈ G.second, BudOwed₃ F L) :
    BudDebts F Bk G :=
  ⟨h₁, h₂, h₃⟩

/-- A list whose bound always holds owes nothing. LAWFUL ONLY WHERE THE PART SENDS NO TABLE: at a row
with no slack `bud := True` makes `exact` false, so this is no way for a row that opens masked trees. -/
theorem budOwed_true (F : FileDescription Xi) {Bk : ProverCoinCounts} (L : Lettered Bk F.S₁ F.Cl V W Y Pb)
    (h : ∀ a b c, L.bud a b c) : BudOwed F L :=
  fun _ _ _ _ _ _ _ _ _ _ _ => h _ _ _

end Johnson.M1

#print axioms Johnson.M1.budDebts_of
#print axioms Johnson.M1.budOwed_true
