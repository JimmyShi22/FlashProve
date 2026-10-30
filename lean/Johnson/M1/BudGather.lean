-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/BudGather.lean: `BudDebts` from one clause a kind: F, the book and the sides are letters, so a kind's share
plugs in under «the lists of kind κ are my rows».

  `KindBud`          the clause at the lists of one kind, in each chain
  `budDebts_of_kinds`   **`BudDebts` from `KindBud` at every kind**
  `kindBud_none`     a kind with no list: the clause is over nothing, and says nothing
  `budDebts_of_sixteen`   the same with the sixteen kinds spelled, each a named premise: the debt, in full
  `kindBud_always`   a kind whose lists' bound always holds. LAWFUL ONLY WHERE THE PART SENDS NO TABLE
  `kindBud_K10`      the closings: each list of the kind is a closing's row, in the first chain alone

Limits. The sides are letters here: that a list is a kind's row is a hypothesis.
No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.M1.BudShareCore
import Johnson.Desc.ProofFile.Honest.K10.RowsOfClosings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **The clause at the lists of kind κ, in each chain.** -/
def KindBud (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (κ : KindName) : Prop :=
  (∀ L ∈ G.first, L.place.kind = κ → BudOwed F L) ∧
    (∀ L ∈ G.shared, L.place.kind = κ → BudOwed₂ F L) ∧
    ∀ L ∈ G.second, L.place.kind = κ → BudOwed₃ F L

/-- What a list owes reads its place, its row and its bound alone. -/
theorem budOwed_congr {V W Y Pb : Type} {L L' : Lettered Bk F.S₁ F.Cl V W Y Pb} (hp : L.place = L'.place)
    (hr : L.row = L'.row) (hb : ∀ a b c, L'.bud a b c → L.bud a b c) (h : BudOwed F L') : BudOwed F L := by
  intro σ hσ u hu pre t n hc hn ρ hρ
  have hσ' : L'.side F.first.blocksInOrder = some σ := by
    unfold Lettered.side at hσ ⊢
    rw [← hp, ← hr]
    exact hσ
  exact hb _ _ _ (h σ hσ' u hu pre t n hc hn ρ hρ)

/-- **`BudDebts`, gathered kind by kind.** -/
theorem budDebts_of_kinds {G : Sides F Bk W₀ Rc Ky Tr X₀ X} (h : ∀ κ, KindBud G κ) :
    BudDebts F Bk G :=
  budDebts_of (fun L hL => (h L.place.kind).1 L hL rfl) (fun L hL => (h L.place.kind).2.1 L hL rfl)
    fun L hL => (h L.place.kind).2.2 L hL rfl

/-- **The debt in full**: the sixteen kinds, each a premise. -/
theorem budDebts_of_sixteen {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
    (k1 : KindBud G .K1) (k2 : KindBud G .K2) (k3 : KindBud G .K3) (k4 : KindBud G .K4) (k5 : KindBud G .K5)
    (k6 : KindBud G .K6) (k7 : KindBud G .K7) (k8 : KindBud G .K8) (k9 : KindBud G .K9) (k10 : KindBud G .K10)
    (k11 : KindBud G .K11) (k12 : KindBud G .K12) (k13 : KindBud G .K13) (k14 : KindBud G .K14)
    (k15 : KindBud G .K15) (kf : KindBud G .frame) : BudDebts F Bk G :=
  budDebts_of_kinds fun κ => by cases κ <;> assumption

/-- A kind with no list. The clause says nothing. -/
theorem kindBud_none {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {κ : KindName}
    (h1 : ∀ L ∈ G.first, L.place.kind ≠ κ) (h2 : ∀ L ∈ G.shared, L.place.kind ≠ κ)
    (h3 : ∀ L ∈ G.second, L.place.kind ≠ κ) : KindBud G κ :=
  ⟨fun L hL e => absurd e (h1 L hL), fun L hL e => absurd e (h2 L hL), fun L hL e => absurd e (h3 L hL)⟩

/-- A kind whose lists' bound always holds. LAWFUL ONLY WHERE THE PART SENDS NO TABLE: a row that opens a masked tree must say
how many positions are read. -/
theorem kindBud_always {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {κ : KindName}
    (h1 : ∀ L ∈ G.first, L.place.kind = κ → ∀ a b c, L.bud a b c)
    (h2 : ∀ L ∈ G.shared, L.place.kind = κ → ∀ a b c, L.bud a b c)
    (h3 : ∀ L ∈ G.second, L.place.kind = κ → ∀ a b c, L.bud a b c) : KindBud G κ :=
  ⟨fun L hL e _ _ _ _ _ _ _ _ _ _ _ => h1 L hL e _ _ _, fun L hL e _ _ _ _ _ _ _ _ _ _ _ => h2 L hL e _ _ _,
    fun L hL e _ _ _ _ _ _ _ _ _ _ _ => h3 L hL e _ _ _⟩

/-- **The closings**: at a list of the kind the bound is `closeBud`, which asks nothing; the kind has no list in the other
two chains. -/
theorem kindBud_K10 {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
    (h1 : ∀ L ∈ G.first, L.place.kind = .K10 → L.bud = ProofFile.Honest.K10.closeBud)
    (h2 : ∀ L ∈ G.shared, L.place.kind ≠ .K10) (h3 : ∀ L ∈ G.second, L.place.kind ≠ .K10) :
    KindBud G .K10 :=
  kindBud_always (fun L hL e a b c => by rw [h1 L hL e]; trivial) (fun L hL e => absurd e (h2 L hL))
    fun L hL e => absurd e (h3 L hL)

end Johnson.M1

#print axioms Johnson.M1.budOwed_congr
#print axioms Johnson.M1.budDebts_of_sixteen
#print axioms Johnson.M1.budDebts_of_kinds
#print axioms Johnson.M1.kindBud_none
#print axioms Johnson.M1.kindBud_always
#print axioms Johnson.M1.kindBud_K10
