-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Here.lean: `RowOk.here` (Honest/Law/Rule/Items.lean), list by
list. That field says: at all coins at which the cell is called, its blocks are available, `On`
holds, and it says something. Here it is stated of a cell after a list of stages (`HereAt`) and of
every cell of a list of items (`HereAll`); it carries over two consecutive lists, and gives the
condition at every cut. So it can be proved along the way in which a list is built. Φ and V are type
parameters.

  1  `HereAt`, `HereAll`   definitions
  2  `HereAll.nil`, `HereAll.cons`, `HereAll.append`, `HereAll.cut`
  3  `HereAll.det`   a list without a cell

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Items

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {Bk : ProverCoinCounts} {Φ V : Type} [Inhabited V]

/-! ## 1 Definitions -/

/-- `RowOk.here` at one cell after a list of stages, from L₀. -/
def HereAt (L₀ : Φ) (pre : List (Kit.Stage (Coins Bk) Φ V)) (C : Cell Bk Φ V) : Prop :=
  ∀ k, C.live (Kit.real pre k L₀) = true → ∃ sp ca v, C.spent k = some sp ∧
    C.carried k = some ca ∧ C.On ca (Kit.real pre k L₀) ∧
    C.speaks (C.get k) sp ca (Kit.real pre k L₀) = some v

/-- `HereAt` at every cell of a list of items after a list of stages. -/
def HereAll (L₀ : Φ) : List (Kit.Stage (Coins Bk) Φ V) → List (Item Bk Φ V) → Prop
  | _, [] => True
  | pre, i :: is => (∀ C, i = .cell C → HereAt L₀ pre C) ∧ HereAll L₀ (pre ++ [i.stage]) is

/-! ## 2 Over two consecutive lists -/

theorem HereAll.nil (L₀ : Φ) (pre : List (Kit.Stage (Coins Bk) Φ V)) :
    HereAll L₀ pre ([] : List (Item Bk Φ V)) := trivial

theorem HereAll.cons {L₀ : Φ} {pre : List (Kit.Stage (Coins Bk) Φ V)} {i : Item Bk Φ V}
    {is : List (Item Bk Φ V)} (h1 : ∀ C, i = .cell C → HereAt L₀ pre C)
    (h2 : HereAll L₀ (pre ++ [i.stage]) is) : HereAll L₀ pre (i :: is) := by
  show (∀ C, i = .cell C → HereAt L₀ pre C) ∧ HereAll L₀ (pre ++ [i.stage]) is
  exact ⟨h1, h2⟩

theorem HereAll.append {L₀ : Φ} : ∀ (I₁ I₂ : List (Item Bk Φ V))
    (pre : List (Kit.Stage (Coins Bk) Φ V)), HereAll L₀ pre I₁ →
    HereAll L₀ (pre ++ I₁.map Item.stage) I₂ → HereAll L₀ pre (I₁ ++ I₂)
  | [], I₂, pre, _, h2 => by
    have h2' : HereAll L₀ (pre ++ []) I₂ := h2
    rw [List.append_nil] at h2'
    exact h2'
  | i :: I₁, I₂, pre, h1, h2 => by
    obtain ⟨a1, a2⟩ : (∀ C, i = .cell C → HereAt L₀ pre C) ∧
      HereAll L₀ (pre ++ [i.stage]) I₁ := h1
    refine HereAll.cons a1 (HereAll.append I₁ I₂ (pre ++ [i.stage]) a2 ?_)
    rw [List.append_assoc]
    exact h2

/-- At every cut. -/
theorem HereAll.cut {L₀ : Φ} : ∀ (items : List (Item Bk Φ V))
    (pre : List (Kit.Stage (Coins Bk) Φ V)), HereAll L₀ pre items →
    ∀ I₁ C I₂, items = I₁ ++ Item.cell C :: I₂ → HereAt L₀ (pre ++ I₁.map Item.stage) C
  | [], _, _, I₁, C, I₂, h => by cases I₁ <;> cases h
  | i :: is, pre, hk, [], C, I₂, h => by
    have e : i = Item.cell C := (List.cons.inj h).1
    obtain ⟨a1, -⟩ : (∀ C, i = .cell C → HereAt L₀ pre C) ∧
      HereAll L₀ (pre ++ [i.stage]) is := hk
    show HereAt L₀ (pre ++ []) C
    rw [List.append_nil]
    exact a1 C e
  | i :: is, pre, hk, j :: I₁, C, I₂, h => by
    have e1 : i = j := (List.cons.inj h).1
    have e2 : is = I₁ ++ Item.cell C :: I₂ := (List.cons.inj h).2
    subst e1
    obtain ⟨-, a2⟩ : (∀ C, i = .cell C → HereAt L₀ pre C) ∧
      HereAll L₀ (pre ++ [i.stage]) is := hk
    have := HereAll.cut is (pre ++ [i.stage]) a2 I₁ C I₂ e2
    rw [List.append_assoc] at this
    exact this

/-! ## 3 A list without a cell -/

theorem HereAll.det {L₀ : Φ} : ∀ (is : List (Item Bk Φ V))
    (pre : List (Kit.Stage (Coins Bk) Φ V)), (∀ i ∈ is, ∀ C, i ≠ .cell C) → HereAll L₀ pre is
  | [], _, _ => trivial
  | i :: is, _, h =>
    HereAll.cons (fun C e => absurd e (h i (List.mem_cons.2 (Or.inl rfl)) C))
      (HereAll.det is _ fun j hj => h j (List.mem_cons_of_mem _ hj))

end ProofFile.Honest

#print axioms ProofFile.Honest.HereAll.nil
#print axioms ProofFile.Honest.HereAll.cons
#print axioms ProofFile.Honest.HereAll.append
#print axioms ProofFile.Honest.HereAll.cut
#print axioms ProofFile.Honest.HereAll.det
