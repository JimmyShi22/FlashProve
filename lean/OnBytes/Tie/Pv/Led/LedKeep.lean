-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedKeep.lean: which steps of the shipped Lean verifier leave the gathered total
of
a sub-proof's state as it was.

Model.Fork.total (OnBytes/Model/HideLaws.lean) is the value, in a world, of the left side of the
equation that a state has gathered. It reads the weights L of the virtual rows, the coefficients LS
of the slots and the constant c0. The theorem one_equation (LedPort.lean) asks that the total is 0
before the claims are added and that it does not change between the last claim and Fork.settle.

Main theorems: total_congr (states with the same arrays, LS and c0 have the same total);
hide_total, batchBy_total (Fork.hide and Fork.batchBy keep it, and keep the size of LS);
treesValue_keys (the arrays' share hangs only on the weights L and their first columns L0);
modifyRow_total (changing one virtual row by a function that keeps L and L0 keeps the total: so
does setting the row's weights on the rows of its array).

What this file does not claim. The world is a fixed letter in each theorem. The world of the
committed entries (portWorld) does change with what a state holds for its slots and rows.


-/
import OnBytes.Tie.Pv.Led.LedPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

variable {K : Type} [Field K] (ρ : Model.Reading K) (W : Model.World K)

theorem total_congr (F G : Model.Fork) (h1 : G.trees = F.trees) (h2 : G.LS = F.LS)
    (h3 : G.c0 = F.c0) : G.total ρ W = F.total ρ W := by
  simp only [Model.Fork.total, h1, h2, h3]

/-- Fork.hide keeps the total, the coefficients LS and the number of slots. -/
theorem hide_total {F G : Model.Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) :
    G.total ρ W = F.total ρ W ∧ G.LS = F.LS ∧ G.ns = F.ns ∧ G.nClaim = F.nClaim := by
  obtain ⟨rfl, _⟩ := hide_spec h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Fork.batchBy keeps the total, and sets theta. -/
theorem batchBy_total {F G : Model.Fork} {x : E} (h : F.batchBy x = some G) :
    G.total ρ W = F.total ρ W ∧ G.LS = F.LS ∧ G.ns = F.ns ∧ G.nClaim = F.nClaim ∧
      G.theta = x := by
  unfold Model.Fork.batchBy at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- What the total reads of a virtual row: its weights L and their first column. -/
def rowKey (R : Model.HRow) : Array E × Nat := (R.L, R.L0)

/-- What the total reads of an array. -/
def treeKey (X : Model.HTree) : Array (Array E × Nat) := X.rows.map rowKey

/-- The arrays' share of the total hangs only on the weights L and their first columns. -/
theorem treesValue_keys (a b : Array Model.HTree) (h : a.map treeKey = b.map treeKey) :
    Model.treesValue ρ W a = Model.treesValue ρ W b := by
  have row : ∀ t r R, Model.HRow.value ρ W t r R =
      Model.sumFrom (fun i v => ρ.val v * W.entry t r i) (rowKey R).2 (rowKey R).1.toList :=
    fun _ _ _ => rfl
  have tree : ∀ t X, Model.HTree.value ρ W t X =
      Model.sumFrom (fun r (p : Array E × Nat) =>
        Model.sumFrom (fun i v => ρ.val v * W.entry t r i) p.2 p.1.toList) 0
        (treeKey X).toList := by
    intro t X
    simp only [Model.HTree.value, row, treeKey, Array.toList_map, sumFrom_map]
  have all : ∀ c : Array Model.HTree, Model.treesValue ρ W c =
      Model.sumFrom (fun t (q : Array (Array E × Nat)) =>
        Model.sumFrom (fun r (p : Array E × Nat) =>
          Model.sumFrom (fun i v => ρ.val v * W.entry t r i) p.2 p.1.toList) 0 q.toList) 0
        (c.map treeKey).toList := by
    intro c
    simp only [Model.treesValue, tree, Array.toList_map, sumFrom_map]
  rw [all a, all b, h]

/-- Changing virtual row r of array t by a function that keeps L and L0 keeps the total. -/
theorem modifyRow_total (F : Model.Fork) (t r : Nat) (f : Model.HRow → Model.HRow)
    (hf : ∀ R, (f R).L = R.L ∧ (f R).L0 = R.L0) :
    Model.Fork.total ρ W
        { F with trees := F.trees.modify t fun X => { X with rows := X.rows.modify r f } } =
      F.total ρ W := by
  have hk : ∀ R, rowKey (f R) = rowKey R := fun R => by
    simp only [rowKey, (hf R).1, (hf R).2]
  have ht : ∀ X : Model.HTree, treeKey { X with rows := X.rows.modify r f } = treeKey X :=
    fun X => Model.map_modify_same rowKey f hk X.rows r
  have e := treesValue_keys ρ W
    (F.trees.modify t fun X => { X with rows := X.rows.modify r f }) F.trees
    (Model.map_modify_same treeKey _ ht F.trees t)
  simp only [Model.Fork.total, e]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.hide_total
#print axioms OnBytes.Road.Rows.treesValue_keys
#print axioms OnBytes.Road.Rows.modifyRow_total
