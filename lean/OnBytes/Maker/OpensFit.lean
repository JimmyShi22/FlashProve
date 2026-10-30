-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OpensFit.lean: for one stretch of a file's rounds, the openings that the typing lays
stand exactly at the positions that are read, and have salts and paths of the right lengths.

A compiled verifier with the strict format asks of the openings in a proof string: an opening stands
only at a position that is read; each position that is read has one; its salt has a fixed number of
bits; its path is as long as its tree is deep. This file shows these of `opensT`
(OnBytes/Maker/TypingT.lean), for one stretch, at any tables that meet `TabsHold` and `TabsBack`, as
the value of the tables with whole paths does (`tabsWFull`, OnBytes/Maker/Tables.lean).

  `OpensFit`          the four conditions for one stretch, with "is read" as a letter.
  `opensT_some`       what a value of `opensT` is made of.
  `shape₁`, `shape₂`, `shape₃`
                      the shape of a stretch's tree, by its number over the whole file.
  `opensFit_of`       the four conditions for a stretch, where "is read" is "tree and leaf are
                      wanted" and what is wanted is what the file's openings list.

OnBytes/Maker/TypingAlike.lean has the three stretches of a file, with "is
read" the reduction's own, and the stored table (`opensFitA₁`, `opensFitA₂`, `opensFitA₃`,
`extFitA`).

The premises of `opensFit_of`, six. `TabsHold`, `TabsBack`: both follow where the tables return a
value. The test `shapesFit`. Each sender's run's value has 32 bytes (`hrun`). That what is wanted is
what the file's openings list. None of these five is shown here. The equation of shapes (`hsh`):
`shape₁`, `shape₂`, `shape₃` have it.

Not claimed. Nothing on hashes; nothing on soundness.


-/
import OnBytes.Maker.WantsRows
import OnBytes.Maker.TablesBack

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom _root_.Compile _root_.Run _root_.Run.PQ

/-- What is asked of the openings at one stretch. rd: is this position read. sMT: the bits of a
salt. -/
structure OpensFit (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (sMT : ℕ) (rd : OPos (uLT C ds) → Prop) : Prop where
  only : ∀ q op, opensT C ds base tabs q = some op → rd q ∧ op.salt.length = sMT
  all : ∀ q, rd q → (opensT C ds base tabs q).isSome = true
  path : ∀ q op sh, opensT C ds base tabs q = some op →
    treeShT ds (treeAt C ds q) = some sh → op.path.length = sh.a

/-- What a value of `opensT` is made of. -/
theorem opensT_some (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (q : OPos (uLT C ds)) (op : Opening 256 (OSym (uLT C ds) q))
    (h : opensT C ds base tabs q = some op) :
    ∃ tab c, tabs.lookup (base + treeAt C ds q) = some tab ∧
      tab.lookup (leafAt C ds q) = some (c, op.salt, op.path) ∧
      symT' C ds q c = some op.sym := by
  have h0 : atTT (symT' C ds q) tabs (base + treeAt C ds q) (leafAt C ds q) = some op := h
  unfold atTT at h0
  cases ht : tabs.lookup (base + treeAt C ds q) with
  | none => rw [ht] at h0; cases h0
  | some tab =>
    rw [ht] at h0
    have h1 : atT (symT' C ds q) tab (leafAt C ds q) = some op := h0
    unfold atT at h1
    cases hl : tab.lookup (leafAt C ds q) with
    | none => rw [hl] at h1; cases h1
    | some row =>
      obtain ⟨c, s, pt⟩ := row
      rw [hl] at h1
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1
        (show (symT' C ds q c).map (fun y => (⟨y, s, pt⟩ : Opening 256 _)) = some op from h1)
      exact ⟨tab, c, rfl, hl, hy⟩

/-- And back. -/
theorem opensT_of (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (q : OPos (uLT C ds)) (tab : List (ℕ × Row3)) (c : List UInt64) (s : Bits)
    (pt : List (Dig 256)) (y : OSym (uLT C ds) q)
    (ht : tabs.lookup (base + treeAt C ds q) = some tab)
    (hl : tab.lookup (leafAt C ds q) = some (c, s, pt)) (hy : symT' C ds q c = some y) :
    opensT C ds base tabs q = some ⟨y, s, pt⟩ := by
  show atTT (symT' C ds q) tabs (base + treeAt C ds q) (leafAt C ds q) = _
  unfold atTT
  rw [ht]
  show atT (symT' C ds q) tab (leafAt C ds q) = _
  unfold atT
  rw [hl]
  show (symT' C ds q c).map _ = _
  rw [hy]
  rfl

/-! ## The shape of a stretch's tree -/

section Shapes
variable (C : CK) (D : WholeD)

theorem shape₁ (q : OPos (uLT C D.ds₁)) :
    D.shape (0 + treeAt C D.ds₁ q) = treeShT D.ds₁ (treeAt C D.ds₁ q) := by
  unfold WholeD.shape
  rw [Nat.zero_add, if_pos (show treeAt C D.ds₁ q < D.t₁ from treeAt_lt C D.ds₁ q)]

theorem shape₂ (q : OPos (uLT C D.ds₂)) :
    D.shape (D.t₁ + treeAt C D.ds₂ q) = treeShT D.ds₂ (treeAt C D.ds₂ q) := by
  unfold WholeD.shape
  have h2 : treeAt C D.ds₂ q < D.t₂ := treeAt_lt C D.ds₂ q
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos h2]

theorem shape₃ (q : OPos (uLT C D.ds₃)) :
    D.shape (D.t₁ + D.t₂ + treeAt C D.ds₃ q) = treeShT D.ds₃ (treeAt C D.ds₃ q) := by
  unfold WholeD.shape
  rw [if_neg (by omega), if_neg (by omega),
    show D.t₁ + D.t₂ + treeAt C D.ds₃ q - D.t₁ - D.t₂ = treeAt C D.ds₃ q by omega]

end Shapes

/-! ## One stretch -/

/-- **The four conditions for a stretch.** ds, base: the stretch and the number of trees sent before
it. wanted: what the verifier's messages ask of the trees. -/
theorem opensFit_of (C : CK) (a : ℕ) (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
    (tabs : List (ℕ × List (ℕ × Row3))) (ds : List RDT) (base : ℕ) (wanted : ℕ → ℕ → Prop)
    (htabs : TabsHold W sb r tabs) (hback : TabsBack W sb r tabs)
    (hshape : shapesFit a W = true)
    (hrun : ∀ j run, runOfTree W r j = some run → run.size = 32)
    (hsh : ∀ q, (WholeD.of a W).shape (base + treeAt C ds q) = treeShT ds (treeAt C ds q))
    (hw : ∀ j x, wanted j x ↔ ∃ z, (j, z) ∈ ownRowsW W r ∧ x ∈ z.2.1) :
    OpensFit C ds base tabs (256 + 8 * sb)
      fun q => wanted (base + treeAt C ds q) (leafAt C ds q) where
  only := fun q op h => by
    obtain ⟨tab, c, ht, hl, -⟩ := opensT_some C ds base tabs q op h
    obtain ⟨z, run, s0, hz, hm, hr, hs0, hs, -⟩ := hback _ _ _ _ _ _ ht hl
    refine ⟨(hw _ _).2 ⟨z, hz, (List.of_mem_zip hm).1⟩, ?_⟩
    rw [hs, length_leafSalt, hrun _ _ hr, hs0]
  all := fun q h => by
    obtain ⟨z, hz, hx⟩ := (hw _ _).1 h
    obtain ⟨t, ht, e1, hok⟩ := htabs.row _ z hz
    obtain ⟨c, hc⟩ := exists_zip_of_mem z.2.1 z.2.2.cols _
      (Nat.le_of_eq (TieTree.ok_spec (asOpenB z) _ _ hok).1.symm) hx
    obtain ⟨tab, s, pt, hlt, hlx⟩ := htabs.look _ z hz _ c hc
    have hT : treeShT ds (treeAt C ds q) = some t.shape := by
      rw [← hsh q]
      exact shapesFit_at hshape ht
    obtain ⟨y, hy⟩ := symT'_some C ds q t.shape c hT
      ((TieTree.ok_list (asOpenB z) _ _ hok).2.2 c (List.of_mem_zip hc).2)
    rw [opensT_of C ds base tabs q tab c s pt y hlt hlx hy]
    rfl
  path := fun q op sh h hT => by
    obtain ⟨tab, c, ht, hl, -⟩ := opensT_some C ds base tabs q op h
    obtain ⟨z, run, s0, hz, -, -, -, -, hp⟩ := hback _ _ _ _ _ _ ht hl
    obtain ⟨t, ht', e1, -⟩ := htabs.row _ z hz
    have hT' : treeShT ds (treeAt C ds q) = some t.shape := by
      rw [← hsh q]
      exact shapesFit_at hshape ht'
    obtain rfl : t.shape = sh := Option.some.inj (hT'.symm.trans hT)
    rw [hp, e1]

end OnBytes.Maker
