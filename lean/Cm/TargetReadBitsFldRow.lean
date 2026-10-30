-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFldRow.lean: "separable", typed by the row side: all cells of one segment that
share the split into row and column sources, the row guard and the row map cost together, under the
premises of `Spec.sepB_cell` and `Spec.sepB_sepV`, at most one piece for each block of rows; the
predicate is closed under sums, differences, multiples and guards on the column side.

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices; a
piece is Σ_{r < R seg, y < C seg} α t r · β u y · A seg r y: one segment, a table on rows times a
table on columns, t and u the numbers that two lists cs, rs of sources of bits form at b, which
together name no variable twice and none outside the cube (`Sep`, `SepV`, `SPiece`,
Cm/TargetReadBits.lean).

Definitions, statements (in `Cm.TR.Spec`: `sepB_sepV` to `sepK_sum`) and their proofs, in one file.
Generic: any field; no model. The predicates are used at the model's row sides in
Cm/TargetReadBitsFldFF.lean.

Why: in Cm/TargetReadBits.lean's calculus the number of pieces adds up under sums. But pieces with
the same segment, sources and row table can be added (`sep_blocks`, Cm/TargetReadBitsBlk.lean, for
one sum of cells). A model's forms are nested: sums of multiples of values, which are sums of cells.
Here the row side is a parameter of the predicate, and the column side is left free: so pieces are
added into one by the closure rules, however the form is nested.

Main names:
  `RowT`, the row side: a segment; row sources cs, column sources rs; a guard gT on the number t of
    cs; a row map ρ t j (j a block number); a list L of block numbers.
  `SepB R C v W F`: there are column tables β j u y (any function of the block, the number u of rs,
    the column) with, at every vertex b < 2^v and all matrices A: F b A = if gT t then Σ_{j ∈ L}
    Σ_{y < C seg} β j u y · A seg (ρ t j) y else 0; and: under gT, wherever β j u y ≠ 0 (j ∈ L, y <
    C seg), the row ρ t j lies in the shape. v: the number of variables of the cube.
  `Spec.sepB_sepV`: Src.OK (cs ++ rs) v, L without repetition, SepB R C v W F ⇒ SepV R C v |L| F: at
    most one piece a block.
  `Spec.sepB_cell`, the base: F b A := if gT t ∧ gU u then c u · A seg (ρ t (q u)) (κ u) else 0, if
    L is without repetition and at every vertex under the guards: q u ∈ L, the place lies in the
    shapes.
  `SepK R C v W F`, the same up to a constant at each vertex: F b A = G b A + k b with SepB R C v W
    G and any k: so that forms with constant parts, offsets and padding values go through the
    calculus as they are.
  `Spec.sepK_sepV` (at most |L| pieces, if Src.OK (cs ++ rs) v and L is without repetition).

Limits: this file says nothing on multiples and guards that read the row side: these change gT or ρ:
another W.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsProofs

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset

/-- The row side. -/
structure RowT where
  seg : ℕ
  cs : List Src
  rs : List Src
  gT : ℕ → Prop
  [dec : DecidablePred gT]
  ρ : ℕ → ℕ → ℕ
  L : List ℕ

attribute [instance] RowT.dec

variable {E : Type} [Field E]

/-- The value of column tables at a vertex. -/
def RowT.at (W : RowT) (C : ℕ → ℕ) (v : ℕ) (β : ℕ → ℕ → ℕ → E) (b : ℕ) (A : ℕ → ℕ → ℕ → E) : E :=
  if W.gT (Src.num W.cs v b) then
    (W.L.map fun j =>
      ∑ y ∈ range (C W.seg), β j (Src.num W.rs v b) y * A W.seg (W.ρ (Src.num W.cs v b) j) y).sum
  else 0

/-- Under gT, rows lie in the shape wherever the tables are not 0. -/
def RowT.In (W : RowT) (R C : ℕ → ℕ) (v : ℕ) (β : ℕ → ℕ → ℕ → E) : Prop :=
  ∀ b < 2 ^ v, W.gT (Src.num W.cs v b) →
    ∀ j ∈ W.L, ∀ y < C W.seg, β j (Src.num W.rs v b) y ≠ 0 → W.ρ (Src.num W.cs v b) j < R W.seg

/-- Separable at the row side W. -/
def SepB (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F : ℕ → (ℕ → ℕ → ℕ → E) → E) : Prop :=
  ∃ β : ℕ → ℕ → ℕ → E, (∀ b < 2 ^ v, ∀ A, F b A = W.at C v β b A) ∧ W.In R C v β

/-- Separable at the row side W, up to a constant at each vertex. -/
def SepK (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F : ℕ → (ℕ → ℕ → ℕ → E) → E) : Prop :=
  ∃ (G : ℕ → (ℕ → ℕ → ℕ → E) → E) (k : ℕ → E),
    SepB R C v W G ∧ ∀ b < 2 ^ v, ∀ A, F b A = G b A + k b

namespace Spec

def sepB_sepV : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    Src.OK (W.cs ++ W.rs) v → W.L.Nodup → SepB R C v W F → SepV R C v W.L.length F

/-- `sepB_sepV` with a constant part. -/
def sepB_sepVK : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F : ℕ → (ℕ → ℕ → ℕ → E) → E) (k : ℕ → E),
    Src.OK (W.cs ++ W.rs) v → W.L.Nodup → SepB R C v W F →
    SepV R C v W.L.length fun b A => F b A + k b

def sepB_cell : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (gU : ℕ → Prop) [DecidablePred gU]
      (c : ℕ → E) (q κ : ℕ → ℕ),
    (∀ b < 2 ^ v, W.gT (Src.num W.cs v b) → gU (Src.num W.rs v b) →
      q (Src.num W.rs v b) ∈ W.L ∧
      W.ρ (Src.num W.cs v b) (q (Src.num W.rs v b)) < R W.seg ∧
      κ (Src.num W.rs v b) < C W.seg) →
    W.L.Nodup →
    SepB R C v W fun b A =>
      if W.gT (Src.num W.cs v b) ∧ gU (Src.num W.rs v b) then
        c (Src.num W.rs v b) *
          A W.seg (W.ρ (Src.num W.cs v b) (q (Src.num W.rs v b))) (κ (Src.num W.rs v b))
      else 0

def sepB_congr : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ b < 2 ^ v, ∀ A, F b A = G b A) → SepB R C v W G → SepB R C v W F

def sepB_zero : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT), SepB (E := E) R C v W fun _ _ => 0

def sepB_add : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepB R C v W F → SepB R C v W G → SepB R C v W fun b A => F b A + G b A

def sepB_sub : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepB R C v W F → SepB R C v W G → SepB R C v W fun b A => F b A - G b A

def sepB_mulU : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (c : ℕ → E) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepB R C v W F → SepB R C v W fun b A => c (Src.num W.rs v b) * F b A

def sepB_guardU : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (gU : ℕ → Prop)
      [DecidablePred gU] (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepB R C v W F → SepB R C v W fun b A => if gU (Src.num W.rs v b) then F b A else 0

def sepB_sum : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v m : ℕ) (W : RowT) (F : ℕ → ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ k < m, SepB R C v W (F k)) → SepB R C v W fun b A => ∑ k ∈ range m, F k b A

/-! The same, up to a constant at each vertex. -/

def sepK_sepV : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    Src.OK (W.cs ++ W.rs) v → W.L.Nodup → SepK R C v W F → SepV R C v W.L.length F

def sepK_ofB : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepB R C v W F → SepK R C v W F

def sepK_const : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (k : ℕ → E), SepK R C v W fun b _ => k b

def sepK_congr : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ b < 2 ^ v, ∀ A, F b A = G b A) → SepK R C v W G → SepK R C v W F

def sepK_add : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepK R C v W F → SepK R C v W G → SepK R C v W fun b A => F b A + G b A

def sepK_sub : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepK R C v W F → SepK R C v W G → SepK R C v W fun b A => F b A - G b A

def sepK_mulU : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (c : ℕ → E) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepK R C v W F → SepK R C v W fun b A => c (Src.num W.rs v b) * F b A

def sepK_smul : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (c : E) (F : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepK R C v W F → SepK R C v W fun b A => c * F b A

def sepK_iteU : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v : ℕ) (W : RowT) (gU : ℕ → Prop)
      [DecidablePred gU] (F G : ℕ → (ℕ → ℕ → ℕ → E) → E),
    SepK R C v W F → SepK R C v W G →
    SepK R C v W fun b A => if gU (Src.num W.rs v b) then F b A else G b A

def sepK_sum : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v m : ℕ) (W : RowT) (F : ℕ → ℕ → (ℕ → ℕ → ℕ → E) → E),
    (∀ k < m, SepK R C v W (F k)) → SepK R C v W fun b A => ∑ k ∈ range m, F k b A

end Spec

theorem sepB_congr : Spec.sepB_congr := fun _ _ _ _ _ _ _ _ h ⟨β, h1, h2⟩ =>
  ⟨β, fun b hb A => (h b hb A).trans (h1 b hb A), h2⟩

theorem sepB_zero : Spec.sepB_zero := fun E _ R C v W =>
  ⟨fun _ _ _ => 0, fun b _ A => by
    unfold RowT.at
    split_ifs
    · symm
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      simp
    · rfl, fun _ _ _ _ _ _ _ h => absurd rfl h⟩

/-- The value is additive in the tables. -/
theorem RowT.at_add (W : RowT) (C : ℕ → ℕ) (v : ℕ) (β β' : ℕ → ℕ → ℕ → E)
    (b : ℕ) (A : ℕ → ℕ → ℕ → E) :
    W.at C v (fun j u y => β j u y + β' j u y) b A = W.at C v β b A + W.at C v β' b A := by
  unfold RowT.at
  split_ifs
  · rw [← List.sum_map_add]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => add_mul _ _ _
  · rw [add_zero]

/-- The value is homogeneous under multiples that read the column side. -/
theorem RowT.at_mul (W : RowT) (C : ℕ → ℕ) (v : ℕ) (c : ℕ → E) (β : ℕ → ℕ → ℕ → E)
    (b : ℕ) (A : ℕ → ℕ → ℕ → E) :
    W.at C v (fun j u y => c u * β j u y) b A = c (Src.num W.rs v b) * W.at C v β b A := by
  unfold RowT.at
  split_ifs
  · rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => mul_assoc _ _ _
  · rw [mul_zero]

theorem sepB_add : Spec.sepB_add := fun E _ R C v W F G ⟨β, h1, h2⟩ ⟨β', h1', h2'⟩ =>
  ⟨fun j u y => β j u y + β' j u y, fun b hb A => by
    show F b A + G b A = _
    rw [W.at_add, h1 b hb A, h1' b hb A], fun b hb hg j hj y hy hne => by
    by_cases h0 : β j (Src.num W.rs v b) y = 0
    · exact h2' b hb hg j hj y hy fun h0' => hne (by
        show β j (Src.num W.rs v b) y + β' j (Src.num W.rs v b) y = 0
        rw [h0, h0', add_zero])
    · exact h2 b hb hg j hj y hy h0⟩

theorem sepB_mulU : Spec.sepB_mulU := fun E _ R C v W c F ⟨β, h1, h2⟩ =>
  ⟨fun j u y => c u * β j u y, fun b hb A => by
    show c (Src.num W.rs v b) * F b A = _
    rw [W.at_mul, h1 b hb A], fun b hb hg j hj y hy hne => h2 b hb hg j hj y hy fun h0 => hne (by
    show c (Src.num W.rs v b) * β j (Src.num W.rs v b) y = 0
    rw [h0, mul_zero])⟩

theorem sepB_sub : Spec.sepB_sub := fun E _ R C v W F G hF hG =>
  sepB_congr E R C v W _ _ (fun b _ A => by ring)
    (sepB_add E R C v W F _ hF (sepB_mulU E R C v W (fun _ => -1) G hG))

theorem sepB_guardU : Spec.sepB_guardU := fun E _ R C v W gU _ F hF =>
  sepB_congr E R C v W _ _ (fun b _ A => by
    show (if gU (Src.num W.rs v b) then F b A else 0) =
      (if gU (Src.num W.rs v b) then (1 : E) else 0) * F b A
    by_cases h : gU (Src.num W.rs v b)
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]) (sepB_mulU E R C v W (fun u => if gU u then 1 else 0) F hF)

theorem sepB_sum : Spec.sepB_sum := by
  intro E _ R C v m W F h
  induction m with
  | zero =>
    exact sepB_congr E R C v W _ _ (fun _ _ _ => Finset.sum_range_zero _) (sepB_zero E R C v W)
  | succ m ih =>
      exact sepB_congr E R C v W _ _ (fun _ _ _ => Finset.sum_range_succ _ _)
        (sepB_add E R C v W _ _ (ih fun k hk => h k (Nat.lt_succ_of_lt hk))
          (h m (Nat.lt_succ_self m)))

/-- A sum over a list without repetition that picks one member. -/
theorem list_pick (L : List ℕ) (hL : L.Nodup) (a : ℕ) (ha : a ∈ L) (f : ℕ → E) :
    (L.map fun j => if a = j then f j else 0).sum = f a := by
  induction L with
  | nil => exact absurd ha List.not_mem_nil
  | cons x L ih =>
      obtain ⟨hx, hL'⟩ := List.nodup_cons.1 hL
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 ha with rfl | h
      · rw [if_pos rfl]
        have : (L.map fun j => if a = j then f j else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
          exact if_neg fun (e : a = j) => hx (e ▸ hj)
        rw [this, add_zero]
      · rw [if_neg fun (e : a = x) => hx (e ▸ h), zero_add]
        exact ih hL' h

theorem sepB_cell : Spec.sepB_cell := by
  intro E _ R C v W gU _ c q κ hs hL
  refine ⟨fun j u y => if gU u ∧ q u = j ∧ y = κ u then c u else 0,
    fun b hb A => ?_,
    fun b hb hg j hj y hy hne => ?_⟩
  · unfold RowT.at
    beta_reduce
    by_cases hg : W.gT (Src.num W.cs v b)
    · rw [if_pos hg]
      by_cases hu : gU (Src.num W.rs v b)
      · obtain ⟨h1, -, h3⟩ := hs b hb hg hu
        rw [if_pos ⟨hg, hu⟩,
          ← list_pick W.L hL _ h1 fun j =>
            c (Src.num W.rs v b) * A W.seg (W.ρ (Src.num W.cs v b) j) (κ (Src.num W.rs v b))]
        congr 1
        refine List.map_congr_left fun j _ => ?_
        by_cases hj : q (Src.num W.rs v b) = j
        · rw [if_pos hj, Finset.sum_eq_single (κ (Src.num W.rs v b))]
          · rw [if_pos ⟨hu, hj, rfl⟩]
          · intro y _ hy
            rw [if_neg fun h => hy h.2.2, zero_mul]
          · intro h
            exact absurd (Finset.mem_range.2 h3) h
        · rw [if_neg hj]
          symm
          exact Finset.sum_eq_zero fun y _ => by rw [if_neg fun h => hj h.2.1, zero_mul]
      · rw [if_neg fun h => hu h.2]
        symm
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz
        exact Finset.sum_eq_zero fun y _ => by rw [if_neg fun h => hu h.1, zero_mul]
    · rw [if_neg hg, if_neg fun h => hg h.1]
  · by_cases h : gU (Src.num W.rs v b) ∧ q (Src.num W.rs v b) = j ∧ y = κ (Src.num W.rs v b)
    · rw [← h.2.1]
      exact (hs b hb hg h.1).2.1
    · exact absurd (if_neg h) hne

theorem sepB_sepV : Spec.sepB_sepV := by
  intro E _ R C v W F hOK _ ⟨β, h1, h2⟩
  refine ⟨⟨fun _ => 0,
      W.L.map fun j =>
        ⟨W.seg, W.cs, W.rs, fun t r => if W.gT t ∧ r = W.ρ t j then 1 else 0, fun u y => β j u y⟩⟩,
    fun b hb A => ?_, fun P hP => ?_, ?_⟩
  · rw [h1 b hb A]
    unfold SepAtom.at RowT.at
    rw [zero_add, List.map_map]
    have e : ∀ j ∈ W.L,
        (SPiece.at (⟨W.seg, W.cs, W.rs, fun t r => if W.gT t ∧ r = W.ρ t j then 1 else 0,
              fun u y => β j u y⟩ : SPiece E)
            R C v b A) =
          if W.gT (Src.num W.cs v b) then
            ∑ y ∈ range (C W.seg), β j (Src.num W.rs v b) y * A W.seg (W.ρ (Src.num W.cs v b) j) y
          else 0 := by
      intro j hj
      unfold SPiece.at
      show (∑ r ∈ range (R W.seg), ∑ y ∈ range (C W.seg),
          (if W.gT (Src.num W.cs v b) ∧ r = W.ρ (Src.num W.cs v b) j then (1 : E) else 0) *
            β j (Src.num W.rs v b) y * A W.seg r y) = _
      by_cases hg : W.gT (Src.num W.cs v b)
      · rw [if_pos hg]
        by_cases hr : W.ρ (Src.num W.cs v b) j < R W.seg
        · rw [Finset.sum_eq_single (W.ρ (Src.num W.cs v b) j)]
          · exact Finset.sum_congr rfl fun y _ => by rw [if_pos ⟨hg, rfl⟩, one_mul]
          · intro r _ hne
            exact Finset.sum_eq_zero fun y _ => by rw [if_neg fun h => hne h.2, zero_mul, zero_mul]
          · intro h
            exact absurd (Finset.mem_range.2 hr) h
        · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
          · intro y hy
            have h0 : β j (Src.num W.rs v b) y = 0 := by
              by_contra hne
              exact hr (h2 b hb hg j hj y (Finset.mem_range.1 hy) hne)
            rw [h0, zero_mul]
          · intro r hr'
            exact Finset.sum_eq_zero fun y _ => by
              rw [if_neg (fun h : W.gT (Src.num W.cs v b) ∧ r = W.ρ (Src.num W.cs v b) j =>
                    hr (h.2 ▸ Finset.mem_range.1 hr')),
                zero_mul, zero_mul]
      · rw [if_neg hg]
        exact Finset.sum_eq_zero fun r _ =>
          Finset.sum_eq_zero fun y _ => by rw [if_neg fun h => hg h.1, zero_mul, zero_mul]
    rw [List.map_congr_left
        (f := (fun P : SPiece E => P.at R C v b A) ∘
            fun j =>
              (⟨W.seg, W.cs, W.rs, fun t r => if W.gT t ∧ r = W.ρ t j then 1 else 0,
                fun u y => β j u y⟩ : SPiece E)) e]
    by_cases hg : W.gT (Src.num W.cs v b)
    · rw [if_pos hg]
      congr 1
      exact List.map_congr_left fun j _ => (if_pos hg).symm
    · rw [if_neg hg]
      symm
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz
      exact if_neg hg
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hP
    exact hOK
  · rw [List.length_map]

theorem sepB_sepVK : Spec.sepB_sepVK := fun E _ R C v W F k hOK hL hF =>
  sep_add E R C v W.L.length 0 F (fun b _ => k b)
    (sepB_sepV E R C v W F hOK hL hF) (sep_const E R C v k)

theorem sepK_sepV : Spec.sepK_sepV := fun E _ R C v W F hOK hL ⟨G, k, hG, h⟩ =>
  sep_congr E R C v W.L.length F _ h (sepB_sepVK E R C v W G k hOK hL hG)

theorem sepK_ofB : Spec.sepK_ofB := fun _ _ _ _ _ _ F h =>
  ⟨F, fun _ => 0, h, fun _ _ _ => (add_zero _).symm⟩

theorem sepK_const : Spec.sepK_const := fun E _ R C v W k =>
  ⟨fun _ _ => 0, k, sepB_zero E R C v W, fun _ _ _ => (zero_add _).symm⟩

theorem sepK_congr : Spec.sepK_congr := fun _ _ _ _ _ _ _ _ h ⟨G, k, hG, h'⟩ =>
  ⟨G, k, hG, fun b hb A => (h b hb A).trans (h' b hb A)⟩

theorem sepK_add : Spec.sepK_add := fun E _ R C v W F F' ⟨G, k, hG, h⟩ ⟨G', k', hG', h'⟩ =>
  ⟨fun b A => G b A + G' b A, fun b => k b + k' b, sepB_add E R C v W G G' hG hG', fun b hb A => by
    show F b A + F' b A = _
    rw [h b hb A, h' b hb A]
    ring⟩

theorem sepK_mulU : Spec.sepK_mulU := fun E _ R C v W c F ⟨G, k, hG, h⟩ =>
  ⟨fun b A => c (Src.num W.rs v b) * G b A, fun b => c (Src.num W.rs v b) * k b, sepB_mulU E R C v W c G hG, fun b hb A => by
    show c (Src.num W.rs v b) * F b A = _
    rw [h b hb A]
    ring⟩

theorem sepK_smul : Spec.sepK_smul := fun E _ R C v W c F hF =>
  sepK_mulU E R C v W (fun _ => c) F hF

theorem sepK_sub : Spec.sepK_sub := fun E _ R C v W F G hF hG =>
  sepK_congr E R C v W _ _ (fun b _ A => by ring)
    (sepK_add E R C v W F _ hF (sepK_smul E R C v W (-1) G hG))

theorem sepK_iteU : Spec.sepK_iteU := fun E _ R C v W gU _ F G hF hG =>
  sepK_congr E R C v W _ _ (fun b _ A => by
    show (if gU (Src.num W.rs v b) then F b A else G b A) =
      (if gU (Src.num W.rs v b) then (1 : E) else 0) * F b A +
        (if gU (Src.num W.rs v b) then (0 : E) else 1) * G b A
    by_cases h : gU (Src.num W.rs v b)
    · rw [if_pos h, if_pos h, if_pos h, one_mul, zero_mul, add_zero]
    · rw [if_neg h, if_neg h, if_neg h, zero_mul, one_mul, zero_add])
    (sepK_add E R C v W _ _ (sepK_mulU E R C v W (fun u => if gU u then 1 else 0) F hF)
      (sepK_mulU E R C v W (fun u => if gU u then 0 else 1) G hG))

theorem sepK_sum : Spec.sepK_sum := by
  intro E _ R C v m W F h
  induction m with
  | zero =>
    exact sepK_congr E R C v W _ _ (fun _ _ _ => Finset.sum_range_zero _)
      (sepK_const E R C v W fun _ => 0)
  | succ m ih =>
      exact sepK_congr E R C v W _ _ (fun _ _ _ => Finset.sum_range_succ _ _)
        (sepK_add E R C v W _ _ (ih fun k hk => h k (Nat.lt_succ_of_lt hk))
          (h m (Nat.lt_succ_self m)))

end Cm.TR
