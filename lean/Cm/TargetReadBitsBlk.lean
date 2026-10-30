-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsBlk.lean: the base of the calculus of separable atoms, with pieces added into one:
a combination of m cells of one matrix whose rows are (a block read off the column side's variables,
a place in the block read off the row side's) costs, under the premises below, at most one piece for
each block of a list that holds the blocks touched, not one for each cell.

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices; a
piece is Σ_{r < R seg, y < C seg} α t r · β u y · A seg r y: one segment, a table on rows times a
table on columns, t and u the numbers that two lists cs, rs of sources of bits form at b, which
together name no variable twice and none outside the cube (`Sep`, `SepV`, `SPiece`,
Cm/TargetReadBits.lean). A piece costs one item of a reading (`sep_read`,
Cm/TargetReadBitsProofs.lean).

The statement (`Cm.TR.Spec.sep_blocks`) and its proof. Generic. It is applied in
Cm/TargetReadBitsFldBlk.lean; Cm/TargetReadBitsBlkV.lean has it with the premises asked at the
vertices.

Why: Cm/TargetReadBits.lean's `Spec.sep_cell` with `Spec.sep_sum` gives m · Q pieces for m cells.
But pieces with the same segment, sources and row table α can be added: α · β + α · β' = α · (β +
β'): the column tables are arbitrary. The number of pieces is the number of reads.

Main names:
  `Spec.sep_blocks`: cs, rs (`Src`, Cm/SegIdx.lean) with Src.OK (cs ++ rs) v; a list L of block
    numbers without repetition; one guard gT and one row map ρ t j on the row side; for each cell k
    < m: a guard gU k u, a coefficient c k u, a block q k u, a column κ k u. F b A := Σ_{k < m} (if
    gT t ∧ gU k u then c k u · A seg (ρ t (q k u)) (κ k u) else 0) is separable with at most |L|
    pieces, if, at the numbers t < 2^|cs|, u < 2^|rs|, q k u ∈ L under gU k u and under the guards
    the places lie in the shapes R, C.

Limits: what the head of Cm/TargetReadBits.lean lists as not said is not said here either. That is:
that a model's atoms are separable; that reads are shared; anything on protocols, errors or cost. A
place whose row and column read the same variable is not taken in.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsProofs

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset Cm.Seg

def Spec.sep_blocks : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m : ℕ) (L : List ℕ) (cs rs : List Src) (gT : ℕ → Prop)
      [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)] (c : ℕ → ℕ → E)
      (q : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ → ℕ) (κ : ℕ → ℕ → ℕ),
    Src.OK (cs ++ rs) v → L.Nodup → (∀ k < m, ∀ u < 2 ^ rs.length, gU k u → q k u ∈ L) →
    (∀ k < m, ∀ t < 2 ^ cs.length,
      ∀ u < 2 ^ rs.length, gT t → gU k u → ρ t (q k u) < R seg ∧ κ k u < C seg) →
    SepV R C v L.length fun b A =>
      ∑ k ∈ range m, if gT (Src.num cs v b) ∧ gU k (Src.num rs v b) then
        c k (Src.num rs v b) *
          A seg (ρ (Src.num cs v b) (q k (Src.num rs v b))) (κ k (Src.num rs v b))
      else 0

variable {E : Type} [Field E]

/-- One cell, summed over the blocks of the list. -/
theorem blocks_one (R C : ℕ → ℕ) (seg : ℕ) (L : List ℕ) (hL : L.Nodup) (pT pU : Prop) [Decidable pT]
    [Decidable pU] (c : E) (q0 κ0 : ℕ) (ρ : ℕ → ℕ) (A : ℕ → ℕ → ℕ → E) (hq : pU → q0 ∈ L)
    (hs : pT → pU → ρ q0 < R seg ∧ κ0 < C seg) :
    (L.map fun j =>
        ∑ r ∈ range (R seg), ∑ y ∈ range (C seg), (if pT ∧ r = ρ j then (1 : E) else 0) *
          (if pU ∧ q0 = j ∧ y = κ0 then c else 0) * A seg r y).sum =
      if pT ∧ pU then c * A seg (ρ q0) κ0 else 0 := by
  rw [← List.sum_toFinset _ hL]
  by_cases hg : pT ∧ pU
  · rw [if_pos hg, sum_eq_single q0, sum_eq_single (ρ q0), sum_eq_single κ0]
    · rw [if_pos ⟨hg.1, rfl⟩, if_pos ⟨hg.2, rfl, rfl⟩, one_mul]
    · intro y _ hy
      rw [if_neg (fun h : pU ∧ q0 = q0 ∧ y = κ0 => hy h.2.2), mul_zero, zero_mul]
    · intro h
      exact absurd (mem_range.2 (hs hg.1 hg.2).2) h
    · intro r _ hr
      exact sum_eq_zero fun y _ => by
        rw [if_neg (fun h : pT ∧ r = ρ q0 => hr h.2), zero_mul, zero_mul]
    · intro h
      exact absurd (mem_range.2 (hs hg.1 hg.2).1) h
    · intro j _ hj
      exact sum_eq_zero fun r _ =>
        sum_eq_zero fun y _ => by
          rw [if_neg (fun h : pU ∧ q0 = j ∧ y = κ0 => hj h.2.1.symm), mul_zero, zero_mul]
    · intro h
      exact absurd (List.mem_toFinset.2 (hq hg.2)) h
  · rw [if_neg hg]
    refine sum_eq_zero fun j _ => sum_eq_zero fun r _ => sum_eq_zero fun y _ => ?_
    by_cases h1 : pT
    · rw [if_neg (fun h : pU ∧ q0 = j ∧ y = κ0 => hg ⟨h1, h.1⟩), mul_zero, zero_mul]
    · rw [if_neg (fun h : pT ∧ r = ρ j => h1 h.1), zero_mul, zero_mul]

theorem list_sum_comm {α : Type} (L : List α) (m : ℕ) (f : α → ℕ → E) :
    (L.map fun j => ∑ k ∈ range m, f j k).sum = ∑ k ∈ range m, (L.map fun j => f j k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.sum_cons, ih, ← sum_add_distrib]; rfl

theorem sep_blocks : Spec.sep_blocks := by
  intro E _ R C v seg m L cs rs gT _ gU _ c q ρ κ hOK hL hq hs
  refine ⟨⟨fun _ => 0,
      L.map fun j =>
        ⟨seg, cs, rs, fun t r => if gT t ∧ r = ρ t j then 1 else 0,
          fun u y => ∑ k ∈ range m, if gU k u ∧ q k u = j ∧ y = κ k u then c k u else 0⟩⟩,
    fun b _ A => ?_, fun P hP => ?_, ?_⟩
  · have h1 := num_lt cs v b
    have h2 := num_lt rs v b
    unfold SepAtom.at
    rw [zero_add, List.map_map]
    show (∑ k ∈ range m, if gT (Src.num cs v b) ∧ gU k (Src.num rs v b) then
          c k (Src.num rs v b) *
            A seg (ρ (Src.num cs v b) (q k (Src.num rs v b))) (κ k (Src.num rs v b))
        else 0) =
      (L.map fun j =>
        ∑ r ∈ range (R seg), ∑ y ∈ range (C seg),
          (if gT (Src.num cs v b) ∧ r = ρ (Src.num cs v b) j then (1 : E) else 0) *
            (∑ k ∈ range m, if gU k (Src.num rs v b) ∧
                  q k (Src.num rs v b) = j ∧
                  y = κ k (Src.num rs v b) then
                c k (Src.num rs v b)
              else 0) * A seg r y).sum
    generalize Src.num cs v b = t at h1 ⊢
    generalize Src.num rs v b = u at h2 ⊢
    have e : ∀ j,
        (∑ r ∈ range (R seg), ∑ y ∈ range (C seg), (if gT t ∧ r = ρ t j then (1 : E) else 0) *
            (∑ k ∈ range m, if gU k u ∧ q k u = j ∧ y = κ k u then c k u else 0) * A seg r y) =
          ∑ k ∈ range m, ∑ r ∈ range (R seg), ∑ y ∈ range (C seg),
            (if gT t ∧ r = ρ t j then (1 : E) else 0) *
              (if gU k u ∧ q k u = j ∧ y = κ k u then c k u else 0) * A seg r y := fun j => by
      rw [sum_comm (s := range m)]
      refine sum_congr rfl fun r _ => ?_
      rw [sum_comm (s := range m)]
      refine sum_congr rfl fun y _ => ?_
      rw [mul_sum, sum_mul]
    rw [List.map_congr_left fun j _ => e j, list_sum_comm]
    exact sum_congr rfl fun k hk =>
      (blocks_one R C seg L hL (gT t) (gU k u) (c k u) (q k u) (κ k u) (ρ t) A
        (hq k (mem_range.1 hk) u h2) (hs k (mem_range.1 hk) t h1 u h2)).symm
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hP
    exact hOK
  · exact le_of_eq (List.length_map _)

end Cm.TR
