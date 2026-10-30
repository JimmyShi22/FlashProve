-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsBlkV.lean: the base of the calculus of separable atoms for m cells, and its case of
one cell, with the premises asked at the vertices alone.

Separable with at most n pieces in the shapes R, C (the numbers of rows and columns of each
segment's matrix), of a function F of a vertex b < 2^v of a cube and of matrices A: at every vertex
b and for all A the value F b A is a constant k b plus at most n pieces, the same at all vertices
(`Sep`, `SepV`, `SPiece`, Cm/TargetReadBits.lean). What a piece is: the sentence "Separable …" of
Cm/TargetReadBitsBlk.lean's head holds here too.

Statements (`Cm.TR.Spec.sep_blocksV`, `Cm.TR.Spec.sep_cellV`) and proofs. Generic.


Why: Cm/TargetReadBits.lean's `Spec.sep_cell` and Cm/TargetReadBitsBlk.lean's `Spec.sep_blocks` ask,
at all numbers t < 2^|cs|, u < 2^|rs|, that under the guard gU the block is in the list (in
`Spec.sep_cell`: below Q) and that under the guards gT, gU the place lies in the shapes R, C. What a
walk over a model's families has at hand is a
statement on vertices: at every vertex b < 2^v every place that the atom reads lies in the shapes.
The proofs use the premises at t := the number of cs at b, u := the number of rs at b only.

Main names:
  `Spec.sep_blocksV`: as `Spec.sep_blocks`, the two premises in the form: for every vertex b < 2^v
    and every cell k < m, under the guards at b: the block is in L, the place lies in the shapes.
    Then at most |L| pieces.
  `Spec.sep_cellV`: the same for one cell (m = 1): unlike `Spec.sep_cell`, blocks from a list L, at
    most |L| pieces.

Limits: what the head of Cm/TargetReadBits.lean lists as not said is not said here either. That is:
that a model's atoms are separable; that reads are shared; anything on protocols, errors or cost. A
place whose row and column read the same variable is not taken in.

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsBlk

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset Cm.Seg

def Spec.sep_blocksV : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg m : ℕ) (L : List ℕ) (cs rs : List Src) (gT : ℕ → Prop)
      [DecidablePred gT] (gU : ℕ → ℕ → Prop) [∀ k, DecidablePred (gU k)] (c : ℕ → ℕ → E)
      (q : ℕ → ℕ → ℕ) (ρ : ℕ → ℕ → ℕ) (κ : ℕ → ℕ → ℕ),
    Src.OK (cs ++ rs) v → L.Nodup →
    (∀ b < 2 ^ v, ∀ k < m, gT (Src.num cs v b) → gU k (Src.num rs v b) →
      q k (Src.num rs v b) ∈ L ∧
      ρ (Src.num cs v b) (q k (Src.num rs v b)) < R seg ∧
      κ k (Src.num rs v b) < C seg) →
    SepV R C v L.length fun b A =>
      ∑ k ∈ range m, if gT (Src.num cs v b) ∧ gU k (Src.num rs v b) then
        c k (Src.num rs v b) *
          A seg (ρ (Src.num cs v b) (q k (Src.num rs v b))) (κ k (Src.num rs v b))
      else 0

def Spec.sep_cellV : Prop :=
  ∀ (E : Type) [Field E] (R C : ℕ → ℕ) (v seg : ℕ) (L : List ℕ) (cs rs : List Src)
      (gT gU : ℕ → Prop) [DecidablePred gT] [DecidablePred gU] (c : ℕ → E) (q : ℕ → ℕ)
      (ρ : ℕ → ℕ → ℕ) (κ : ℕ → ℕ),
    Src.OK (cs ++ rs) v → L.Nodup →
    (∀ b < 2 ^ v, gT (Src.num cs v b) → gU (Src.num rs v b) →
      q (Src.num rs v b) ∈ L ∧
      ρ (Src.num cs v b) (q (Src.num rs v b)) < R seg ∧
      κ (Src.num rs v b) < C seg) →
    SepV R C v L.length fun b A =>
      if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        c (Src.num rs v b) * A seg (ρ (Src.num cs v b) (q (Src.num rs v b))) (κ (Src.num rs v b))
      else 0

variable {E : Type} [Field E]

/-- One cell, summed over the blocks of the list; the premises under both guards. -/
theorem blocks_oneV (R C : ℕ → ℕ) (seg : ℕ) (L : List ℕ) (hL : L.Nodup) (pT pU : Prop)
    [Decidable pT] [Decidable pU] (c : E) (q0 κ0 : ℕ) (ρ : ℕ → ℕ) (A : ℕ → ℕ → ℕ → E)
    (hs : pT → pU → q0 ∈ L ∧ ρ q0 < R seg ∧ κ0 < C seg) :
    (L.map fun j =>
        ∑ r ∈ range (R seg), ∑ y ∈ range (C seg), (if pT ∧ r = ρ j then (1 : E) else 0) *
          (if pU ∧ q0 = j ∧ y = κ0 then c else 0) * A seg r y).sum =
      if pT ∧ pU then c * A seg (ρ q0) κ0 else 0 := by
  by_cases hT : pT
  · exact blocks_one R C seg L hL pT pU c q0 κ0 ρ A
      (fun hU => (hs hT hU).1) fun h1 h2 => (hs h1 h2).2
  · rw [if_neg fun h => hT h.1]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
    exact sum_eq_zero fun r _ =>
      sum_eq_zero fun y _ => by rw [if_neg (fun h : pT ∧ r = ρ j => hT h.1), zero_mul, zero_mul]

theorem sep_blocksV : Spec.sep_blocksV := by
  intro E _ R C v seg m L cs rs gT _ gU _ c q ρ κ hOK hL hs
  refine ⟨⟨fun _ => 0,
      L.map fun j =>
        ⟨seg, cs, rs, fun t r => if gT t ∧ r = ρ t j then 1 else 0,
          fun u y => ∑ k ∈ range m, if gU k u ∧ q k u = j ∧ y = κ k u then c k u else 0⟩⟩,
    fun b hb A => ?_, fun P hP => ?_, ?_⟩
  · have hs' := hs b hb
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
    generalize Src.num cs v b = t at hs' ⊢
    generalize Src.num rs v b = u at hs' ⊢
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
      (blocks_oneV R C seg L hL (gT t) (gU k u) (c k u) (q k u) (κ k u) (ρ t)
        A (hs' k (mem_range.1 hk))).symm
  · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hP
    exact hOK
  · exact le_of_eq (List.length_map _)

theorem sep_cellV : Spec.sep_cellV := by
  intro E _ R C v seg L cs rs gT gU _ _ c q ρ κ hOK hL hs
  refine sep_congr E R C v L.length _ _ (fun b _ A => ?_)
    (sep_blocksV E R C v seg 1 L cs rs gT (fun _ => gU) (fun _ => c) (fun _ => q) ρ (fun _ => κ)
      hOK hL fun b hb _ _ => hs b hb)
  show _ = ∑ k ∈ range 1, if gT (Src.num cs v b) ∧ gU (Src.num rs v b) then
        c (Src.num rs v b) * A seg (ρ (Src.num cs v b) (q (Src.num rs v b))) (κ (Src.num rs v b))
      else 0
  rw [sum_range_one]

end Cm.TR
