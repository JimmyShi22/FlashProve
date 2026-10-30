-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkPlanesAt.lean: what `Wf.planesAt` adds to a row.

`Wf.planesAt x codes i row v` (OnBytes/Iop/Wf.lean) adds a vector v on the multiplicities of lookup
number i to a row: one structured vector on the main table of the prover's message for each block of
planes of that lookup. This file joins OnBytes/Slice/BlkPlanes.lean (what the blocks' vectors add up
to) and OnBytes/Slice/BlkLayout.lean (the blocks of the layout, each by itself) with the law on a
row's coefficients (OnBytes/Iop/RowLaws.lean: `Row.coefficient_val`).

The result (`planesAt_value`), under any reading of the program's elements and for any table T given
by the index of an entry: the sum over the indices of the main table of the new row's coefficients
times T is that of the old row, plus the sum over all planes j and rows t of v's entry at j + 2 ^ mu
t times the bit at (t, j) (`bitsOf`: OnBytes/Slice/BlkPlanes.lean's `bitAt` at the lookup's blocks).
On every other table the row's coefficients stay, and so does its target.

Asked: v is of product form and has mu + d variables; the lookup is in order; the layout's first
block fits a row of the table (a clause of `Wf.admitted`).

Main definitions: `blocksOf`, `bitsOf`.
Main theorems: `foldl_add`, `planesAt_terms`, `planesAt_coefficient`, `planesAt_target`,
`planesAt_value`.

Not claimed. What the table is. That the bits are 0 or 1. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkLayout
import OnBytes.Iop.RowLaws

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open OnBytes.Model (Reading)
open OnBytes.Params (WfLookup WfPublic)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The code of the main rows of the prover's message. -/
def codeOf (x : WfPublic) (codes : Codes) : Code := codes.base.getD x.message.shape.code default

/-- The blocks of planes of lookup number i, as they are laid. -/
def blocksOf (x : WfPublic) (codes : Codes) (i : ℕ) : List Wf.Block :=
  (Wf.layout x.lookups (codeOf x codes).ell).filter (·.lookup == i)

/-- The bit at (row t, plane j) of lookup number i, read off the main table T of the prover's
message. -/
def bitsOf (x : WfPublic) (codes : Codes) (i : ℕ) (T : ℕ → K) (t j : ℕ) : K :=
  bitAt (ceilLog2 x.message.shape.mainRows) (codeOf x codes).logEll (blocksOf x codes i) T t j

/-- Vectors added to a row one after the other. -/
theorem foldl_add {α : Type} (o : ℕ) (part : Part) (f : α → Tensor) : ∀ (l : List α) (r : Row),
    (l.foldl (fun r b => r.add o part (f b)) r).terms.toList =
        r.terms.toList ++ l.map (fun b => ⟨o, part, f b⟩) ∧
      (l.foldl (fun r b => r.add o part (f b)) r).units = r.units ∧
      (l.foldl (fun r b => r.add o part (f b)) r).runs = r.runs ∧
      (l.foldl (fun r b => r.add o part (f b)) r).forms = r.forms ∧
      (l.foldl (fun r b => r.add o part (f b)) r).target = r.target
  | [], r => by simp
  | b :: l, r => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := foldl_add o part f l (r.add o part (f b))
    rw [List.foldl_cons]
    refine ⟨?_, h2, h3, h4, h5⟩
    rw [h1]
    simp [Row.add]

/-- The terms that are added, and what stays. -/
theorem planesAt_terms (x : WfPublic) (codes : Codes) (i : ℕ) (row : Row) (v : Tensor) :
    (Wf.planesAt x codes i row v).terms.toList =
        row.terms.toList ++ (blocksOf x codes i).map (fun b => ⟨x.messageId, .main,
          blockTensor v (x.lookups.getD i default).mu (ceilLog2 x.message.shape.mainRows)
            (codeOf x codes).logEll b⟩) ∧
      (Wf.planesAt x codes i row v).units = row.units ∧
      (Wf.planesAt x codes i row v).runs = row.runs ∧
      (Wf.planesAt x codes i row v).forms = row.forms ∧
      (Wf.planesAt x codes i row v).target = row.target :=
  foldl_add x.messageId .main (fun b => blockTensor v (x.lookups.getD i default).mu
    (ceilLog2 x.message.shape.mainRows) (codeOf x codes).logEll b) (blocksOf x codes i) row

/-- The target stays. -/
theorem planesAt_target (x : WfPublic) (codes : Codes) (i : ℕ) (row : Row) (v : Tensor) :
    (Wf.planesAt x codes i row v).target = row.target := (planesAt_terms x codes i row v).2.2.2.2

/-- The coefficients of the new row. -/
theorem planesAt_coefficient (x : WfPublic) (codes : Codes) (i : ℕ) (row : Row) (v : Tensor)
    (o : ℕ) (part : Part) (idx : ℕ) :
    ρ.val ((Wf.planesAt x codes i row v).coefficient o part idx) =
      ρ.val (row.coefficient o part idx) +
        (if x.messageId = o ∧ Part.main = part then
          ((blocksOf x codes i).map fun b =>
            ρ.val ((blockTensor v (x.lookups.getD i default).mu
              (ceilLog2 x.message.shape.mainRows) (codeOf x codes).logEll b).entry idx)).sum
          else 0) := by
  obtain ⟨h1, h2, h3, h4, _⟩ := planesAt_terms x codes i row v
  rw [Row.coefficient_val, Row.coefficient_val, h1, h2, h3, h4, List.map_append, List.sum_append,
    List.map_map]
  have e : ((blocksOf x codes i).map ((fun t : Term =>
      if t.oracle = o ∧ t.part = part then ρ.val (t.v.entry idx) else 0) ∘ fun b =>
        ⟨x.messageId, .main, blockTensor v (x.lookups.getD i default).mu
          (ceilLog2 x.message.shape.mainRows) (codeOf x codes).logEll b⟩)).sum =
      (if x.messageId = o ∧ Part.main = part then
        ((blocksOf x codes i).map fun b =>
          ρ.val ((blockTensor v (x.lookups.getD i default).mu
            (ceilLog2 x.message.shape.mainRows) (codeOf x codes).logEll b).entry idx)).sum
        else 0) := by
    by_cases hc : x.messageId = o ∧ Part.main = part
    · rw [if_pos hc]
      refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
      show (if x.messageId = o ∧ Part.main = part then _ else 0) = _
      rw [if_pos hc]
    · rw [if_neg hc]
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
      show (if x.messageId = o ∧ Part.main = part then _ else 0) = _
      rw [if_neg hc]
  rw [e]
  ring

/-- What `Wf.planesAt` adds to a row, on the main table of the prover's message. -/
theorem planesAt_value (x : WfPublic) (codes : Codes) (i : ℕ) (l : WfLookup) (row : Row)
    (v : Tensor) (hi : x.lookups[i]? = some l) (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout x.lookups (codeOf x codes).ell).head?.any fun b =>
      decide (2 ^ b.bits ≤ (codeOf x codes).ell)) = true)
    (hv : v.denseVars = []) (hn : v.pairs.length = l.mu + l.d) (T : ℕ → K) :
    ∑ J ∈ Finset.range (2 ^ ((codeOf x codes).logEll + ceilLog2 x.message.shape.mainRows)),
        ρ.val ((Wf.planesAt x codes i row v).coefficient x.messageId .main J) * T J =
      ∑ J ∈ Finset.range (2 ^ ((codeOf x codes).logEll + ceilLog2 x.message.shape.mainRows)),
          ρ.val (row.coefficient x.messageId .main J) * T J +
        ∑ j ∈ Finset.range (2 ^ l.mu), ∑ t ∈ Finset.range (2 ^ l.d),
          ρ.val (v.entry (j + 2 ^ l.mu * t)) * bitsOf x codes i T t j := by
  have hg : x.lookups.getD i default = l := by
    rw [List.getD_eq_getElem?_getD, hi]
    rfl
  have hb := blocks_value ρ v l.mu l.d (ceilLog2 x.message.shape.mainRows)
    (codeOf x codes).logEll hv hn T (blocksOf x codes i)
    (layout_fits x.lookups (codeOf x codes).ell i l hi hl hh)
  unfold bitsOf
  rw [← hb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [planesAt_coefficient, if_pos ⟨rfl, rfl⟩, hg, add_mul]

end OnBytes.Slice.Planes
