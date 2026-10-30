-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackSides.lean: the form parts of the verifier's two long vectors, place by place,
as sums of the library's blocks, if each placed panel has the sides of its member of the library's
list.

Johnson/Road/K4/PanelSides.lean says what one pair of panels has in common (SidesAre);
Johnson/Road/K4/PanelsBlocks.lean turns a long vector over the verifier's placed panels into blocks
over the library's panels. Here the two are joined.

Main names:
  `faOf`, `fbOf`: the library's two factors of an entry of a panel, the first with all weights.
  `vaOf`, `vbOf`: the form part of a panel's block on each side: 0 for a panel whose A side is a
    never-sent vector, or whose B side is a weight matrix.
  `vecs_of_sides`: the two long vectors without never-sent vectors and weight claims' vectors.
Limits. The premise F2 asks SidesAre of every pair; nothing here shows it. An identity in one world:
nothing on a run, on soundness or on hiding.


-/
import Johnson.Road.K4.PanelSides
import Johnson.Road.K4.PanelsBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World)
open OnBytes.Model.Layer (Lay SBlk placePanels)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim LW Pan Rd pans wc call)
open Cb.Pv.Lay.At (isVirt blk nP cellOf)

variable {K : Type} [Field K] [scl : Scl]

/-- The first factor of an entry of a panel, with all weights. x: the weight of claim 1. -/
def faOf (D : Dim) (r : Rd K) (z : ℕ → K) (x : K) (pn : Pan) (i j : ℕ) : K :=
  pn.om x * wc D z (call pn.fam) * pn.wt D z i * pn.A D r i j

/-- The form part of a panel's block of the first long vector. -/
def vaOf (D : Dim) (r : Rd K) (z : ℕ → K) (x : K) (pn : Pan) (t : ℕ) : K :=
  if isVirt pn = true then 0 else cellOf D pn (faOf D r z x pn) t

/-- The form part of a panel's block of the second long vector. -/
def vbOf (D : Dim) (r : Rd K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K) (pn : Pan)
    (t : ℕ) : K :=
  if pn.weight = true then 0 else cellOf D pn (pn.B D r tb L0 w z zh) t

/-- **The two long vectors' form parts, as blocks.** -/
theorem vecs_of_sides {ρ : Reading K} {W : World K} {y : Lay} {om : Array E} {D : Dim} {r : Rd K}
    {tb : Tables} {L0 : ℕ} {w : ℕ → LW K} {z zh : ℕ → K} {x : K} (bl : Array SBlk)
    (F2 : List.Forall₂ (fun b pn => SidesAre ρ W y om D r tb L0 w z zh x b pn)
      (placePanels bl).1.toList (pans D)) (Y : ℕ) :
    vecOf (aG ρ W y om fun _ _ => 0) (placePanels bl).1.toList Y =
        ((pans D).map fun pn => blk (pn.wid D) (nP D pn) (vaOf D r z x pn) Y).sum ∧
      vecOf (bG ρ W fun _ _ => 0) (placePanels bl).1.toList Y =
        ((pans D).map fun pn => blk (pn.wid D) (nP D pn) (vbOf D r tb L0 w z zh pn) Y).sum := by
  refine ⟨vecOf_blocks D bl (F2.imp fun b pn e => ⟨e.bw, fun t _ => ?_⟩) Y,
    vecOf_blocks D bl (F2.imp fun b pn e => ⟨e.bw, fun t _ => ?_⟩) Y⟩
  · rw [e.bwy, e.sa]
    rfl
  · rw [e.bwy, e.sb]
    rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.vecs_of_sides
