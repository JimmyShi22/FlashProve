-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/SameCellsTraceAt.lean: sameCells_trace
(Honest/K6/Law/SameCellsTrace.lean) WITH ITS WEIGHTIEST PREMISE CUT TO WHAT IS READ: UNDER SIX
PREMISES, of which one is that the honest side's reader's matrices are the images of list 24 of the
trace AT THE PLACES OF THE FEATURES AND POSITIONS THAT THE HEAD's RELATION NAMES, AND NOWHERE ELSE
(ReaderMeets): the cells that the honest side of the sub-protocol "the output head's own rounds"
makes (headCellsOf, Honest/K6/Wit.lean) and the cells read off a trace (traceCells) ARE THE SAME ON
WHAT THE HEAD's RELATION NAMES (SameCells, Kinds/Law/CellsAlike.lean).

Why. sameCells_trace asks its reader at ALL numbers, rows and columns: of the matrix of planes
(number NHf + 2 of the head's list), of numbers beyond the list and of places beyond the ranges too.
SameCells names four ranges. A reader that is not the trace's image at a place that nobody reads
fails that premise and meets this one.

What it is not. CONDITIONAL ON SIX PREMISES, NONE OF WHICH IS MET HERE but through
readerMeets_of_all. The reader c, the weights Wh, the honest side's numbers N, the trace T, the
public part X, the index i and the four classes are letters. The places are the library's placeH
(Johnson/HonestTrace/Full.lean) at X: which numbers of the list they are is not said here. No
verifier's state, no round and no run stands in it. Nothing on soundness, on completeness or on what
a proof hides.

  HeadMatAt            at one place the reader's matrix is the image of list 24 of the trace. A
                       definition for statements alone.
  ReaderMeets          HeadMatAt at the places of the four matrices' features, inside SameCells' own
                       four ranges. A definition for statements alone.
  readerMeets_of_all   sameCells_trace's premise hM (all numbers, rows and columns) gives it.
  sameCells_trace_at   the main statement.
CALLED: valMinAbs_cast (Johnson/HonestTrace/Packed.lean). That Hd.cellsH reads the entry at placeH
holds by unfolding, as the library's cellsH_placeH (Johnson/HonestTrace/Full.lean) has it for lists
of integers.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCells
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Desc.Kinds.Law.CellsAlike
import Johnson.HonestTrace.Packed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6

open Inst.Model (ppref)
open OnBytes.Model.Verify (borderOf)
open OnBytes.HonestTrace (Tr placeH)
open VerifiableInference.Desc.Kinds (Head.Sizes Head.Policy Head.Request Head.Token Norm.T NR)
open VerifiableInference.Desc.Kinds.Norm (d)
open VerifiableInference.Desc.Kinds.Head (V JV)
open VerifiableInference.Desc.Kinds.Head.Law (SameCells)
open VerifiableInference.Desc.Kinds.Head.Law.Came (traceCells)

/-- At one place (number in the head's list, row, column) the honest side's reader's matrix is the
image in the field of list 24 of the trace. A definition for statements alone. -/
def HeadMatAt (N : HeadWhere) (c : Cells) (T : Tr) (p : Nat × Nat × Nat) : Prop :=
  headMats N c p.1 p.2.1 p.2.2 = ((T 24 p.1 p.2.1 p.2.2 : Int) : Cb.Gl.F)

/-- **The reader meets the trace where the head's relation reads**: at the library's place of each
feature and position inside the four ranges of SameCells. A definition for statements alone. -/
structure ReaderMeets [Head.Sizes] (X : OnBytes.Model.Verify.Public) (N : HeadWhere) (c : Cells)
    (T : Tr) : Prop where
  wide : ∀ f t, f < 4 * d + 6 * JV → t < Norm.T → HeadMatAt N c T (placeH X .hf f t)
  act : ∀ f t, f < 2 * d → t < Norm.T → HeadMatAt N c T (placeH X .hd f t)
  row : ∀ f t, f < NR + 21 → t < Norm.T → HeadMatAt N c T (placeH X .hr f t)
  stream : ∀ f t, f < 5 * d → t < Norm.T → HeadMatAt N c T (placeH X .x f t)

/-- sameCells_trace's premise hM, at all numbers, rows and columns, gives it. -/
theorem readerMeets_of_all [Head.Sizes] (X : OnBytes.Model.Verify.Public) (N : HeadWhere)
    (c : Cells) (T : Tr)
    (hM : ∀ n r k, headMats N c n r k = ((T 24 n r k : Int) : Cb.Gl.F)) : ReaderMeets X N c T :=
  ⟨fun _ _ _ _ => hM _ _ _, fun _ _ _ _ => hM _ _ _, fun _ _ _ _ => hM _ _ _,
    fun _ _ _ _ => hM _ _ _⟩

/-- **THE HONEST SIDE's CELLS AND THE CELLS OFF THE TRACE ARE THE SAME ON WHAT THE RELATION NAMES**,
where the reader meets the trace at the places that are read. -/
theorem sameCells_trace_at [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token]
    {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {T : Tr} (N : HeadWhere) (c : Cells)
    (Wh : Nat → Nat → Int) (h1 : N.shape = X.hS) (h2 : N.lay = X.HLy)
    (h3 : N.border = borderOf X.y) (hM : ReaderMeets X N c T)
    (hs : ∀ a r k, |T 24 a r k| < 129)
    (hWh : ∀ k v, k < d → v < V →
      Wh k v = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v) :
    SameCells (headCellsOf N c Wh) (traceCells X i T) := by
  have back : ∀ p : Nat × Nat × Nat, HeadMatAt N c T p →
      ZMod.valMinAbs (headMats N c p.1 p.2.1 p.2.2) = T 24 p.1 p.2.1 p.2.2 := fun p hp => by
    rw [show headMats N c p.1 p.2.1 p.2.2 = ((T 24 p.1 p.2.1 p.2.2 : Int) : Cb.Gl.F) from hp]
    exact OnBytes.HonestTrace.valMinAbs_cast (lt_trans (hs _ _ _) (by norm_num))
  refine ⟨fun f t hf ht => ?_, fun f t hf ht => ?_, fun f t hf ht => ?_, fun f t hf ht => ?_, hWh⟩
  · show ZMod.valMinAbs ((OnBytes.Road.Hd.cellsH N.shape N.lay N.border (headMats N c)).hf f t) = _
    rw [h1, h2, h3]
    exact back _ (hM.wide f t hf ht)
  · show ZMod.valMinAbs ((OnBytes.Road.Hd.cellsH N.shape N.lay N.border (headMats N c)).hd f t) = _
    rw [h1, h2, h3]
    exact back _ (hM.act f t hf ht)
  · show ZMod.valMinAbs ((OnBytes.Road.Hd.cellsH N.shape N.lay N.border (headMats N c)).hr f t) = _
    rw [h1, h2, h3]
    exact back _ (hM.row f t hf ht)
  · show ZMod.valMinAbs ((OnBytes.Road.Hd.cellsH N.shape N.lay N.border (headMats N c)).x f t) = _
    rw [h1, h2, h3]
    exact back _ (hM.stream f t hf ht)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.HeadMatAt
#print axioms ProofFile.Honest.K6.ReaderMeets
#print axioms ProofFile.Honest.K6.readerMeets_of_all
#print axioms ProofFile.Honest.K6.sameCells_trace_at
