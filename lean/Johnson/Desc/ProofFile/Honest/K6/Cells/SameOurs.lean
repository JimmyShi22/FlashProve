-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/SameOurs.lean: the cells that the honest side of the
sub-protocol "the output head's own rounds" (K6) makes (`headCellsOf`, Honest/K6/Wit.lean) and the
cells that the head's law reads off a witness (`compCut`, Johnson/Desc/Kinds/Law/K6Cut.lean) are the
same inside the ranges that the head's relation names (`SameCells`, Law/CellsAlike.lean). One lemma,
by calls. No goal is stated.

WHAT IT IS NOT. CONDITIONAL ON SIX PREMISES, NONE OF WHICH IS MET HERE: the public numbers are the
law's (h1, h2, h3); the geometry of the four ranges (hG: `InRanges`, Law/HeadCellsMeet.lean); inside
the four ranges (`InFour`, Law/K6Cut.lean) the reader's cell, as the integer of least absolute
value, is segment 24's own integer off the witness (hM); the weights meet (hW). INSIDE THE RANGES
ALONE: of a cell outside them nothing is said. No thread, no run, no state of the verifier's, no
measure. The reader c of the cells and the weights Wh are letters.

  `sameCells_ours`  **the two are the same**, in the form of the library's `sameCells_head`
                    (Law/HeadCellsMeet.lean), whose left side is another reading of the cells

WHO PAYS WHAT. Each of the four ranges: hM through `ownCut` (Law/K6Cut.lean), at the place that
`InRanges`' field for that range gives. The weights: hW as it stands. `P5J.ownQ`:
Johnson/P5J/CellQ.lean.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Wit
import Johnson.Desc.Kinds.Law.HeadCellsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K6
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc (Wit)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)
open VerifiableInference.Desc.Kinds (Head.Sizes)
open VerifiableInference.Desc.Kinds.Norm (d)
open VerifiableInference.Desc.Kinds.Head (V)
open VerifiableInference.Desc.Kinds.Head.Law (SameCells InRanges InFour compCut ownCut whOf)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE HONEST SIDE's CELLS AND THE CELLS THAT THE HEAD's LAW READS OFF A WITNESS ARE THE SAME
INSIDE THE RANGES THAT THE HEAD's RELATION NAMES**, where the public numbers are the law's (h1, h2,
h3), the geometry holds (hG), inside the four ranges the reader's cell, as the integer of least
absolute value, is segment 24's own integer off the witness (hM), and the weights meet (hW). In the
form of `sameCells_head` (Johnson/Desc/Kinds/Law/HeadCellsMeet.lean), whose left side is another
reading. No thread and no run is read here. -/
theorem sameCells_ours [Head.Sizes] (Nw : HeadWhere) (c : Cells) (Wh : Nat → Nat → Int)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h1 : Nw.shape = Wp.hS) (h2 : Nw.lay = Wp.HLy) (h3 : Nw.border = borderOf Wp.y)
    (hG : InRanges Wp.hS Wp.HLy (borderOf Wp.y))
    (hM : ∀ a r k, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r k →
      (ZMod.valMinAbs (headMats Nw c a r k) : Int) = P5J.ownQ cs arr msR N s seat w 24 a r k)
    (hW : ∀ k v, k < d → v < V → Wh k v = whOf w.cells k v) :
    SameCells (headCellsOf Nw c Wh) (compCut cs arr msR N s seat Wp pl w).1 := by
  have key : ∀ a r k, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r k →
      (ZMod.valMinAbs (headMats Nw c a r k) : Int) = ownCut cs arr msR N s seat Wp w a r k :=
    fun a r k hin => (hM a r k hin).trans (if_pos hin).symm
  unfold headCellsOf
  rw [h1, h2, h3]
  exact ⟨fun f t hf ht => key _ _ _ (hG.wide f t hf ht),
    fun f t hf ht => key _ _ _ (hG.act f t hf ht),
    fun f t hf ht => key _ _ _ (hG.row f t hf ht),
    fun f t hf ht => key _ _ _ (hG.stream f t hf ht), hW⟩

#print axioms sameCells_ours

end ProofFile.Honest.K6
