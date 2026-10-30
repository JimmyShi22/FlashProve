-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/NoSplitAtHead.lean: "THE OWN GROUP NEEDS NO SPLIT" FROM THE ONE HEAD ALONE. One theorem: two calls.

  **`hsp_at_head`**: (K13.whereOf Zp).lin.ownSplitNeeded = false, from h : P5J.AtMg …: the first chain's own copy of the
    shape is the batch's as sized (`P5J.linOne`, Johnson/P5J/Cols13Paid.lean, from h.laid), and the planner's gate refuses a
    split there (`noOwnSplit_at_seat`, Johnson/Desc/Last/ShapeNoSplit.lean, from h.laid.pub).

What stays a premise. The head.
Limits. It reads neither `AtMg.rc` nor `AtMg.rch`: it stands whatever these two are. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeNoSplit
import Johnson.P5J.Cols13Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Maker

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- **The own group needs no split: from the head alone.** -/
theorem hsp_at_head {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) :
    (K13.whereOf Zp).lin.ownSplitNeeded = false := by
  show Zp.first.lin.ownSplitNeeded = false
  rw [P5J.linOne h.laid]
  exact noOwnSplit_at_seat (o := o) (pol := Z.pol) (lay := Z.lay) (KL := Z.KL) h.laid.pub

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.hsp_at_head
