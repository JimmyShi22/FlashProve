-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/PublicAtCutMore.lean: the conclusions of five laws of the library on
what `publicOf` returns, each to the letter, from `PublicCut pol KL X`
(Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean) in the place of the premise "`publicOf pol KL layout
= .ok X`".

`PublicCut pol KL X` holds wherever `publicOf`, or `publicOfO o` at any o, returns X, and it names
no hash. So a law that spends only these conclusions can take `PublicCut` as its premise and holds
at every o.

Row or tool. Every declaration here is a tool: rules for all files and all records. No description
of the protocol is named.

What is here. Each is a clause of `PublicCut`, or one step from one.
  `cut_layout`: the first clause of `Fo.Pub.publicOf_cut`
    (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean): `polLayout pol` returns the scan and the layout that
    X holds.
  `cut_scan`: the conclusion of `Verify.publicOf_scan` (OnBytes/Model/VerifyDerives.lean): the scan
    in X is the strict scan of the parameter file. By `polLayout_scan` (the same file).
  `cut_reads`: the conclusion of `Fit.public_reads` (OnBytes/Model/Fit/LayerCaps.lean).
  `cut_G`: the conclusion of `Fo.Pub.public_G`: a member of X.G is what `Layer.planG` returns. By
    `plansG_at`.
  `cut_H`: the conclusion of `Fo.Pub.public_H`: X.H is what `Head.planH2` returns, but for one
    field.
The conclusion of `Fo.Pub.public_A` is `cut_A`, in Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean.

Limits. Those of Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean. Nothing on soundness.


-/
import Johnson.Desc.Ok.PlanWritten.PublicAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model Fo.Pub

variable {pol KL : ByteArray} {X : Verify.Public}

/-- `polLayout pol` returns the scan and the layout that X holds. -/
theorem cut_layout (C : PublicCut pol KL X) : Verify.polLayout pol = .ok (X.P, X.layers.y) := C.1.1

/-- The scan in X is the strict scan of the parameter file. -/
theorem cut_scan (C : PublicCut pol KL X) : polScan pol = .ok X.P :=
  Verify.polLayout_scan (cut_layout C)

/-- The tables of reads in X are `readsOf`'s at its layout. -/
theorem cut_reads (C : PublicCut pol KL X) : Layer.readsOf X.layers.y = .ok X.layers.rd := C.2

/-- The members of X.G come from `Layer.planG`. -/
theorem cut_G (C : PublicCut pol KL X) (g : Nat) (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) :
    Layer.planG X.layers g (if g = 0 then none else X.G[g - 1]?) = .ok hp :=
  plansG_at X.layers X.G C.1.2.2.1 g hp hg

/-- X.H comes from `Head.planH2`. -/
theorem cut_H (C : PublicCut pol KL X) :
    ∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
      X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL } :=
  C.1.2.2.2.2.1

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.cut_layout
#print axioms VerifiableInference.PlanWritten.cut_scan
#print axioms VerifiableInference.PlanWritten.cut_reads
#print axioms VerifiableInference.PlanWritten.cut_G
#print axioms VerifiableInference.PlanWritten.cut_H
