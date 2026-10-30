-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersSymbolsPlanesSizesPaid.lean

On public data. One theorem, by two calls.

THE PREMISE "planesSizes" of EntersSymbolsShapes.lean and what stands on it, UNDER THE HEAD: by the lookups'
"planesSizesAreTheFillingsUnderTheHead" (Johnson/Desc/ProofFile/Honest/K3/Term/PlanesSizesAreTheFillings.lean) at the tail that their
"linksTailIsTheMeanings" (…/PackedTraceCellsAtTheHonestTrace.lean) names. "Meaning.sizesOf X link" is "szOf (Meaning.tlAt X link)" by
unfolding.

Limits. THIS STANDS WHERE Johnson/Desc/ProofFile/Honest/K3/Term/PlaneNumbersInScope.lean imports
Johnson.HonestTrace.PlaneLookNumbersInScope, whose laws it and PlanesSizesAreTheFillings.lean
call: there the three laws are proved over the library's public side. By that import nothing of the
executable model's folder Johnson/HonestTrace/Run comes beneath this file. The files that take
"planesSizes" as a premise do not stand over Johnson.HonestTrace.PlaneLookNumbersInScope.
-/
import Johnson.HonestTrace.Joint.EntersSymbolsShapes
import Johnson.Desc.ProofFile.Honest.K3.Term.PackedTraceCellsAtTheHonestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Meaning (sizesOf)
open P5J (AtMgA TS)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {xp : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head the planes' matrices have the filling's sizes, at all 25 links.** -/
theorem planes_sizes_under_the_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xp) :
    ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (sizesOf (P5J.At.X Zp) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (sizesOf (P5J.At.X Zp) link).k number = (Sz.ref.shapeNo link number).2 :=
  fun _ below => ProofFile.Honest.K3.Term.planesSizesAreTheFillingsUnderTheHead h below
    (ProofFile.Honest.K3.Term.linksTailIsTheMeanings h.scope h.reads h.pubOne below)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.planes_sizes_under_the_head
