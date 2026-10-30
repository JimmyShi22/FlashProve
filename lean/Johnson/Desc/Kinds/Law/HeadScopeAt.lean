-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadScopeAt.lean: THE SCOPE's READER PAYS HeadScope (Law/SameRequestOf.lean): at the sizes that the head's place is
given of the verifier's public record X (the head's public numbers X.hS), under the public hypotheses on
the layers and the head (Johnson/Road/HeadL5Pub.lean: LayersHeadAt X: from the verifier's own call publicOf and
the list of the parameter file's numbers): T = 1024, V = 202048, d = 5120 are the reference parameters', AND
sh = 8. SO "sh = 8" IS A FACT OF THE FILES IN SCOPE, READ OFF THE PARAMETER FILE: no test of the kind or of a program is
narrowed for it: a parameter file with sh = 7 passes the kind's tests and lies outside the theorem's scope.
THE SIZES ARE TYPED HERE AS A RECORD OF X.hS's FIELDS: the harness's sizesOf (Johnson/Stored/HeadSeatAt.lean) is that record,
field for field, and reducible: this file does not import the harness.
It names two records of `verify-on-bytes` (Model.Verify.Public, Model.Head.Shape): data alone.

-/
import Mathlib
import Johnson.Road.HeadL5Pub
import Johnson.Desc.Kinds.Law.SameRequestOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes
open Inst.Model (ppref)

/-- The head's sizes, of the head's public numbers: the harness's sizesOf, field for field. -/
@[reducible] def sizesAt (h : Model.Head.Shape) : Sizes :=
  { lt := h.lt, ls := h.ls, d := h.d, MF := h.MF, KF := h.KF, epsF := h.epsF, V := h.V,
    sh := h.digSh, F := h.famF }

theorem headScope_of_full (h : Model.Head.Shape) (hF : OnBytes.Road.Hd.FullH h) (hsh : h.digSh = 8) :
    @HeadScope (sizesAt h) ppref := by
  letI := sizesAt h
  refine ⟨?_, hF.V, hF.d, hsh⟩
  show 2 ^ h.lt = 1024
  rw [hF.lt]

/-- **The scope's reader pays HeadScope.** -/
theorem headScope_of_public (X : Model.Verify.Public) (A : OnBytes.Road.Hd.LayersHeadAt X) :
    @HeadScope (sizesAt X.hS) ppref :=
  headScope_of_full X.hS A.full A.sh

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headScope_of_public
