-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPub0.lean.
The calls' lookup's share of a link's public record at attention: its first slot is the number 0.

Fo.Pub2.lookPubA_ok (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean) has the first slot as
a.seam.Fp.next. Where Verify.publicOf returns X, that number is 0 at every member of X.A
(Fo.Next0.planned_next0, OnBytes/Tie/Pv/Lookup/Ends/FoNext0.lean). At the head it is 0 by the
record's own text (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubH.lean).

Main name:
  `lookPubA_ok0`: Fo.Pub2.LookPubOK of lookPubA at the first slot 0. Premises: Verify.publicOf
    returns X; a is a member of X.A.
Limits: those of OnBytes/Tie/Pv/Lookup/Ends/FoLookPubA.lean. No file but FoBoxAH.lean calls
`lookPubA_ok0`. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoNext0
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends

theorem lookPubA_ok0 {M₀ : Type} (rdA : M₀ → IxA → Cb.Gl.E) {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    (g : ℕ) (a : Attention.Plan) (hg : X.A[g]? = some a) (nR nC : ℕ) (St : Type) :
    LookPubOK (lookPubA rdA a nR nC St) (a.S.calls.map (·.call)) a.fs.pub a.lid a.S.cf.lmb 0 maskJ
      (cellJ (a.S.cf.NAs + 2)) := by
  have k := lookPubA_ok rdA h g a hg nR nC St
  rw [(Fo.Next0.planned_next0 h).2 g a hg] at k
  exact k

end Fo.Pub2
