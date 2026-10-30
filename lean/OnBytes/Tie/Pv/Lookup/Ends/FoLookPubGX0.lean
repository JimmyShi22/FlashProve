-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubGX0.lean.
The calls' lookup's share of a link's public record at a group of layers: its first slot is the
number 0.

Fo.Pub2.lookPubGX_ok (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubGX.lean) has the first slot as hp.Fp.next,
for every hp. Where Verify.publicOf returns X, that number is 0 at every member hp of X.G
(Fo.Next0.planned_next0, OnBytes/Tie/Pv/Lookup/Ends/FoNext0.lean).

Main name:
  `lookPubGX_ok0`: Fo.Pub2.LookPubOK of lookPubGX at the first slot 0, at a member of X.G.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoNext0
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubGX

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.G

theorem lookPubGX_ok0 {M₀ : Type} (rdG : M₀ → IxGw → Cb.Gl.E) {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Verify.Public} (h : Verify.publicOf pol KL layout = .ok X)
    (g : ℕ) (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) (nM nR nC wR wC : ℕ) (St : Type) :
    LookPubOK (lookPubGX rdG X g hp nM nR nC wR wC St) X.layers.y.cl X.layers.y.fo.pub
      X.layers.y.h.lidb X.layers.y.h.lmb 0 maskH (cellH (Layer.matIx X.layers.y).iB) := by
  have k := lookPubGX_ok rdG h g hp nM nR nC wR wC St
  rw [(Fo.Next0.planned_next0 h).1 g hp hg] at k
  exact k

end Fo.Pub2
