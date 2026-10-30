-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/SixBefore.lean: the six statements on the two lookups of a link (SixAt,
Johnson/AtFull/K3X/SixAt.lean) at the 24 links in front of the output head's, at a public part whose
layers' structure and plans are what the makers return at the full size. A joining: the general laws
of KernelTests.lean, the three closed facts (KernelNames.lean, KernelLayers.lean, KernelAtt.lean),
and at_witnesses (Johnson/AtFull/Public/AtWitnesses.lean), which carries a closed fact at the makers
to the letters of the makers' own equations.

  **`six_layers`**: SixAt X (2 g) for g < 12. Premises beside the makers' equations: the layers'
    sixteen counts of padding keys and the host's count are the written list (paid by laws:
    CountsAtFull.lean, LaidAtFull.lean).
  **`six_attention`**: SixAt X (2 g + 1) for g < 12. Premise beside the makers' equations: the test
    on the padding key accepts at each plan (paid by a law: PadKeyLaw.lean).

Limits. Every premise is a premise: that the makers return is said where the public part's value is
joined. THE LETTERS y, sc, .. ARE NO LAW'S LETTERS: the premise OpensAt y is asked at every test, so
only the full-size layout (yFull, Johnson/AtFull/Public/Values.lean) can meet it: the two theorems
are instances at the full size, written in letters. They count for nothing until they are joined.
The full size alone. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.K3X.KernelNames
import Johnson.AtFull.K3X.KernelLayers
import Johnson.AtFull.K3X.KernelAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (atMakers at_witnesses OpensAt Makers)
open OnBytes.Road.K4.Trial.AttL2 (AOf)
open VerifiableInference.Desc.First.Look (laidLayers padKeyAtt)
open Johnson.AtFull.Lots.K3 (pubW)

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **THE LAYERS' TWELVE LINKS.** -/
theorem six_layers (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA)
    {X : Verify.Public} (hN : X.NGr = 12) (h4 : X.p4 = true) (eL : X.layers = layers)
    (eG : X.G = G) (hpub : layers.y.fo.pub = pubW 0 false)
    (hlaid : laidLayers layers = some (pubW 0 false)) : ∀ g, g < 12 → SixAt X (2 * g) :=
  six_even h4 hN names_W (by rw [eL, eG]; exact at_witnesses O M layers_W) (by rw [eL]; exact hpub)
    (by rw [eL]; exact hlaid)

/-- **THE ATTENTION's TWELVE LINKS.** -/
theorem six_attention (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA)
    {X : Verify.Public} (hN : X.NGr = 12) (h4 : X.p4 = true)
    (eA : X.A = AOf ps.toArray seenA)
    (hk : ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → padKeyAtt a.S = true) :
    ∀ g, g < 12 → SixAt X (2 * g + 1) :=
  six_odd h4 hN names_W (by rw [eA]; exact at_witnesses O M att_W) hk

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.six_layers
#print axioms Johnson.AtFull.K3X.six_attention
