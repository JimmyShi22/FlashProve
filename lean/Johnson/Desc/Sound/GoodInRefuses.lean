-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/GoodInRefuses.lean: A CLAUSE OF A LAW'S CONDITION IN FRONT THAT THE BLOCK ITSELF
TESTS NEED NOT BE PROMISED. One lemma.

Why. A kind's law holds under a condition in front (`Piece.GoodIn`,
Johnson/Desc/Sound/GoodIn.lean). Where the seated block asks a clause of that condition itself, and
refuses without it, nobody in front need make or keep that clause: at a statement without it the
piece never says yes, and what is owed there holds of every transcript.

  `goodIn_or_refuses`: the law under `on`, and "under on₀ either `on` holds or the piece says yes at
    no transcript", give the law under on₀.

Limits. A rule; that a block refuses is the kind's own lemma on its text. A block that refuses all
passes it. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **What the block tests itself need not be promised.** -/
theorem goodIn_or_refuses (p : Piece C F S Cl W) (on₀ on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R')
    (h : ∀ a, on₀ a → on a ∨ ∀ τ, p.ior.red.out a τ = none) : p.GoodIn on₀ on' R R' := by
  intro a ha
  rcases h a ha with h1 | h1
  · exact g a h1
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    rw [h1 τ] at hb
    cases hb

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.goodIn_or_refuses
