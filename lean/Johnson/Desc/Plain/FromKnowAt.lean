-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/FromKnowAt.lean: THE DOOR FROM THE LIBRARY's TYPED CHAINS INTO THE PLAIN FORM AT
ONE WORLD.

The library's typed chains (the layers' own rounds, the attention's, the head's …) have their
knowledge soundness as `TWhole.KnowAt` (Cb/G6/Cut.lean): FOR EACH FIXED TUPLE OF MESSAGES m,
round-by-round knowledge soundness: m STANDS OUTSIDE THE GAME; a witness is a pair (m, wp). The rule
of composition's coin has "for every world w" INSIDE the game (`KeepsW`,
Johnson/Desc/Plain/World.lean), and the first does not give the second for nothing (`not_inside`,
Johnson/Desc/Plain/Pinned.lean). `leadsAt_of_knowAt`: `KnowAt` at the extractor "the rest of the
witness as it is" gives, for each m, the plain law "the condition behind holds; for every world
whose messages are m: behind gives in front", at the same errors. Nothing is asked.
`keepsW_of_knowAt`: WITH A PIN (the relation behind fixes the world's messages as a function mOf of
the statement in front: what its oracles decode to): `KeepsW`, at the same errors.
Nearest kin: `keepsW_of_pinned` (Pinned.lean), which it calls; in the library: `KnowAt`'s own joins
(Cb/G6/Join.lean) stay at a fixed m.
Limits: those of Leads.lean and of `KnowAt`. The pin is a premise. For an extractor that lays a part
of the witness: not here.

-/
import Johnson.Desc.Plain.Pinned
import Cb.G6.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Plain
open Iop TWhole

variable {K M Xi Xo Wp : Type} {Ei Eo : ExtSpec}

/-- **From `KnowAt` to the plain law, the messages outside the game.** -/
theorem leadsAt_of_knowAt {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wp)}
    {B : IOR.Rels K Xo Eo (M × Wp)} {ε : Err R.shape}
    (h : KnowAt R A B (fun _ _ _ wp => wp) ε) (m : M) :
    R.red.Leads A.on (fun a b => B.on b ∧ ∀ w : M × Wp, w.1 = m → B.relR b w → A.relR a w) ε :=
  fun a ha => Doomed.mono _ _ (fun τ hτ b hb =>
    ⟨h.onOut a τ b ha hb, fun w hw hr => by
      obtain ⟨m', wp⟩ := w
      have e : m' = m := hw
      subst e
      exact hτ b wp hb hr⟩) (h.know m a ha)

/-- **From `KnowAt` and a pin to the plain law at one world.** -/
theorem keepsW_of_knowAt {R : IOR Xi Ei Xo Eo} {A : IOR.Rels K Xi Ei (M × Wp)}
    {B : IOR.Rels K Xo Eo (M × Wp)} {ε : Err R.shape}
    (h : KnowAt R A B (fun _ _ _ wp => wp) ε) (mOf : Xi × Ei.Str → M)
    (pin : ∀ a τ b (w : M × Wp), A.on a → R.red.out a τ = some b → B.relR b w → w.1 = mOf a) :
    R.red.KeepsW A.on B.on A.relR B.relR ε :=
  Reduction.keepsW_of_pinned Prod.fst mOf (leadsAt_of_knowAt h) pin

end VerifiableInference.Desc.Plain

#print axioms VerifiableInference.Desc.Plain.leadsAt_of_knowAt
#print axioms VerifiableInference.Desc.Plain.keepsW_of_knowAt
