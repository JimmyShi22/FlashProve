-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Mid.lean: the merge's proved block in the plain form, with no letter left but the record: for each fixed tuple of entries, outside the rounds' bad values, true output
claims give true claims on the weights.

Cb/Pv/Lay/Weights.lean proves the block knowledge sound for each fixed tuple of messages (WeightsL.know), at letters: a riding joint R0, a type of messages M with a reading msg, a further witness
Wp. Here they are filled with nothing: M := the entries themselves, msg := the identity, Wp := Unit, a riding joint that asks nothing. What is left:
    G_mid   for every statement a and every m: the prover has lost (Iop.Doomed), at the block's own errors, towards: whenever the block puts out o, and the record's side condition Rd, the row on the
            hiding coefficients (Rw1) and the row on the end value (EV) hold of o and m, then every claim holds of a and m
The entries m are fixed BEFORE the game: the bad values of a round may hang on them.
SPENT OF THE LIBRARY: Cb.Pv.Lay.WeightsL.know (Cb/Pv/Lay/Weights.lean) · Iop.Doomed.mono (Iop/Rbr.lean).
Limits: nothing on who fixes m, or on whether m is committed before the first draw. The errors are counts: Rounds.lean holds them against the planner's prices. That a written block's yes is this
block's output on the transcript read is not said here. On hiding nothing.

-/
import Cb.Pv.Lay.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K11Caller
open Iop IOR Cb Cb.Pv.Lay TWhole

variable {E : Type} [Field E] [Fintype E]

/-- The riding joint that asks nothing. -/
def noRider (G : WeightsL E) (Ex : ExtSpec) : Rels Unit G.St Ex ((G.J → E) × Unit) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩

/-- **The merge's block in the plain form.** -/
theorem G_mid (G : WeightsL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (m : G.J → E) (a : G.St × Ex.Str) :
    Doomed (G.blk V).shape (G.eps (Kc := Unit) V) (fun τ => ∀ o, (G.blk V).red.out a τ = some o →
      G.Rd o.1.st.1 m → G.L.Rw1.Says o.1 m → G.L.EV o.1 m → ∀ c, G.Cl a.1 m c) := by
  have h := G.know (noRider G Ex) id V m a trivial
  refine Doomed.mono _ _ (fun τ hτ o ho hR hU hE c => ?_) h
  exact (hτ o () ho ⟨⟨trivial, hR⟩, hU, hE⟩).2 c

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.G_mid
