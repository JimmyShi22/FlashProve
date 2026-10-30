-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupAttentionClauseAtLookR.lean: the kind "lookup" (K3): the
hypothesis `attentionClauseHoldsOfEveryHearing` of `lookupFormRidersAndKeepsBehindTheCalls`
(Honest/K3/Term/LookupBehindAndRidesPast.lean) holds at the value of the letter R that the kind K5
reads.

What is shown.
  `attentionClauseAtLookR`: a definition: R g o := at every plan a that the public structure holds at
    the attention group g, `H2K5.Honest.lookR a o` (Johnson/Desc/K5/Honest/Law/LookR.lean).
  `attentionClauseAtLookRHoldsOfEveryHearing`: at that R the hypothesis holds. By
    `ProofFile.Honest.K5.lookR_of_hearVia` (Honest/K5/Law/LookRHeard.lean), called.

Hypotheses that remain. `h`: the library's hypothesis `P5J.AtMgA` at the hash function `secondHashFunction`.

Limits. Nothing here sets the thread's letter R to this value: that is for the thread's authors.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LookRHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K3.Law (hearVia)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The sentence on what the lookup on the calls of attention group g returned, as the kind K5 reads
it: at every plan that the public structure holds at g. -/
def attentionClauseAtLookR (Zp : ProofFile.Pub) (g : Nat) (o : Option OnBytes.Model.Forest.Heard) :
    Prop :=
  ∀ a, (P5J.At.X Zp).A[g]? = some a → H2K5.Honest.lookR a o

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At that sentence the hypothesis on the letter R holds. -/
theorem attentionClauseAtLookRHoldsOfEveryHearing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ g, g < 12 → ∀ a, (P5J.At.X Zp).A[g]? = some a →
      ∀ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs →
      ∀ F rs Hd G₁, hearVia p F rs = some (Hd, G₁) → attentionClauseAtLookR Zp g (some Hd) := by
  intro g hg a ha p hp F rs Hd G₁ hv a' ha'
  obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
  exact ProofFile.Honest.K5.lookR_of_hearVia h hg ha p hp F rs Hd G₁ hv

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.attentionClauseAtLookRHoldsOfEveryHearing
