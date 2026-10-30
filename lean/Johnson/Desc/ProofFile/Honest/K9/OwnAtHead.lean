-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OwnAtHead.lean: ONE EQUATION ON PUBLIC DATA, FOR WHOEVER JOINS A LAW AT THE HEAD's OWN
DATA TO OUR ASSEMBLIES FOR THE ITEM "totalB". No prover is in this file, and no goal is stated.
  `own_at_head`   under the head: `h.𝔇.N.group l = (P5J.At.N Zp cF).group l`, at every l: by unfolding. Our assemblies
      pin their letter own to the right side (their binder hown); the library's laws at the head's data speak of the
      left.
WHAT IS NOT CLAIMED. Anything else. Called by Honest/K9/TotalWorthTwo.lean alone. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The groups of the head's own data are the closed letter's**: public data on both sides. -/
theorem own_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) :
    h.𝔇.N.group l = (P5J.At.N Zp cF).group l := rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.own_at_head
