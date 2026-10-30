-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/PadKeyLaw.lean: the test on the padding key of an attention link's lookup on the
calls (padKeyAtt, Johnson/Desc/First/Look/Laid.lean) accepts at every attention plan of a public
part that the verifier's maker returns. A joining of laws of the library; nothing is evaluated.

The test asks of each call whose table is not of the kind KFD that row t0 of the call's table has
the value 0. Two of these calls have tables of 65,536 rows. The library's law padKeyOk_ofPlan
(Johnson/Desc/First/Att/Row/K5PadKeyOk.lean) shows the same test, in the letters of the attention
sub-proof's own description, from the maker's text, without building a table.

  `padKeyAtt_eq`: the two tests are one: call by call, by unfolding.
  **`padKeyAtt_public`**: wherever publicOf returns X, at each plan a of X.A: padKeyAtt a.S = true.
  `padKeyAtt_public_o`: the same where the maker's text with the hash as an argument returns, at
    the second hash function.

Limits. Nothing on the padding key of a call of the kind KFD. Nothing on soundness, completeness or
hiding.

-/
import Johnson.Desc.First.Att.Row.K5PadKeyOk
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (padKeyAtt)
open VerifiableInference.Desc.First.Att.P (geoOf padKeyOk)

/-- The two tests are one. -/
theorem padKeyAtt_eq (S : Attention.Shape) : padKeyAtt S = padKeyOk (geoOf S) := by
  rw [H2K5.Row.padKeyOk_calls]
  unfold padKeyAtt
  congr 1
  funext c
  unfold H2K5.Row.padOkA
  congr 1
  show (c.kind == .kfd) = (VerifiableInference.Desc.First.Att.P.tabOf c.kind == .kfd)
  cases c.kind <;> rfl

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **At every attention plan of a public part that the maker returns.** -/
theorem padKeyAtt_public (h : Verify.publicOf pol KL lay = .ok X) (g : Nat) (a : Attention.Plan)
    (ha : X.A[g]? = some a) : padKeyAtt a.S = true :=
  (padKeyAtt_eq a.S).trans (H2K5.Row.padKeyOk_ofPlan (K5Law.public_ofPlan h g a ha))

theorem padKeyAtt_public_o
    (h : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol KL lay = .ok X) (g : Nat)
    (a : Attention.Plan) (ha : X.A[g]? = some a) : padKeyAtt a.S = true :=
  padKeyAtt_public ((VerifiableInference.PlanWritten.publicOfO_older _ _ _).symm.trans h) g a ha

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.padKeyAtt_eq
#print axioms Johnson.AtFull.K3X.padKeyAtt_public
#print axioms Johnson.AtFull.K3X.padKeyAtt_public_o
