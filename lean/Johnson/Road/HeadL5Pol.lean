-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5Pol.lean: the acceptance policy of the parameter file meets the library's
condition on a policy.

The library's theorems on a request under a policy ask that the policy's three words are bounded
(Policy.PolCond: C and theta below 2^40, cap below 2^16). The verifier has the three words in the
shape of the output head: polOf (Johnson/Road/HeadLinkLPort.lean) reads them off as the library's
record. This file says that the policy in what publicOf returns (OnBytes/Model/VerifyPublic.lean)
meets the condition. No number of a parameter file is asked: the bounds are tests of the verifier.

Which tests. cap below 2^16 and theta at most C: the head's layout. C below 2^32: the strict scan of
the parameter file refuses a value line of 2^32 or more (Johnson/Road/HeadScan.lean).

Main theorem: polCond_of_public.

What is not claimed. That a statement on the head's sub-proof stands at this policy: the theorems on
the verifier's four claims on the costs ask it (Johnson/Road/HeadPolicyForms.lean). The program does
not import this file.
-/
import Johnson.Road.HeadScan
import Johnson.Road.HeadLinkLPort
import Policy.Rel.True

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

/-- **The parameter file's own policy meets the library's condition**, in what the public part of a
stage returns. -/
theorem polCond_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) : Policy.PolCond (polOf X.hS) :=
  polOK_of_public h

#print axioms polCond_of_public

end OnBytes.Road.Hd
