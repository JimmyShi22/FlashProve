-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5TopPol.lean

The theorem of Lane5TopPub.lean for the head with the cost ledger, at the parameter file's own
policy.

"under_of_public" takes a policy as a free letter, with the library's condition on it as a
hypothesis. Here the policy is the one that stands in the head's shape, "Hd.polOf X.hS"
(HeadLinkLPort.lean), and the condition is a
theorem from the verifier's own call ("Hd.polCond_of_public", HeadL5Pol.lean): its bounds are tests
of the verifier. Why this policy: the verifier's four claims on the costs hold the shape's own three
numbers, so a statement on the head's sub-proof can be delivered at this policy alone.

Main theorems:
* "under_of_file": OrdsL at the file's own policy and r < e give "true under that policy".
* "ordsL_met_file": at that policy the bundle has a value.

Like the files that it joins, a translation, not a step towards a proof file. Not claimed: all that
Lane5TopPub.lean does not claim.
-/
import Johnson.Road.Lane5TopPub
import Johnson.Road.HeadL5Pol

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Verify (publicOf layerShape)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **The head with the cost ledger, at one parameter file and its own policy.** -/
theorem under_of_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) {i : Cm.Idx} {x : Instance ppref}
    {Z : ℕ → ℕ → ℕ → ℕ → ℤ} {ZA : ℕ → Zs} (hre : x.r < x.e)
    (O : OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
      (Hd.shapeA X) i.mat x Z ZA) :
    Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) (Hd.polOf X.hS) i
      x :=
  under_of_public h A hW (Hd.polCond_of_public h) hre O

/-- **At the file's own policy the ledger's bundle has a value.** -/
theorem ordsL_met_file (h : publicOf pol KL lay = .ok X) (A : Hd.PublicAt X.P)
    (hW : Model.fileWords KL = scalesKF.toArray) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
          (Hd.shapeA X) i.mat x Z ZA :=
  ordsL_met_public h A hW (Hd.polCond_of_public h)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.under_of_file
#print axioms OnBytes.Road.L5.ordsL_met_file
