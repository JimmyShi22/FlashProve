-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean: a public part that has the steps of the public
part's text at files in the scope of the goals is as at the full size; so is what `publicOfO o`
returns there, at every o.

`PublicSteps pol KL X` (Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean) holds every step of the text
of Model.Verify.publicOf that takes no hash, in X's own fields; both `publicOf` and `publicOfO o`
(Johnson/Desc/Ok/PlanWritten/PublicAt.lean: the same text with the second hash function as an
argument o) pay it. StageSizesAtScope.lean and LastAtScope.lean size a proof's four proximity tests
from `PubFull X` and configure's yes. Here `PubFull X` is drawn from two fields of `PublicSteps`:
`layout` and `wsLay`.
Main names:
  `pubFull_of_steps`: THE STATEMENT: in scope, `PublicSteps Z.pol Z.KL X` gives `PubFull X`.
  `publicO_at_scope`: so what `publicOfO o` returns at files in scope has it, at every o.
  `atFull_of_publicO`: so, with configure's yes, `AtFull made`.
Limits: one direction: from a run that returns; at no o and no file is `publicOfO o` shown to
return. Nothing on the tests of `publicOfO o` that read o. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Params VerifiableInference.PlanWritten

/-- **In scope, a public part with the steps of the public part's text is as at the full size.**
Two fields are spent, by name: the scan with the layers' layout, and the layout of the committed
matrix. -/
theorem pubFull_of_steps {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {X : Public}
    (C : PublicSteps Z.pol Z.KL X) : PubFull X :=
  pubFull_of_layout hZ C.layout C.wsLay

/-- **What `publicOfO o` returns at files in the goals' scope is a public part as at the full
size**, at every o. -/
theorem publicO_at_scope {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {lay : Option ByteArray} {X : Public}
    (hX : publicOfO o Z.pol Z.KL lay = .ok X) : PubFull X :=
  pubFull_of_steps hZ (publicSteps_of_O hX)

/-- So, with configure's yes on its lines and on shapes whose sub-proofs are subproofsWith's. -/
theorem atFull_of_publicO {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) {lay : Option ByteArray} {X : Public}
    (hX : publicOfO o Z.pol Z.KL lay = .ok X) {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure X.P.frame shapes cfg bits = .ok made) {rl : List ReqLink}
    (he : shapes.sub = subproofsWith X rl) : AtFull made :=
  atFull_of_public (publicO_at_scope hZ hX) hc he

end H2K.Sizes

#print axioms H2K.Sizes.pubFull_of_steps
#print axioms H2K.Sizes.publicO_at_scope
#print axioms H2K.Sizes.atFull_of_publicO
