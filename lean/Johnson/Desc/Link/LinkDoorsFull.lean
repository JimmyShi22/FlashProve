-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkDoorsFull.lean: THE COPY's FILE's LINK: THE FIVE DOORS THROUGH WHICH FOURTEEN
OLDER TEST FUNCTIONS ARE REACHED FROM THE SEATED DECISION (Desc.K15.linkDecisionAtParameterFile) ARE, AT THE WRITTEN
FULL-SIZE PARAMETERS frP AND THE WRITTEN LIST OF ROUNDS recordPlan, CLOSED VALUES; EACH IS WHAT AN
ACCEPTING RUN NEEDS, BY THE KERNEL, UNDER ITS OWN NAME. Each is constant at the seat AND true by the
kernel.
  okAt_full (LinkWrittenMade.lean:22; not new)   linkRoundsMatchPlan frP recordPlan = true
  front_full     (frontBlock frP).planOk = true: the codes' lengths and the public shape's
                 conditions (Codes.lengthsOk && linkOk)
  reads_full     the written IOP's declared rounds all pass readsFit (FileDescription.readsOk)
  entries_full   (entries frP).isSome = true: the trees of the link's one sending can be laid
  nums_full      (numsOf frP).isSome = true: the proximity test's place has its numbers
planOk_full (LinkWrittenMade.lean:28) has the first three as conjuncts, by unfolding; here each
stands alone, so that nobody has to unfold. NO PROVER's DATUM STANDS IN ANY OF THE FIVE: each is a
closed term.
OBJECT: the link's IOP as written at frP · USER: Johnson/Desc/K1/Law/SitsEntry.lean (entries_full).
Nothing on soundness.
-/
import Johnson.Desc.Link.LinkWrittenMade

set_option autoImplicit false

namespace Desc.K15
open VerifiableInference.Desc OnBytes.Params

set_option maxRecDepth 1000000 in
theorem front_full : (frontBlock frP).planOk = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem reads_full : (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).asFile.readsOk = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem entries_full : (entries frP).isSome = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem nums_full : (numsOf frP).isSome = true := by decide +kernel

end Desc.K15

#print axioms Desc.K15.okAt_full
#print axioms Desc.K15.planOk_full
#print axioms Desc.K15.front_full
#print axioms Desc.K15.reads_full
#print axioms Desc.K15.entries_full
#print axioms Desc.K15.nums_full
