-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/FitOk.lean: a public test on the planner's record: the made plans fit the format's
words.

Why. A chain's plan is spelled into the chain's parameter bytes and read back from them. Reading
undoes spelling where the plan fits the format's words (`Fmt.Plan.fit`, Fmt/ParamsReadLaws.lean: six
numbers of the plan and eleven of each entry are below 2^64, and each entry's name is one that the
format can spell). By the head of OnBytes/Model/ReadBackMade.lean the planner has no test of that as
a whole. This file has the test, with code, on the planner's record alone, so that a description can
ask it through its field `fileOk`, beside the test on the plan's prices (Johnson/Desc/MadeOk.lean).

Definitions only.
  `keyFit c`: each plan of the key file's chains fits. `entryFit c`: the plan of the entry file's
  chain fits. `proofFit c`: each plan of the proof file's chains fits. `fitOk c`: all three.

Not to be taken for `OnBytes.Flat.keyFits`, `proofFits`
(OnBytes/Flat/PlanFitDefs.lean [not in this library]), which are
another test, on the plans as read back.

Limits. No theorem is here; what the test gives is in Johnson/G/PlansPriced.lean, and where it says
no and yes on small records in Johnson/Desc/Ok/NumberPrices/Teeth.lean. The test does not ask how
many plans
a file has: of a record with no plan for the key, `keyFit` says yes. Nothing here says that any
description asks the test, nor that it says yes of the plans of any public files.


-/
import OnBytes.Params.Configure
import Fmt.ParamsReadLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes.Params

/-- Each plan of the key file's chains fits the format's words. -/
def keyFit (c : Configured) : Bool := c.key.all fun P => P.plan.fit

/-- The plan of the entry file's chain fits the format's words. -/
def entryFit (c : Configured) : Bool := c.entry.plan.fit

/-- Each plan of the proof file's chains fits the format's words. -/
def proofFit (c : Configured) : Bool := c.proof.all fun P => P.plan.fit

/-- The plans of all seven chains fit the format's words. -/
def fitOk (c : Configured) : Bool := keyFit c && entryFit c && proofFit c

end VerifiableInference.Desc
