-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/LaterRests.lean: THE SENTENCE "A LEDGER IS OPEN AND IS LATER THAN U" PASSES
AN ACCEPTING CALL OF EACH RUN OF A SEGMENT THAT THE LIBRARY's `RunRests` NAMES
(Johnson/Desc/First/Link/Law/RunRel.lean: its eight fields on runs: front · back · free · merge ·
join · eq · ls · tests), at every ledger U that has its sizes: the library's five closure rules for
a property of a ledger (`LinkJoin.ForkRests`, Johnson/Desc/First/Link/Law/SizedRides.lean) at the
property "later than U" (`OnBytes.PscRun.Later U`). For the smallness test's share of the item
"totalB": that the ledger at which the run "K8.equations" is called inside the gatherer is later
than the one in front of the batching. Lemmas on the library's own text; none of its goals.

  **`later_rests`**   Sized U → ForkRests fun G => Later U G: each rule by the library's own law
                   that the step in question yields a later ledger, and transitivity
  **`rests_later`**   so: Sized U → RunRests fun e e₁ => HasFork (Later U) e → HasFork (Later U) e₁
                   (by the library's `rests_fork`)
Limits. THE RUNS THAT `RunRests` NAMES ALONE (the library's heads call them "the nine known runs";
how it counts nine is not held here): a lookup's runs are not among them: that they too yield a
later ledger is that kind's to say. That every run which a link's order names is one of these is the
sort's tie: not spent here. Nothing on the draw.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Sized hideRun_later paid_later)
open VerifiableInference.Desc.First.TailClaims.Law (eq_later)
open VerifiableInference.Desc.K9L (later_of_same coef_side)
open VerifiableInference.Desc.LinkJoin (ForkRests HasFork RunRests rests_fork)

/-- **The five rules at "later than U".** -/
theorem later_rests {U : Fork} (hU : Sized U) : ForkRests fun G => Later U G where
  later _ _ _ hl h := h.trans hl
  hide _ _ _ _ _ hr h := h.trans (hideRun_later (h.sized hU) hr)
  paid F i h := h.trans (paid_later F i)
  eq _ _ _ _ _ _ _ he h := h.trans (eq_later he)
  coef tl g F h := h.trans (later_of_same F _ (coef_side tl g F).1 (coef_side tl g F).2.1
    (coef_side tl g F).2.2.2.1 (coef_side tl g F).2.2.2.2.1 (coef_side tl g F).2.2.1)

/-- **So the sentence passes each run that `RunRests` names.** -/
theorem rests_later {U : Fork} (hU : Sized U) :
    RunRests fun e e₁ => HasFork (fun G => Later U G) e → HasFork (fun G => Later U G) e₁ :=
  rests_fork (later_rests hU)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.later_rests
#print axioms VerifiableInference.Desc.First.K8.Honest.rests_later
