-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Handle/Congr.lean: the run of an oracle algorithm under a rule for answering its queries
(Rom/Handle/Defs.lean) hangs on the rule only at the queries that the algorithm asks. General in the
family of oracles.

General lemmas. This file states no goal of the release.

  interp_congr     two rules that agree at every query which the algorithm asks (OComp.AsksIn,
                   Rom/SigmaExits.lean) give the same run.
  runDefer_congr   two tests for "deferred" that agree at every query which the algorithm asks give
                   the same run with a table and a log.

-/
import Rom.Handle.Laws
import Rom.AsksIn

set_option autoImplicit false

noncomputable section

namespace Rom
namespace OComp
variable {S : OSpec} {σ α : Type}

/-- Two rules that agree at every query which the algorithm asks give the same run. -/
theorem interp_congr {h h' : Handler S σ} :
    ∀ {c : OComp S α}, c.AsksIn (fun o q => ∀ s, h s o q = h' s o q) →
      ∀ s, c.interp h s = c.interp h' s
  | .pure _, _, _ => rfl
  | .sample _ _, hc, s => by
    simp only [interp_sample]
    exact congrArg _ (funext fun r => interp_congr (hc r) s)
  | .query _ _ _, hc, s => by
    simp only [interp_query]
    rw [hc.1 s]
    exact congrArg _ (funext fun p => interp_congr (hc.2 p.1) p.2)

/-- Two tests for "deferred" that agree at every query which the algorithm asks give the same run.
-/
theorem runDefer_congr {mk mk' : Mark S} {c : OComp S α}
    (hc : c.AsksIn fun o q => mk o q = mk' o q) (T : Table S) (lg : Trace S) :
    c.runDefer mk T lg = c.runDefer mk' T lg :=
  interp_congr (hc.mono fun o q e s => by simp only [Handler.defer, e]) (T, lg)

end OComp
end Rom

#print axioms Rom.OComp.interp_congr
#print axioms Rom.OComp.runDefer_congr
