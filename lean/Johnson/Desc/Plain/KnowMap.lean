-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/KnowMap.lean: FROM THE LIBRARY's `Know` TO THE PLAIN FORM WITH THE EXTRACTOR
  NAMED: one theorem. `Know.toLeadsMap`: a reduction that is knowledge sound at an extractor which,
  at a yes, is a function E of the two statements and the witness, has the plain form in the one
  wording for every row's debt: Q a b := ∀ w, RB b w → RA a (E a b w): at the same errors. Beside
  `Know.toLeads` (Leads.lean), which keeps only "there is a witness".
It lies in a file of its own so that Leads.lean does not turn.
Near kin: `ride_leads` (Johnson/Top/H/SwitchLeads.lean):
this theorem at one kind.
Limits. A rule. It would stay proved if the protocol were otherwise.

-/
import Johnson.Desc.Plain.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
namespace Reduction
variable {A B WA WB : Type} {K : Reduction A B} {on : A → Prop} {ε : Err K.shape}

theorem Know.toLeadsMap {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    (h : K.Know on RA RB ext ε) (E : A → B → WB → WA)
    (hE : ∀ a τ b w, K.out a τ = some b → ext a τ w = E a b w) :
    K.Leads on (fun a b => ∀ w, RB b w → RA a (E a b w)) ε := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb w hw => hE a τ b w hb ▸ hτ b w hb hw) (h a ha)

end Reduction
end Iop

#print axioms Iop.Reduction.Know.toLeadsMap
