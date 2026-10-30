-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwStateR.lean.
The equation of Cb/Pv/Lookup/Out/TwState.lean with no premise left.

Main names:
  `rootTg`: `RootTg A st kAt`, from `tK_eq`, `tgT0_eq` (Cb/Pv/Lookup/Out/TwRoot.lean).
  `state_eq`: for every assembly A, every kAt, st and typed transcript τ: `traceOf A (chnV (SV₀ E
    Ex) A st τ) = traceOfFlat (numsOf A st kAt) (flChn Ex A τ)`.
  `chn_trace`: the same of the chain's own reduction: at every statement and transcript it puts out
    a last state, and that state's trace is the flat trace.
Limits: as in Cb/Pv/Lookup/Out/TwState.lean, but for the premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwState
import Cb.Pv.Lookup.Out.TwRoot

set_option autoImplicit false

namespace Tw
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwV Tw3

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A : LkAsmH E)

theorem rootTg (st : A.St) (kAt : ℕ → A.J ⊕ E) : RootTg A st kAt :=
  ⟨fun x t ht => tK_eq A x t ht, fun x hx ϱ t ht hj => tgT0_eq A st kAt x hx ϱ t ht hj⟩

theorem state_eq (st : A.St) (kAt : ℕ → A.J ⊕ E) (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    traceOf A (chnV (SV₀ E Ex) A st τ) = traceOfFlat (numsOf A st kAt) (flChn Ex A τ) :=
  state_eq_of Ex A st kAt (rootTg A st kAt) τ

theorem chn_trace (kAt : ℕ → A.J ⊕ E) (a : A.St × Ex.Str) (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    ∃ o : A.XB, (A.chnK (SK₀ E Ex)).R.red.out a τ = some (o, a.2) ∧
      traceOf A o = traceOfFlat (numsOf A a.1 kAt) (flChn Ex A τ) :=
  ⟨_, chnK₀_out Ex A a τ, state_eq Ex A a.1 kAt τ⟩

end
end Tw
#print axioms Tw.rootTg
#print axioms Tw.state_eq
#print axioms Tw.chn_trace
