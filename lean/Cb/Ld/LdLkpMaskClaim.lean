-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskClaim.lean: for every assembled lookup A with its places in order (`A.PlacesOK Dt`,
Cb/Ld/LdLkpMaskPlaces2.lean): the claim with which the lookup is started (`A.lk.inP A.ValidMu`;
`ValidMu`: Cb/Ld/LdLkpAsm2Pull.lean) reads the data places (`Dt`) alone, and is stable under the
swap of all masks (`A.swAll`).
The lookup's input relation is read here as a predicate on the entries of the oracle messages; the
two theorems say on which entries it does not depend.

Two theorems (`ldLkpMask_claim_reads`, `ldLkpMask_claim_stab`). Generic: any finite field, any
`A : LkAsm2 E` (Cb/Ld/LdLkpAsm2.lean).

Used: `ldLkpMask_claim_stab` gives the premise `MjStab C A.swAll` of `Spec.ldLkpMaskAsm2_link`
(Cb/Ld/LdLkpMaskAsm2.lean) at C := `A.lk.inP A.ValidMu`.
Why a file of its own: generic files use them, and so does the guard Cb/Ld/LdLkpToyMask.lean: here
they import no toy.
Limits: this file does not say that `A.PlacesOK` can be met (a guard: Cb/Ld/LdLkpToyMask.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdLkpMaskLift2
import Cb.Ld.LdLkpMaskPlaces2Proofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section General
variable (E : Type) [Field E] [Fintype E]

/-- Under `h`: the lookup's exact claim (`A.lk.inP A.ValidMu`) reads the data only. -/
theorem ldLkpMask_claim_reads (A : LkAsm2 E) (Dt : A.J → Prop) (h : A.PlacesOK Dt) (st : A.St)
    (k k' : A.J → E) (hk : ∀ j, Dt j → k j = k' j) (hc : A.lk.inP A.ValidMu st k) :
    A.lk.inP A.ValidMu st k' := by
  have ek := h.keys st k k' hk
  have eb : A.H.bit k = A.H.bit k' := funext fun u => funext fun j => hk _ (h.bits u j)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨⟨?_, h2⟩, ?_⟩
  · show InTable (A.v' + 1) A.d (A.key st k') (A.tab st)
    rw [← ek]
    exact h1
  · show Valid (A.v' + 1) A.d A.w (A.n + 1) (A.key st k') (A.tab st) (A.H.bit k')
    rw [← ek, ← eb]
    exact h3

/-- Under `h`: the lookup's exact claim (`A.lk.inP A.ValidMu`) reads no own mask (`MjStab`,
Cb/Ld/LdLkpMaskSp.lean). -/
theorem ldLkpMask_claim_stab (A : LkAsm2 E) (Dt : A.J → Prop) (h : A.PlacesOK Dt) :
    MjStab (A.lk.inP A.ValidMu) A.swAll := fun st k k' hk hc =>
  ldLkpMask_claim_reads E A Dt h st k k' (fun j hj => hk j fun hw => by
    obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E A j).1 hw
    exact h.out i hj) hc

end General

end Cb
