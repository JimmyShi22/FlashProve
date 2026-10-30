-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontFreshProofs.lean: the proofs of the statements of Cb/Ld/LdFrontFresh.lean.

Main names (statements and hypotheses: Cb/Ld/LdFrontFresh.lean):
  `front_fresh`, `idle_fresh`: see their statements in Cb/Ld/LdFrontFresh.lean.
  `subQ_one`: one entry, read on the oracle messages that are kept.

Limits: what the head of Cb/Ld/LdFrontFresh.lean lists as not said is not said here either.
-/
import Cb.Ld.LdFrontFresh
import Cb.Ld.LdFrontProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

theorem front_fresh : Spec.front_fresh := by
  intro E Kc _ _ S E₀ Wp x y p Z c Rd Rr own Mk _ _ val hH hQ h
  exact ldReq_prog_fresh E Kc Z x.stage y.stage c p.prog (fun g => c.FreshFor g.kc g.Mk g.put)
    (fun _ hg => hg) _
    (front_carry E Kc S E₀ Wp x y p (fun g => c.FreshFor g.kc g.Mk g.put) Rd Rr own Mk val hH hQ h)

theorem idle_fresh : Spec.idle_fresh := by
  intro E Kc _ a Z c Kr kc Mk _ _ put h
  rw [append_one]
  exact (freshFor_snoc c a.idLink kc Mk put).2
    (Or.inr ⟨Kr, kc, put, h,
        blind_stepPure _ _ _ _ _ _ (fun x => some x) (ExtMap.id a.Ex) (fun q => q)
          _ _ kc kc Mk put put fun _ _ _ _ hk => ⟨rfl, hk⟩⟩)

theorem subQ_one : Spec.subQ_one := by
  intro E S kp _ a j
  funext n
  obtain ⟨⟨o, ho⟩, j'⟩ := n
  obtain ⟨a1, ha⟩ := a
  refine propext ⟨fun e => ?_, fun e => ?_⟩
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj e
    have h1' : o = a1 := h1
    subst h1'
    obtain rfl := eq_of_heq h2
    rfl
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj e
    have h1' : o = a1 := congrArg Subtype.val h1
    subst h1'
    obtain rfl := eq_of_heq h2
    rfl

end Cb
