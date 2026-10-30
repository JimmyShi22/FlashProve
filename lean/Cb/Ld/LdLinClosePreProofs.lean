-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePreProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePre.lean (a step
without rounds from the rows that the test for linear constraints leaves to a joint over one
signature).
Main names (statements and hypotheses: Cb/Ld/LdLinClosePre.lean):
  `ldLinPre_rows`: the rows read off the messages, and the rows of Cb/Ld/LdLin.lean.
  `ldLinPre_step`: the re-bracketing as a step without rounds.
  `ldLinPre_step_cf`: the same step between the joints whose condition may fail (`Rels.cf`).
Named tools: `LdLinC.toE_isLocal` (each symbol of the re-bracketed oracles depends only on its one
source position: `ExtMap.IsLocal`, Ior/Frame.lean). Nothing is defined here that a statement reads.
-/
import Cb.Ld.LdLinClosePre
import Cb.Ld.LdBatPeelProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E ι κ J Y : Type} [Field E]

theorem LdLinC.toE_isLocal (C : LdLinC E ι κ J Y) : C.toE.IsLocal := by
  intro y y' q h
  rcases q with p | ⟨((a | a) | a) | a, x⟩
  · have := h (.inl (.inl (.inl (.inl p)))) (Finset.mem_singleton_self _)
    exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj this))))
  · have := h (.inl (.inl (.inl (.inr ⟨a, x⟩)))) (Finset.mem_singleton_self _)
    have h2 : (⟨a, (C.Sa.om a).C.T ((C.Sa.om a).upW (y.1.1.1.2 a)) x⟩ : C.Sa.ext.Sym) =
        ⟨a, (C.Sa.om a).C.T ((C.Sa.om a).upW (y'.1.1.1.2 a)) x⟩ :=
      Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj this)))
    have h3 := eq_of_heq (Sigma.mk.inj h2).2
    exact congrArg (fun s => (Sum.inr ⟨.inl (.inl (.inl a)), s⟩ : (C.E₀.prod C.S.ext).Sym)) h3
  · have := h (.inl (.inl (.inr ⟨a, x⟩))) (Finset.mem_singleton_self _)
    have h2 : (⟨a, (C.NW.om a).C.T ((C.NW.om a).upW (y.1.1.2 a)) x⟩ : C.NW.ext.Sym) =
        ⟨a, (C.NW.om a).C.T ((C.NW.om a).upW (y'.1.1.2 a)) x⟩ :=
      Sum.inr.inj (Sum.inl.inj (Sum.inl.inj this))
    have h3 := eq_of_heq (Sigma.mk.inj h2).2
    exact congrArg (fun s => (Sum.inr ⟨.inl (.inl (.inr a)), s⟩ : (C.E₀.prod C.S.ext).Sym)) h3
  · have := h (.inl (.inr ⟨a, x⟩)) (Finset.mem_singleton_self _)
    have h2 : (⟨a, (C.NU.om a).C.T ((C.NU.om a).upW (y.1.2 a)) x⟩ : C.NU.ext.Sym) =
        ⟨a, (C.NU.om a).C.T ((C.NU.om a).upW (y'.1.2 a)) x⟩ :=
      Sum.inr.inj (Sum.inl.inj this)
    have h3 := eq_of_heq (Sigma.mk.inj h2).2
    exact congrArg (fun s => (Sum.inr ⟨.inl (.inr a), s⟩ : (C.E₀.prod C.S.ext).Sym)) h3
  · have := h (.inr ⟨a, x⟩) (Finset.mem_singleton_self _)
    have h2 : (⟨a, (C.NO.om a).C.T ((C.NO.om a).upW (y.2 a)) x⟩ : C.NO.ext.Sym) =
        ⟨a, (C.NO.om a).C.T ((C.NO.om a).upW (y'.2 a)) x⟩ := Sum.inr.inj this
    have h3 := eq_of_heq (Sigma.mk.inj h2).2
    exact congrArg (fun s => (Sum.inr ⟨.inr a, s⟩ : (C.E₀.prod C.S.ext).Sym)) h3

end

section
variable (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] in
theorem ldLinPre_rows : Spec.ldLinPre_rows E ι κ J Y := fun _ _ _ => Iff.rfl

omit [Fintype E] [Fintype ι] in
theorem ldLinPre_step : Spec.ldLinPre_step E ι κ J Y := by
  intro C Stq Bq fq hS
  refine ⟨C.toE_isLocal, ?_, ?_, fun _ _ => rfl, ?_⟩
  · rintro x y w ⟨hEO, hAO, ⟨hEU, hAU⟩, ⟨hEW, hAW⟩, hRec, ⟨hEa, hAa, hAb⟩, hCl, hw, hu, hcol, ho⟩
    refine ⟨rfl, ?_, ?_, hS.fwd _ _ _ _ ?_ hAb⟩
    · rintro (((a | a) | a) | a)
      · exact hEa a
      · exact hEW a
      · exact hEU a
      · exact hEO a
    · rintro (((a | a) | a) | a)
      · exact hAa a
      · exact hAW a
      · exact hAU a
      · exact hAO a
    · obtain ⟨c1, _, c3, c4, c5⟩ :=
        ldLin_complete C.D w.2.2.2.1 x.1.1.1.1.1.1.2 (C.g x.1.1.1.1.1.1.1.1)
          (C.ψ x.1.1.1.1.1.1.1.1) (C.rest x.1.1.1.1.1.1.1.1 (C.Sa.msgs w.2.2.2.2.1))
          (C.τ x.1.1.1.1.1.1.1.1) x.1.1.1.1.2 C.t x.1.1.2.1 x.2 hRec hCl
      have hu' : C.uM (C.S.msgs (C.toW w).1) = foldAll x.1.1.1.1.2.1 w.2.2.2.1 := hu
      have hw' : C.wM (C.S.msgs (C.toW w).1) =
          C.D.wOf (C.D.X.view w.2.2.2.1) (C.g x.1.1.1.1.1.1.1.1) := hw
      have ho' : C.oM (C.S.msgs (C.toW w).1) = C.D.omOf (C.D.X.view w.2.2.2.1) x.1.1.1.1.2 := ho
      have hR : C.RowsM (C.toSt x) (C.S.msgs (C.toW w).1) := by
        unfold LdLinC.RowsM
        rw [hu', hw', ho']
        exact ⟨c1, hu' ▸ hcol, c3, c4, c5⟩
      exact hR
  · rintro x y x' ⟨hcO, ⟨hca, hab⟩, hcW, hcU⟩ hx
    rw [← Option.some.inj hx]
    refine ⟨?_, hS.on _ _ hab⟩
    rintro (((a | a) | a) | a)
    · exact hca a
    · exact hcW a
    · exact hcU a
    · exact hcO a
  · rintro x y x' w' ⟨_, ⟨_, hab⟩, _, _⟩ hx hB
    rw [← Option.some.inj hx] at hB
    obtain ⟨hdec, hq⟩ := hB
    obtain ⟨hrows, hr⟩ := hS.bwd _ _ _ _ hab hq
    exact ⟨fun i => hdec (.inr i),
      fun i => hdec (.inl (.inr i)),
      fun i => hdec (.inl (.inl (.inr i))),
      ⟨fun i => hdec (.inl (.inl (.inl i))), hr⟩,
      hrows⟩

omit [Fintype E] [Fintype ι] in
theorem ldLinPre_step_cf : Spec.ldLinPre_step_cf E ι κ J Y := fun C Stq Bq fq hS =>
  ldPeel_cf _ _ _ _ _ _ _ _ _ _ _ _ _ (ldLinPre_step E ι κ J Y C Stq Bq fq hS)

end
end Cb
