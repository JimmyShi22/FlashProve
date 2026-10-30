-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseAltProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseAlt.lean (a closing
in which fronts and whole tests alternate). By composition.
Named tools: `extId_src` (the sources of a set of positions under the identity are the set),
`LdStage.idLink_sideC` (the link that does nothing has the budgets' half from q to q). Nothing is
defined here.
-/
import Cb.Ld.LdLinCloseAlt
import Cb.Ld.LdLinCloseDemandVProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the sources under the identity are the set itself -/
theorem extId_src (Ex : ExtSpec) (inst : DecidableEq Ex.Pos) (U : Finset Ex.Pos) :
    @Finset.biUnion _ _ inst U (ExtMap.id Ex).src = U := by
  ext q
  constructor
  · intro h
    obtain ⟨u, hu, hq⟩ := (ldDemand_mem_biUnion _).1 h
    obtain rfl := Finset.mem_singleton.1 hq
    exact hu
  · intro h
    exact (ldDemand_mem_biUnion _).2 ⟨q, h, Finset.mem_singleton_self _⟩

theorem LdStage.idLink_sideC
    {E : Type} [Field E] (a : LdStage E Unit) (q : Finset a.J.E.Pos → Prop) : a.idLink.SideC q q :=
  sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨fun _ _ => rfl, fun _ _ => rfl, fun ρ U hU => ⟨trivial, by
    have e : a.idLink.R.need ρ U = U :=
      (need_pure (fun x => some x) (ExtMap.id a.Ex) ρ U).trans (extId_src a.Ex _ U)
    rw [e]
    exact hU⟩⟩

theorem ldAlt_of_ok : Spec.ldAlt_of_ok := fun E _ S E₀ Wp Q Z c₀ h =>
  ldChain_behind E S E₀ Wp Q Z c₀ h

theorem ldAlt_cons : Spec.ldAlt_cons := by
  intro E _ _ S E₀ Wp D Q d d' Z c₀ hD hQ
  obtain ⟨h1, h2⟩ :=
    ldChain_link E S D Q.St Wp E₀ Q.base d d' (LdTc.cons D Q d d').q Q.q hD fun U hU => ⟨U, hU, rfl⟩
  refine ⟨ldChain_okFrom_append
      c₀ (Chain.one (D.link Q.base d d')) Q.c ((Chain.okFrom_one c₀ _).2 (Or.inl h1)) ?_,
    sidesCT_append Unit _ _ _ (Chain.one (D.link Q.base d d')) Q.c _ Q.q
      ((Chain.sidesC_one _ _ _).2 h2) hQ.2⟩
  rw [Chain.append_one]
  exact hQ.1

theorem ldAlt_front : Spec.ldAlt_front := by
  intro E _ _ S E₀ Wp x Q p Z c₀ Rd Rr h₀ hp hs hz hQ
  have hid : (Chain.one x.stage.idLink).OkFrom c₀ :=
    (Chain.okFrom_one c₀ _).2 (Or.inl x.stage.idLink_goodT)
  have h1 : (LdTc.frontC p).OkFrom c₀ :=
    front_okFrom E Unit S E₀ Wp x _ p Z _ c₀ (.one x.stage.idLink) Rd Rr h₀ hid hp hz
  have s1 : (LdTc.frontC p).SidesC Q.q Q.q :=
    front_sides E Unit S E₀ Wp x _ p _ (.one x.stage.idLink) Q.q Q.q
      ((Chain.sidesC_one _ _ _).2 (x.stage.idLink_sideC Q.q)) hp hs
  exact ⟨ldChain_okFrom_append c₀ (LdTc.frontC p) Q.c h1 hQ.1,
    sidesCT_append Unit _ _ _ (LdTc.frontC p) Q.c Q.q Q.q s1 hQ.2⟩

theorem ldAlt_demand : Spec.ldAlt_demand := fun _ _ _ _ _ _ _ _ _ => rfl

end Cb
