-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldLinProofs.lean: the proofs of the statements of Cb/Ld/LdBldLin.lean (what the linear test
on the encoded index and the link need beside the configuration and the claims, for variable data).
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
What is said and what is not: the head of that file.

Main names (statements and hypotheses: Cb/Ld/LdBldLin.lean):
  `bld_invS`: `invS f`, the partial inverse of a map f, at an injective f.
  `bldLn_places`, `bldLn_fair`: the linear test's `Places`; fair seeds of its three families.
  `bldLk_reads`, `bldLk_fair`, `bldLk_pl`: the link's layout and (u₀, u₁); fair seeds; places at
    different corners.
-/
import Cb.Ld.LdBldLin
import Cb.Ld.LdBldMsgProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem bld_invS : Spec.bld_invS := by
  intro O V D f hf v
  have h : ∃ w, f w = ⟨(f v).1, (f v).2⟩ := ⟨v, rfl⟩
  unfold invS
  rw [dif_pos h]
  exact congrArg some (hf h.choose_spec)

theorem bldLn_places : Spec.bldLn_places := fun _ _ _ _ _ _ _ _ _ L _ _ _ hI =>
  ⟨fun _ => rfl,
    fun c =>
      bld_invS L.FW.O _ L.FW.lay.Dt (fun c => ⟨L.iW, L.aW c⟩) (sigma_mk_injective.comp hI.w) c,
    fun _ => rfl,
    fun k =>
      bld_invS L.FU.O _ L.FU.lay.Dt (fun k => ⟨L.iU, L.aU k⟩) (sigma_mk_injective.comp hI.u) k,
    fun _ => rfl,
    fun y =>
      bld_invS L.FO.O _ L.FO.lay.Dt (fun y => ⟨L.iO, L.aO y⟩) (sigma_mk_injective.comp hI.o) y⟩

theorem bldLn_fair : Spec.bldLn_fair := fun E _ _ _ _ _ _ _ _ L =>
  ⟨(bld_fair E L.FW).1, (bld_fair E L.FU).1, (bld_fair E L.FO).1⟩

theorem bldLk_reads : Spec.bldLk_reads := by
  intro F E _ _ _ _ _ Cf L hI c
  refine ⟨(L.uvAt c).1, (L.uvAt c).2, bld_invS L.F.O _ L.F.lay.Dt L.uvAt hI c, fun m => ?_⟩
  cases c <;> rfl

theorem bldLk_fair : Spec.bldLk_fair := fun E _ _ _ _ L => (bld_fair E L.F).1

theorem bldLk_pl : Spec.bldLk_pl := fun _ _ _ _ _ _ _ Cf L h => bld_binC Cf.Lay L.l h

end Cb
