-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldCodeGrpProofs.lean: the proofs of the statements of Cb/Ld/LdBldCodeGrp.lean: a member of
a group, reading modulo the short length, where a native position is read, finitely many
coordinates.

Main names (statements and hypotheses: Cb/Ld/LdBldCodeGrp.lean):
  `bld_mem_glC`, `bld_mem_glJ`: `GlC`, `GlJ` of a member of a group.
  `bld_mem_glC_at`, `bld_mem_glJ_at`: the same for a member read through a map.
  `bld_dn_even`, `bld_rep_eq`: reading modulo the short length; the native form as the short code so
    read.
  `bld_cov_rs` to `bld_cov_mem`: `CovOK` of the maps for the three forms and for a member.
  `bld_finNS_rs` to `bld_finNS_mem`: finitely many coordinates of a native symbol (`LdCode.FinNS`).

Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Limits: what the head of Cb/Ld/LdBldCodeGrp.lean lists as not said is not said here either.
-/
import Cb.Ld.LdBldCodeGrp
import Cb.Ld.LdBldCodeProofs
import Cb.Ld.LdBldCodeAtProofs

set_option autoImplicit false

namespace Cb.Gl.Bld
open Code Prob Blocks

theorem bld_mem_glC : Spec.bld_mem_glC := fun _ _ _ _ _ _ _ _ _ _ _ _ hC hZ =>
  .pair (.il _ hC) (.il _ hZ)

theorem bld_mem_glJ : Spec.bld_mem_glJ := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hZ =>
  .pair (.il _ hC) (.il _ hZ)

theorem bld_mem_glC_at :
    Spec.bld_mem_glC_at := fun P P' _ _ C Z Rm Rz _ _ _ _ d t pos' m hC hZ hm hp =>
  glC_atPos P P' _ d t pos' m (bld_mem_glC P C Z Rm Rz d t hC hZ) hm hp

theorem bld_mem_glJ_at :
    Spec.bld_mem_glJ_at := fun P P' _ _ C Z Rm Rz _ _ _ _ d t e bC bZ pos' m hC hZ hm hp =>
  bld_glJ_atPos P P' _ d t e _ pos' m (bld_mem_glJ P C Z Rm Rz d t e bC bZ hC hZ) hm hp

theorem bld_dn_even : Spec.bld_dn_even := fun a' a h => by
  have g := gl_rep_even Unit (fun _ => a') (fun _ => 0) (fun _ => 0) (fun _ => 0) a (fun _ => h) ()
  refine ⟨pow_pos (by norm_num) _, fun y => ?_⟩
  rw [← bld_pow_div h]
  exact g.2 y

theorem bld_rep_eq : Spec.bld_rep_eq := fun _ _ _ _ _ _ _ _ _ => rfl

theorem bld_cov_rs : Spec.bld_cov_rs := fun _ _ _ _ _ _ _ _ =>
  Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_singleton.2 rfl⟩

theorem bld_cov_cp : Spec.bld_cov_cp := fun _ _ _ _ _ _ _ _ _ =>
  Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_singleton.2 rfl⟩

theorem bld_cov_rep : Spec.bld_cov_rep := fun _ _ _ _ _ _ _ _ _ p =>
  Finset.mem_sigma.2 ⟨Finset.mem_univ _,
    Finset.mem_singleton.2 (Fin.ext (Nat.mod_eq_of_lt p.2.isLt).symm)⟩

theorem bld_cov_mem : Spec.bld_cov_mem := fun _ _ _ _ _ _ _ _ _ _ _ hC hZ p => match p with
  | .inl p => Finset.inl_mem_disjSum.2 (hC p)
  | .inr p => Finset.inr_mem_disjSum.2 (hZ p)

theorem bld_finNS_rs : Spec.bld_finNS_rs := fun _ _ _ _ R _ _ _ =>
  inferInstanceAs (Finite (R × Unit))
theorem bld_finNS_cp : Spec.bld_finNS_cp := fun _ _ _ _ _ R _ _ _ =>
  inferInstanceAs (Finite (R × Unit))
theorem bld_finNS_rep : Spec.bld_finNS_rep := fun _ _ _ _ _ _ R _ _ _ =>
  inferInstanceAs (Finite (R × Unit))

theorem bld_finNS_mem : Spec.bld_finNS_mem := fun _ C Z Rm Rz _ _ _ _ hC hZ p => match p with
  | .inl p => by
      haveI := hC p
      exact inferInstanceAs (Finite (Rm × C.NS p))
  | .inr p => by
      haveI := hZ p
      exact inferInstanceAs (Finite (Rz × Z.NS p))

end Cb.Gl.Bld
