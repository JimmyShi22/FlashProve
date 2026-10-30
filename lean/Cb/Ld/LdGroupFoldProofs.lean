-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupFoldProofs.lean: the proofs of the statements of Cb/Ld/LdGroupFold.lean.

An assembly; the one computation is that the weights of the corners of a cube sum to 1.

Main names (statements and hypotheses: Cb/Ld/LdGroupFold.lean):
  `ldGroup_fold`: under the hypotheses of `Spec.ldGroup_fold`, the bridge, the arrangement and the
    fold on a group, beside the carried part, are a piece of a chain.
  `ldGroup_shape_laws`: the laws of the arrangement.
  `ldGroup_list`: the list of the complex as sent, from that of the full interleaving.
  `ldGroup_block`: the block as a piece, of h + g + 1 rounds.
  `ldGroup_fold_kept`, `ldGroup_fold_kept_near`: the kept rows after the fold: words, messages,
    randomness; for messages and randomness the same close to an arranged word.

Limits: what the head of Cb/Ld/LdGroupFold.lean lists as not said is not said here either.
-/
import Cb.Ld.LdGroupFold
import Cb.Ld.LdGroupProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} (Sh : GShape G)

theorem GShape.am_ok (h : Sh.OK) : Sh.am.OK := fun r => by
  have h1 := h.main r
  unfold GShape.am
  dsimp only
  cases hd : Sh.dst r with
  | inl b =>
      rw [hd] at h1
      exact h1
  | inr j =>
      rw [hd] at h1
      exact congrArg some h1

theorem GShape.az_ok (h : Sh.OK) : Sh.az.OK := h.rowsZ

end

theorem ldGroup_shape_laws : Spec.ldGroup_shape_laws := by
  intro E _ _ S G Sh h
  have hg := ldShape_gather E G.P G.A Sh.Rm Sh.Rz Sh.Cb Sh.Zb
  have hflat :=
    ldShape_comp E G.P _ _ _ Sh.view (Reshape.gather Sh.Rm Sh.Rz Sh.Cb Sh.Zb) h.view hg.1
  have htwo :=
    ldShape_two E G.P Sh.Cb Sh.Zb _ _ _ _ Sh.am Sh.az h.base (Sh.am_ok h) h.mask (Sh.az_ok h)
  have hcur := ldShape_curry E G.P Sh.Cb (Fin (Sh.h + Sh.g) → Bool) (Option Sh.Kp)
  have hcurL := ldShape_pairL E G.P _ _ (Sh.Zb.il (Fin Sh.h → Bool)) _ hcur.1
  have h1 := ldShape_comp E G.P _ _ _ Sh.flat _ hflat.1 htwo.1
  have h2 := ldShape_comp E G.P _ _ _ _ _ h1.1 hcurL.1
  refine ⟨h2.1, fun d dz e hd he hdz hez hv => ?_⟩
  exact h2.2 e (h1.2 e (hflat.2 e hv (hg.2 e)) (htwo.2 d dz e hd he hdz hez)) (hcurL.2 e (hcur.2 e))

theorem ldGroup_list : Spec.ldGroup_list := fun E _ _ S G Sh e L h hL =>
  ldShape_list E G.P _ _ Sh.rho e L (ldGroup_shape_laws E S G Sh h).1 hL

theorem ldGroup_block : Spec.ldGroup_block := by
  intro E B _ _ _ S G _ Sh Sb sl Z d t Lst mC mS mW h hY
  have hY' : (Sh.fold Sb sl Z).Hyp d G.e t Lst mC mS mW :=
    ⟨hY.codes, ⟨hY.errs.list, hY.errs.mcaC, hY.errs.mcaS, hY.errs.mcaW⟩,
      hY.inj, hY.deg, hY.pack, hY.qw, hY.zk⟩
  obtain ⟨h1, h2, -⟩ := ldTower_sum_after E G.P Sh.par G.e t Lst mC mS mW _ (Sh.form Sb sl Z)
    ((Sh.fold Sb sl Z).ext d) (sumGood_of_hyp _ d G.e t Lst mC mS mW hY')
  refine ⟨ldTower_seq E _ _ _ _ _ t t t
      (ldShape_block E G.P _ _ Sh.rho _ _ G.e t (ldGroup_shape_laws E S G Sh h).1) h1,
    ?_⟩
  show ([] ++ (ldSumAfter Sh.par G.e t Lst mC mS mW (Sh.form Sb sl Z)
        ((Sh.fold Sb sl Z).ext d)).R.shape).length = _
  rw [List.nil_append, h2]
  rfl

open Classical in
theorem ldGroup_fold : Spec.ldGroup_fold := by
  intro E B Kc St₀ Wp _ _ _ S G _ Sh kp _ Sb sl Z L E₀ A₀ hc dw d t Lst mC mS
    mW qi qF h hY hZ hL hF hq
  obtain ⟨hB, hlen⟩ := ldGroup_block E B S G Sh Sb sl Z d t Lst mC mS mW h hY
  refine ⟨ldGroup_run E B Kc St₀ Wp S G kp Sb sl Z L E₀ A₀ hc dw _
      (Sh.block Sb sl Z d t Lst mC mS mW) t t qi qF hZ hL hF hB hq,
    ?_⟩
  rw [(ldGroup_run_data E B Kc St₀ S G kp Sb sl Z 0 E₀ _ (Sh.block Sb sl Z d t Lst mC mS mW)).1,
    hlen]

theorem ldGroup_fold_kept : Spec.ldGroup_fold_kept := by
  intro E _ S G Sh γ j
  refine ⟨fun f p s => ?_, fun w c => ?_, fun w c => ?_⟩
  · show ∑ b, Alg.eqk γ b *
        LdCode.fstW (C₁ := Sh.Cb.il (Σ a, Sh.Rm a)) (C₂ := Sh.Zb.il (Σ a, Sh.Rz a))
          (Sh.flat.wd f) p (Sh.kept j, s) = _
    rw [← Finset.sum_mul, Alg.sum_eqk, one_mul]
  · show ∑ b, Alg.eqk γ b * (Sh.flat.up w).1 (.inl (Sh.kept j, c)) = _
    rw [← Finset.sum_mul, Alg.sum_eqk, one_mul]
  · show ∑ b, Alg.eqk γ b * (Sh.flat.up w).2 (.inl (Sh.kept j, c)) = _
    rw [← Finset.sum_mul, Alg.sum_eqk, one_mul]

theorem ldGroup_fold_kept_near : Spec.ldGroup_fold_kept_near := by
  intro E _ _ S G Sh d dz e h hd he hdz hez hv f w' hn γ j
  have hfix := (ldGroup_shape_laws E S G Sh h).2 d dz e hd he hdz hez hv f w' hn
  obtain ⟨-, h2, h3⟩ := ldGroup_fold_kept E S G Sh γ j
  refine ⟨fun c => ?_, fun c => ?_⟩
  · have := h2 (Sh.rho.dn w') c
    rwa [hfix] at this
  · have := h3 (Sh.rho.dn w') c
    rwa [hfix] at this

end Cb
