-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinWordsProofs.lean: the proofs of the statements of Cb/Ld/LdLinWords.lean. Nothing is
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

The counts of the fold and of the locations are those of Cb/Ld/LdFoldEqProofs.lean; the others come
from Alg/Mle.lean (two different multilinear extensions agree at few points). (The lemmas cnt_…:
Prob/Cnt.lean, Prob/Count.lean, Blocks/LowerKit.lean; ldFe_…: Cb/Ld/LdFoldEqProofs.lean.)
The backward step (`ldLin_back`), under the hypotheses of its statement: the locations are not bad
and u' meets `X.RecRow` and `ColR`, so u' is not wrong (`X.Wrong`): the index decodes to some U, and
the message part of u' is the fold of U; ζ is not bad and `FoldR` holds, so ω' is `omOf U ψ*` (by
`ldLin_om_fold`); the shared point is not bad and `Dot` holds, so w' is `wOf U g`; then `Eval` is
the claim (`ldLin_eval_iff`).
-/
import Cb.Ld.LdLinWords
import Cb.Ld.LdFoldEqProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

namespace LdLinW
variable {E ι κ J Y : Type} [Field E] (D : LdLinW E ι κ J Y)

omit [Field E] in
/-- a sum over the columns is a sum over code rows and places in a block -/
theorem sum_col {M : Type} [AddCommMonoid M] (F : D.Col → M) :
    ∑ c, F c = ∑ r : D.X.Row, ∑ j : Fin D.klo → Bool, F (Sum.elim r j) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow (Fin D.X.v) (Fin D.klo) Bool).symm _ _
    fun _ => rfl).symm

theorem eqk_pt (ψ : D.Pt) (r : D.X.Row) (j : Fin D.klo → Bool) :
    Alg.eqk (D.pt ψ) (Sum.elim r j) = Alg.eqk ψ.1 r * Alg.eqk ψ.2 j := by
  unfold pt
  rw [Alg.eqk_sumElim]
  rfl

omit [Field E] in
theorem mat_elim (U : D.X.Row × J → E) (y : Y) (r : D.X.Row) (j : Fin D.klo → Bool) :
    D.mat U y (Sum.elim r j) = U (r, D.lay (y, j)) := rfl

variable [Fintype Y]

/-- ⟨g, mat·eq(ψ, ·)⟩ is the extension of gᵀ·mat at ψ -/
theorem dot_honest (U : D.X.Row × J → E) (g : Y → E) (ψ : D.Pt) :
    ∑ y, g y * D.omOf U ψ y = Alg.mle (D.wOf U g) (D.pt ψ) := by
  unfold omOf wOf Alg.mle
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => by ring

end LdLinW

section
variable {E ι κ J Y : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldLin_om_fold : Spec.ldLin_om_fold E ι κ J Y := by
  intro D U ψs
  funext y
  unfold LdLinW.omOf LdLinW.omU foldV
  rw [D.sum_col, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [D.eqk_pt, D.mat_elim]; ring

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLin_eval_iff : Spec.ldLin_eval_iff E ι κ J Y := by
  intro D U g ψ rest τ
  unfold LdLinW.Eval LdLinW.Claim
  have h : Alg.mle (D.wOf U g) (D.pt ψ) = ∑ y, ∑ c, g y * Alg.eqk (D.pt ψ) c * D.mat U y c := by
    unfold LdLinW.wOf Alg.mle
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun c _ => by ring
  rw [h]

omit [Fintype ι] in
theorem ldLin_complete : Spec.ldLin_complete E ι κ J Y := by
  intro D M rec g ψ rest τ ψs t Q ζ hrec hcl
  refine ⟨ldFe_rec_fold D.X rec M hrec ψs.1, fun i => ?_, ?_,
    (ldLin_eval_iff D _ g ψ rest τ).2 hcl, D.dot_honest _ g ψs⟩
  · rw [D.X.mulVec_foldAll]
  · unfold LdLinW.FoldR
    rw [ldLin_om_fold D (D.X.view M) ψs, D.X.msg_foldAll]

omit [Fintype Y] in
theorem ldLin_cnt_loc : Spec.ldLin_cnt_loc E ι κ J Y := by
  intro D e' t f rec γ u' hb
  unfold LdLinW.BadLoc
  exact cnt_and_le fun hr => cnt_and_le fun hw => ldFe_loc D.X e' t f rec γ u' hb hr hw

omit [Fintype Y] in
theorem ldLin_cnt_loc_far : Spec.ldLin_cnt_loc_far E ι κ J Y := by
  intro D d t f rec γ u' hd hdec
  unfold LdLinW.BadLoc
  exact cnt_and_le fun _ => cnt_and_le fun hw => ldFe_loc_far D.X d t f rec γ u' hd hdec hw

theorem ldLin_back : Spec.ldLin_back E ι κ J Y := by
  intro D t f rec g ψ rest τ w' ψs u' Q ω' ζ hP hL hZ hrec hcol hfold heval hdot
  have hw : ¬ D.X.Wrong f rec ψs.1 u' := fun h => hL ⟨hrec, h, hcol⟩
  unfold LdIx.Wrong at hw
  push Not at hw
  obtain ⟨U, hU, hmsg⟩ := hw
  refine ⟨U, hU, ?_⟩
  have hom : ω' = D.omOf U ψs := by
    by_contra hne
    refine hZ ⟨fun h => hne ?_, hfold⟩
    rw [h, hmsg, ldLin_om_fold D U ψs]
  have hww : w' = D.wOf U g := by
    by_contra hne
    refine hP U hU ⟨hne, ?_⟩
    rw [← D.dot_honest U g ψs, ← hom]
    exact hdot.symm
  rw [hww] at heval
  exact (ldLin_eval_iff D U g ψ rest τ).1 heval

variable [Fintype E]

omit [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- counting points as pairs or as one vector of coordinates -/
theorem ldk_cnt_pt (D : LdLinW E ι κ J Y) (P : (D.CV → E) → Prop) :
    cnt (fun ψ : D.Pt => P (D.pt ψ)) = cnt P :=
  cnt_equiv (Equiv.sumArrowEquivProdArrow (Fin D.X.v) (Fin D.klo) E).symm P

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLin_cnt_pt : Spec.ldLin_cnt_pt E ι κ J Y := by
  intro D U g w'
  unfold LdLinW.BadPt
  refine cnt_and_le fun hne => ?_
  rw [ldk_cnt_pt D fun z => Alg.mle w' z = Alg.mle (D.wOf U g) z]
  have h := Alg.count_mle_eq_le w' (D.wOf U g) hne
  rwa [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h

/-- the instances' part of the bad shared points -/
theorem ldk_cnt_inst (D : LdLinW E ι κ J Y) {N : ℕ} (f : D.X.Row → ι → E) (rec : D.X.Rec)
    (a : Fin N → Option ((Y → E) × (D.Col → E))) :
    cnt (fun ψs : D.Pt =>
        ∃ U, D.X.dec f rec = some U ∧ ∃ c gw, a c = some gw ∧ D.BadPt U gw.1 gw.2 ψs) ≤
      N * ((D.X.v + D.klo) * Fintype.card E ^ (D.X.v + D.klo - 1)) := by
  refine cnt_exists_unique_le (fun _ _ hb hb' => Option.some.inj (hb.symm.trans hb')) fun U _ => ?_
  have := cnt_exists_le_mul
    (fun (c : Fin N) (ψs : D.Pt) => ∃ gw, a c = some gw ∧ D.BadPt U gw.1 gw.2 ψs)
    ((D.X.v + D.klo) * Fintype.card E ^ (D.X.v + D.klo - 1)) (fun c =>
      cnt_exists_unique_le (fun _ _ hb hb' => Option.some.inj (hb.symm.trans hb'))
        fun gw _ => ldLin_cnt_pt D U gw.1 gw.2)
  simpa using this

/-- the bad shared points, from any bound on the bad points of the fold -/
theorem ldk_cnt_badSh (D : LdLinW E ι κ J Y) {N e' εf : ℕ} (f : D.X.Row → ι → E) (rec : D.X.Rec)
    (a : Fin N → Option ((Y → E) × (D.Col → E))) (h : cnt (D.X.Bad f rec e') ≤ εf) :
    cnt (D.BadSh f rec e' a) ≤
      εf * Fintype.card E ^ D.klo +
        N * ((D.X.v + D.klo) * Fintype.card E ^ (D.X.v + D.klo - 1)) := by
  unfold LdLinW.BadSh
  refine (cnt_or_le _ _).trans (Nat.add_le_add ?_ (ldk_cnt_inst D f rec a))
  rw [cnt_fst (D := Fin D.klo → E) (D.X.Bad f rec e'), Fintype.card_fun, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ h

theorem ldLin_cnt_sh :
    Spec.ldLin_cnt_sh E ι κ J Y := fun D d e' bad L _ f rec a hd he hee hm hL hc =>
  ldk_cnt_badSh D f rec a (ldFe_cnt D.X d e' bad L f rec hd he hee hm hL hc)

theorem ldLin_cnt_sh_far : Spec.ldLin_cnt_sh_far E ι κ J Y := by
  intro D d e' N f rec a hd he hdec
  refine (cnt_mono fun ψs h => ?_).trans (ldk_cnt_inst D f rec a)
  exact h.resolve_left (ldFe_none D.X d e' f rec hd he hdec ψs.1)

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldLin_cnt_zeta : Spec.ldLin_cnt_zeta E ι κ J Y := by
  intro D um ψlo ω' hpy
  unfold LdLinW.BadZeta LdLinW.FoldR
  refine cnt_and_le fun hne => ?_
  have h := Alg.count_mle_zero_of_injective D.py hpy (ω' - D.omU um ψlo) (sub_ne_zero.mpr hne)
  rw [Fintype.card_fin] at h
  refine (cnt_mono fun ζ hζ => ?_).trans h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hζ, sub_self]

end
end Cb
