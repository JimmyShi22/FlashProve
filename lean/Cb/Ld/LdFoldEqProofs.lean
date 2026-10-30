-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFoldEqProofs.lean: the proofs of the statements of Cb/Ld/LdFoldEq.lean. Nothing is assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Main names (statements and hypotheses: Cb/Ld/LdFoldEq.lean):
  `ldFe_msg_fold`, `ldFe_rec_fold`: the message part, and the record's row, of a fold
  `ldFe_lift`: what is near the folded word, at a point that is not exceptional
  `ldFe_far`, `ldFe_none`: second regime: a wrong codeword's agreements; the bad points
  `ldFe_loc`, `ldFe_loc_far`: the draw of locations, first and second regime
  `ldFe_honest`, `ldFe_unique`: the two guards
  `ldFe_cnt`, `ldFe_cnt_nil`: first regime: the number of bad points (`LdIx.Bad`) of the fold
  `ldFe_mca_sum`: the agreement error for eq(γ, ·), from the errors for lines
The counts come from Code/Derived.lean (the points γ at which the coefficients eq(γ, ·) are bad,
`Code.Bad`, at every radius), Alg/Mle.lean (a non-zero multilinear extension has few zeros),
Cb/Ld/LdSumStepProofs.lean (the union bound over a list).
Limits: what the head of Cb/Ld/LdFoldEq.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFoldEq
import Cb.Gen.OodDecMinProofs
import Cb.Gen.OodDecPadProofs
import Cb.Gen.CodeEraseProofs
import Cb.Gen.FoldWordsProofs
import Cb.Ld.LdSumStepProofs
import Blocks.LowerKit

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

namespace LdIx
variable {E ι κ J : Type} [Field E] (X : LdIx E ι κ J)

theorem msg_foldAll (M : X.Row → κ → E) (γ : Fin X.v → E) :
    X.msg (foldAll γ M) = foldV γ (X.view M) := by
  funext j
  unfold msg foldV view
  rw [foldAll_apply]
  rfl

variable [Fintype κ]

theorem mulVec_foldAll (M : X.Row → κ → E) (γ : Fin X.v → E) :
    X.G.mulVec (foldAll γ M) = foldAll γ fun r => X.G.mulVec (M r) := by
  unfold foldAll
  have h1 := map_sum X.G.mulVecLin (fun r => Alg.eqk γ r • M r) Finset.univ
  simp only [map_smul, Matrix.mulVecLin_apply] at h1
  exact h1

variable [Fintype ι]

/-- the fold of a table near M is near the fold of M -/
theorem nearW_fold {e : ℕ} {f : X.Row → ι → E} {M : X.Row → κ → E}
    (h : DecodesTo X.G e f M) (γ : Fin X.v → E) :
    X.NearW e (foldAll γ f) (foldAll γ M) := by
  have h1 := decodesTo_foldAll E ι κ (Fin X.v) X.G e γ f M h
  exact decodesTo_word_iff.mp h1

/-- two full messages whose codewords are near one word, the radii together below the distance, are
equal -/
theorem nearW_unique {d e e' : ℕ} (hd : HasDist X.G d) (hee : e + e' < d) {w : ι → E} {u u' : κ → E}
    (h : X.NearW e w u) (h' : X.NearW e' w u') : u = u' := by
  have h1 : DecodesTo X.G e (fun _ : Unit => w) (fun _ => u) := decodesTo_word_iff.mpr h
  have h2 : DecodesTo X.G e' (fun _ : Unit => w) (fun _ => u') := decodesTo_word_iff.mpr h'
  exact h1.row_unique hd hee h2 (a := ()) (a' := ()) rfl

variable [Fintype J]

/-- what the decoder returns is the message part of a member of the list (at the radius eM) that has
the record's answers -/
theorem dec_cand {f : X.Row → ι → E} {rec : X.Rec} {U : X.Row × J → E} (h : X.dec f rec = some U) :
    ∃ M, DecodesTo X.G X.eM f M ∧ X.view M = U ∧ X.HasRec rec M := by
  obtain ⟨⟨M, hM, hv⟩, hy⟩ := ood_decMin_cand _ _ _ _ _ _ _ _ _ _ _ _ h
  refine ⟨M, hM, hv, ?_⟩
  unfold HasRec
  rw [hv]
  exact hy

/-- without a collision (`LdIx.Coll`) at the record's seed, the message part of a member of the
list (at the radius eM) that has the record's answers is what the decoder returns -/
theorem dec_of_cand {f : X.Row → ι → E} {rec : X.Rec} (hc : ¬ X.Coll f rec.1) {M : X.Row → κ → E}
    (hM : DecodesTo X.G X.eM f M) (hr : X.HasRec rec M) : X.dec f rec = some (X.view M) :=
  (ood_decMinS_good E ι κ X.Row (X.Row × J) X.G X.eM X.rank X.view X.ZR f
      rec.1 hc rec.2 (X.view M)).2
    ⟨⟨M, hM, rfl⟩, hr⟩

omit [Fintype κ] [Fintype ι] in
/-- the sample of a folded message part is the fold of the samples of the rows -/
theorem val_fold (ρ : X.Z.D) (M : X.Row → κ → E) (γ : Fin X.v → E) (s : X.Z.S) :
    X.Z.val ρ (X.msg (foldAll γ M)) s = ∑ r, Alg.eqk γ r * X.ZR.val ρ (X.view M) (r, s) := by
  have h1 : ∀ r, X.ZR.val ρ (X.view M) (r, s) = X.Z.val ρ (X.msg (M r)) s := fun r =>
    ood_val_rows_same E J X.Row X.Z ρ (X.view M) r s
  simp only [h1]
  unfold Sample.val msg
  simp only [foldAll_apply, Alg.mle, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring

end LdIx

section
variable {E ι κ J : Type} [Field E] [Fintype ι] [Fintype κ] [Fintype J]

omit [Fintype ι] [Fintype κ] [Fintype J] in
theorem ldFe_msg_fold : Spec.ldFe_msg_fold E ι κ J := fun X M γ => X.msg_foldAll M γ

omit [Fintype ι] [Fintype κ] in
theorem ldFe_rec_fold : Spec.ldFe_rec_fold E ι κ J := by
  intro X rec M hM γ
  funext s
  rw [X.val_fold, hM]
  rfl

omit [Fintype J] in
theorem ldFe_lift : Spec.ldFe_lift E ι κ J := by
  intro X d e' f γ u hd he hx hu
  classical
  set S : Finset ι := agr X.G (fun _ : Unit => foldAll γ f) fun _ => u with hS
  have hcard : Fintype.card ι ≤ S.card + e' :=
    (decodesTo_iff_agr E ι κ Unit X.G e' _ _).1 (decodesTo_word_iff.mpr hu)
  have hagr : ∀ j ∈ S, foldAll γ f j = X.G.mulVec u j := fun j hj =>
    (agreesOn_iff_subset E ι κ Unit X.G S _ _).2 (le_of_eq hS) j hj ()
  have hfold : ∀ _a : Unit,
      ∑ r, Alg.eqk γ r • f r ∈ Code.agreeOn (LinearMap.range X.G.mulVecLin) S := fun _ =>
    ⟨X.G.mulVec u, ⟨u, rfl⟩, fun j hj => hagr j hj⟩
  have hrows : ∀ r, f r ∈ Code.agreeOn (LinearMap.range X.G.mulVecLin) S := fun r =>
    Code.mem_agreeOn_of_not_bad hx hcard hfold r ()
  choose c hc hfc using hrows
  choose M hM using hc
  have hA : AgreesOn X.G S f M := fun j hj r => by
    rw [hfc r j hj, ← hM r]
    rfl
  have hlarge : Fintype.card ι < S.card + d := by omega
  refine ⟨M, (erase_iff E ι κ X.Row X.G d hd S f M).2 ⟨hlarge, hA⟩, ?_, ?_⟩
  · exact erase_decodesTo E ι κ X.Row X.G d e' hd S f M
      ((erase_iff E ι κ X.Row X.G d hd S f M).2 ⟨hlarge, hA⟩) hcard
  · have h1 : AgreesOn X.G S (fun _ : Unit => foldAll γ f)
        (fun _ => foldAll γ M) := fun j hj _ => by
      show foldAll γ f j = X.G.mulVec (foldAll γ M) j
      rw [X.mulVec_foldAll, foldAll_apply, foldAll_apply]
      exact congrArg (fun t => Alg.mle t γ) (funext fun r => hA j hj r)
    have h2 : AgreesOn X.G S (fun _ : Unit => foldAll γ f) (fun _ => u) := fun j hj _ => hagr j hj
    exact congrFun (agreesOn_unique E ι κ Unit X.G d hd S hlarge _ _ _ h1 h2) ()

omit [Fintype J] in
theorem ldFe_far : Spec.ldFe_far E ι κ J := by
  intro X d e₀ f M γ u hd hM hne
  exact Code.cnt_agree_mulVec_add_le hd hM (Alg.eqk γ) hne

theorem ldFe_none : Spec.ldFe_none E ι κ J := by
  intro X d e' f rec hd he hdec γ hbad
  obtain ⟨u, hu, -, hw⟩ := hbad
  obtain ⟨U, hU⟩ := Option.ne_none_iff_exists'.mp hdec
  obtain ⟨M, hM, hv, -⟩ := X.dec_cand hU
  have h1 : u = foldAll γ M := X.nearW_unique hd he hu (X.nearW_fold hM γ)
  refine hw U hU ?_
  rw [h1, X.msg_foldAll, hv]

/-- lists of positions inside a set of at most m positions: there are at most m ^ t of length t -/
theorem ldk_cnt_lists_le {ι : Type} [Fintype ι] (P : ι → Prop) (m t : ℕ) (h : cnt P ≤ m) :
    cnt (fun Q : Fin t → ι => ∀ i, P (Q i)) ≤ m ^ t := by
  rw [cnt_forall_pow]
  exact Nat.pow_le_pow_left h t

omit [Fintype J] in
/-- a codeword that is farther than e' from a word has the values of the word at all t drawn
positions for few lists: at most (n - e' - 1) ^ t, n the number of positions -/
theorem LdIx.cnt_far_lists (X : LdIx E ι κ J) {e' : ℕ} (t : ℕ) {w : ι → E}
    {u : κ → E} (h1 : ¬ X.NearW e' w u) :
    cnt (fun Q : Fin t → ι => ∀ i, X.G.mulVec u (Q i) = w (Q i)) ≤
      (Fintype.card ι - e' - 1) ^ t := by
  refine ldk_cnt_lists_le (fun j => X.G.mulVec u j = w j) _ t ?_
  unfold LdIx.NearW at h1
  have h2 := cnt_add_cnt_not fun j => X.G.mulVec u j = w j
  have h3 : cnt (fun j => ¬ X.G.mulVec u j = w j) = cnt (fun j => w j ≠ X.G.mulVec u j) :=
    cnt_congr fun j => ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  omega

theorem ldFe_loc : Spec.ldFe_loc E ι κ J := by
  intro X e' t f rec γ u hb hr hw
  exact X.cnt_far_lists t fun h => hb ⟨u, h, hr, hw⟩

theorem ldFe_loc_far : Spec.ldFe_loc_far E ι κ J := by
  intro X d t f rec γ u hd hdec hw
  refine ldk_cnt_lists_le (fun j => X.G.mulVec u j = foldAll γ f j) _ t ?_
  obtain ⟨U, hU⟩ := Option.ne_none_iff_exists'.mp hdec
  obtain ⟨M, hM, hv, -⟩ := X.dec_cand hU
  have hne : u ≠ foldAll γ M := fun h => hw U hU (by rw [h, X.msg_foldAll, hv])
  have := ldFe_far X d X.eM f M γ u hd hM hne
  omega

theorem ldFe_honest : Spec.ldFe_honest E ι κ J := fun X d M ρ hd he =>
  ood_decMinS_mulVec E ι κ X.Row (X.Row × J) X.G d X.eM X.rank X.view X.ZR M hd he ρ

theorem ldFe_unique : Spec.ldFe_unique E ι κ J := by
  intro X d f rec U hd h2
  refine ⟨ood_decMinS_unique E ι κ X.Row (X.Row × J) X.G d X.eM X.rank X.view
      X.ZR f rec.1 rec.2 U hd h2,
    ?_⟩
  rintro ⟨u, u', ⟨M, hM, rfl⟩, ⟨M', hM', rfl⟩, hne, -⟩
  exact hne (by rw [hM.unique hd h2 hM'])

variable [Fintype E]

omit [Fintype E] in
/-- under hd, he, hee, hc (d a distance of G, eM < d, e' ≤ eM, no collision at the record's seed):
at a bad point that is not exceptional, some member of the list (at the radius e') lacks the
record's answers, and the extension of its defects (its samples less the record's answers, row by
row) vanishes at that point -/
theorem ldk_bad_split (X : LdIx E ι κ J) {d e' : ℕ} {f : X.Row → ι → E} {rec : X.Rec}
    (hd : HasDist X.G d) (he : X.eM < d) (hee : e' ≤ X.eM) (hc : ¬ X.Coll f rec.1) {γ : Fin X.v → E}
    (hb : X.Bad f rec e' γ) (hx : ¬ X.Exc f e' γ) :
    ∃ M,
      DecodesTo X.G e' f M ∧
      ¬ X.HasRec rec M ∧
      ∀ s, Alg.mle (fun r => X.ZR.val rec.1 (X.view M) (r, s) - rec.2 (r, s)) γ = 0 := by
  obtain ⟨u, hu, hr, hw⟩ := hb
  obtain ⟨M, -, hM, hf⟩ := ldFe_lift X d e' f γ u hd (lt_of_le_of_lt hee he) hx hu
  refine ⟨M, hM, fun hrec => ?_, fun s => ?_⟩
  · refine hw _ (X.dec_of_cand hc (hM.mono hee) hrec) ?_
    rw [← hf, X.msg_foldAll]
  · have h1 := congrFun hr s
    rw [← hf, X.val_fold] at h1
    unfold Alg.mle
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [h1]
    exact sub_self _

theorem ldFe_cnt : Spec.ldFe_cnt E ι κ J := by
  intro X d e' bad L f rec hd he hee hm hL hc
  classical
  have hL' : cnt (DecodesTo X.G e' f) ≤ L := by
    rw [cnt_eq_card_filter]
    exact hL _ fun M hM => (Finset.mem_filter.1 hM).2
  refine (cnt_le_add (Q := X.Exc f e')
      (R := fun γ =>
          ∃ M,
            DecodesTo X.G e' f M ∧
            (¬ X.HasRec rec M ∧
              ∀ s, Alg.mle (fun r => X.ZR.val rec.1 (X.view M) (r, s) - rec.2 (r, s)) γ = 0))
      ?_).trans
    (Nat.add_le_add (hm f) (lds_cnt_list _ _ _ _ L _ hL' ?_))
  · intro γ hb
    by_cases hx : X.Exc f e' γ
    · exact Or.inl hx
    · exact Or.inr (ldk_bad_split X hd he hee hc hb hx)
  · intro M _
    refine cnt_and_le fun hrec => ?_
    have h1 : ∃ n : X.Row × X.Z.S, X.ZR.val rec.1 (X.view M) n ≠ rec.2 n := by
      by_contra hall
      push Not at hall
      exact hrec (funext hall)
    obtain ⟨⟨r, s⟩, hrs⟩ := h1
    have hne : (fun r => X.ZR.val rec.1 (X.view M) (r, s) - rec.2 (r, s)) ≠ 0 := fun h0 =>
      hrs (sub_eq_zero.mp (congrFun h0 r))
    have h2 := Alg.count_mle_zero_le _ hne
    rw [Fintype.card_fin] at h2
    exact (cnt_mono fun γ hγ => hγ s).trans h2

theorem ldFe_cnt_nil : Spec.ldFe_cnt_nil E ι κ J := by
  intro X d e' bad f rec hS hd he hee hm hc
  refine (cnt_mono fun γ hb => ?_).trans (hm f)
  by_contra hx
  obtain ⟨M, -, hrec, -⟩ := ldk_bad_split X hd he hee hc hb hx
  exact hrec (funext fun n => (hS.false n.2).elim)

omit [Fintype J] in
theorem ldFe_mca_sum : Spec.ldFe_mca_sum E ι κ J := by
  intro X e' c h f
  exact Alg.le_mul_pow_pred Fintype.card_pos
    (Code.cnt_bad_eqk_mul_sum c X.v h fun r (_ : Unit) => f r)

end
end Cb
