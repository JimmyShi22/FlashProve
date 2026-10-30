-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTreeProofs.lean: the proofs of the statements of Cb/Ld/LdLkpTree.lean (the product tree
with masked claims).
`LdLkp.sum_line` is an auxiliary lemma.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdLkpTree.lean):
  `ldLkp_tree`: the tree.
-/
import Cb.Ld.LdLkpTree
import Cb.Gen.GpAlgProofs

set_option autoImplicit false

namespace Cb
open Blocks Finset Prob Cb.Gp Cb.LdLkp Iop IOR

/-- Auxiliary: the combined mask form at the entries. -/
theorem LdLkp.sum_line {E N : Type} [Field E] [Fintype N] (ρ : E) (a b μ : N → E) :
    ∑ i, ((1 - ρ) * a i + ρ * b i) * μ i = (1 - ρ) * ∑ i, a i * μ i + ρ * ∑ i, b i * μ i := by
  simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]

theorem ldLkp_lev_iff_sum : Spec.ldLkp_lev_iff_sum := by
  intro E St M N _ _ T l x m hl
  have he := (claim_iff_sum E T.g T.n (T.fac x.1 m) l x.2.1.pt _ hl).mpr rfl
  unfold Claim at he
  unfold Tree.lev Tree.sum MCl.Holds
  rw [he]

theorem ldLkp_line_fwd : Spec.ldLkp_line_fwd := by
  intro E St M N _ _ T l x m ρ h
  obtain ⟨h0, h1, hr⟩ := h
  refine ⟨?_, hr⟩
  show ext (l + 1 + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1)) (consPt ρ x.2.1.pt) +
      ∑ i, ((1 - ρ) * x.2.1.mf₀ i + ρ * x.2.1.mf₁ i) * T.ent m i =
    (1 - ρ) * x.2.1.tg₀ + ρ * x.2.1.tg₁
  have hidx : l + 1 + T.g = l + T.g + 1 := by omega
  rw [hidx, ext_succ_consPt, sum_line]
  have h1' : ext (l + T.g)
          (fun X => lvl T.g T.n (T.fac x.1 m) (l + 1) (X + 2 ^ (l + T.g))) x.2.1.pt +
        ∑ i, x.2.1.mf₁ i * T.ent m i = x.2.1.tg₁ := h1
  linear_combination (1 - ρ) * h0 + ρ * h1'

theorem ldLkp_line_cnt : Spec.ldLkp_line_cnt := by
  intro E St M N _ _ _ T l x m
  by_cases hends : T.ends l x m
  · exact (le_of_eq (cnt_false fun ρ h => h.2 hends)).trans (Nat.zero_le _)
  by_cases hr : RowsHold x.2.2 (T.ent m) ∧ T.more x.1 m
  · have hne : ext (l + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1)) x.2.1.pt ≠
      x.2.1.tg₀ - ∑ i, x.2.1.mf₀ i * T.ent m i ∨
        ext (l + T.g) (up (l + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1))) x.2.1.pt ≠
            x.2.1.tg₁ - ∑ i, x.2.1.mf₁ i * T.ent m i := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact hends ⟨by rw [hcon.1]; ring, by rw [hcon.2]; ring, hr⟩
    refine (cnt_mono fun ρ h => ?_).trans
      (cnt_line_le_one E (l + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1)) x.2.1.pt _ _ hne)
    have h0 : ext (l + 1 + T.g) (lvl T.g T.n (T.fac x.1 m) (l + 1)) (consPt ρ x.2.1.pt) +
          ∑ i, ((1 - ρ) * x.2.1.mf₀ i + ρ * x.2.1.mf₁ i) * T.ent m i =
        (1 - ρ) * x.2.1.tg₀ + ρ * x.2.1.tg₁ := h.1.1
    have hidx : l + 1 + T.g = l + T.g + 1 := by omega
    rw [hidx, sum_line] at h0
    linear_combination h0
  · exact (le_of_eq (cnt_false fun ρ h => hr h.1.2)).trans (Nat.zero_le _)

theorem ldLkp_lev_top : Spec.ldLkp_lev_top := by
  intro E St M N _ _ T x m
  unfold Tree.lev
  rw [lvl_top]

theorem ldLkp_lev_zero : Spec.ldLkp_lev_zero := by
  intro E St M N _ _ T x m hg
  have h : ext (0 + 0) (lvl 0 T.n (T.fac x.1 m) 0) x.2.1.pt =
      ∏ b ∈ range (2 ^ T.n), T.fac x.1 m b := by
    simp [Blocks.ext, Blocks.eqN, Blocks.lvl]
  unfold Tree.lev MCl.Holds
  rw [hg, h]

theorem ldLkp_line : Spec.ldLkp_line := by
  intro E _ _ S E₀ St N Wp _ T on hon l q
  refine sig_draw E S Unit (EX St E N) (TX St E N) Wp E E₀ lineNx _ _ 1 q ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro st y w β h
    exact ⟨ldLkp_line_fwd E St (Ms S E₀) N T l st (y, w.1) β h.1, h.2⟩
  · intro st y m _
    refine (cnt_mono fun β hβ => ?_).trans (ldLkp_line_cnt E St (Ms S E₀) N T l st (y, m))
    obtain ⟨wp, h1, h2⟩ := hβ
    exact ⟨h1, h2⟩

theorem ldLkp_tree : Spec.ldLkp_tree := by
  intro E _ _ S E₀ St N Wp _ T on hon p d n' hn hp
  rw [hn]
  refine bk_chain_goodB Unit _ (Ex S E₀) _ (fun l => level (p l) d) d
    (fun l => jt S E₀ Wp (onFst on) (honFst hon) (T.lev l)) n' fun l hl => ?_
  have hls : T.lev l = T.sum l :=
    funext fun x => funext fun m => propext (ldLkp_lev_iff_sum E St (Ms S E₀) N T l x m (by omega))
  have g1 := hp l hl
  rw [← hls] at g1
  have g2 := ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mp
    (goodT_of_good _ _ _ _ _ _ _ _ _ _ _ _ _
      (ldLkp_line E S E₀ St N Wp T on hon l fun _ => True).good)).1
  exact goodB_seq Unit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ g1 g2

theorem ldLkp_tree_rounds : Spec.ldLkp_tree_rounds := by
  intro E _ _ S E₀ St N Wp p d n'
  unfold tree
  rw [bk_chain_rounds]
  refine sum_congr rfl fun l _ => ?_
  exact List.length_append

end Cb
