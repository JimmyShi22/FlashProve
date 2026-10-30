-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpProofs.lean: the proofs of the statements of Cb/Ld/LdLkp.lean (a lookup argument inside
an interactive oracle proof: the first steps of one instantiation by products).

The theorems are "ldLkp_* : Cb.Spec.ldLkp_*"; before them auxiliary lemmas: two records of relations
with equal fields are equal; if W ≤ 2^w, the claim after the first challenge reads the bits at u <
2^T, j < 2^w only; two sums exchanged.
-/
import Cb.Ld.LdLkp
import Cb.Ld.LdLkpTreeProofs
import Cb.Gen.LkpAlgProofs

set_option autoImplicit false

namespace Cb
open Blocks Finset Prob Cb.Gp Cb.Lkp Cb.LdLkp Iop IOR

/-- two records of relations with equal fields are equal -/
theorem LdLkp.rels_ext' {K X : Type} {Ex : ExtSpec} {W : Type} {A B : Rels K X Ex W}
    (h1 : A.rel = B.rel) (h2 : A.relR = B.relR) (h3 : A.on = B.on) (h4 : A.core = B.core) :
    A = B := by
  cases A
  cases B
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- if W ≤ 2^w, `Mid` (Cb/Gen/LkpAlg.lean) reads the bits at u < 2^T, j < 2^w only -/
theorem LdLkp.mid_congr {E : Type} [Field E] (n T w W : ℕ) (key t : ℕ → E)
    (M M' : ℕ → ℕ → E) (al : E) (hW : W ≤ 2 ^ w)
    (h : ∀ u < 2 ^ T, ∀ j < 2 ^ w, M u j = M' u j) (hM : Mid n T w W key t M' al) :
    Mid n T w W key t M al := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun u hu j hj => by rw [h u hu j hj]; exact h1 u hu j hj, ?_, ?_⟩
  · unfold NumKeys at h2 ⊢
    rw [← h2]
    exact sum_congr rfl fun u hu =>
      sum_congr rfl fun j hj => by
        rw [h u (mem_range.mp hu) j (lt_of_lt_of_le (mem_range.mp hj) hW)]
  · rw [h3]
    refine prod_congr rfl fun j hj => ?_
    have ht : tabProd T t M al j = tabProd T t M' al j :=
      prod_congr rfl fun u hu => by
        rw [h u (mem_range.mp hu) j (lt_of_lt_of_le (mem_range.mp hj) hW)]
    rw [ht]

/-- the mask form of a point of a forest, at the entries -/
theorem LdLkp.sum_at {E N : Type} [Field E] [Fintype N] (s : Finset ℕ) (c : ℕ → E)
    (hf : ℕ → N → E) (μ : N → E) :
    ∑ i, (∑ θ ∈ s, c θ * hf θ i) * μ i = ∑ θ ∈ s, c θ * ∑ i, hf θ i * μ i := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun θ _ => sum_congr rfl fun i _ => by ring

theorem ldLkp_sub_of_subR : Spec.ldLkp_sub_of_subR := by
  intro E _ S E₀ St N Wp _ B L mult on hon ent h
  have e1 : S.over
        (rideJ S (⟨fun st y w => hon st (y, w.1) w.2, fun _ _ => True, on,
            fun _ => ()⟩ : Rels Unit St E₀ (S.Msg × Wp))
          id (L.inP mult) L.inR) =
      jt2 S E₀ Wp on hon (L.inP mult) L.inR :=
    congrArg S.over
      (rels_ext' (funext fun x => funext fun y => funext fun w => propext and_comm)
        (funext fun a => funext fun w => true_and _) rfl rfl)
  have e2 : S.over
        (rideJ S (⟨fun st y w => hon st (y, w.1) w.2, fun _ _ => True, on,
            fun _ => ()⟩ : Rels Unit St E₀ (S.Msg × Wp))
          Prod.fst (L.out id ent) (L.out id ent)) =
      jt S E₀ Wp (onFst on) (honFst fun st m' wp => hon st (id m') wp) (L.out id ent) :=
    congrArg S.over
      (rels_ext' (funext fun x => funext fun y => funext fun w => propext and_comm)
        (funext fun a => funext fun w => true_and _) rfl rfl)
  unfold SubR.OK at h
  rw [e1, e2] at h
  exact goodB_cf _ _ _ _ _ _ _ _ _ _ _ _ _ h

theorem ldLkp_lambda_fwd : Spec.ldLkp_lambda_fwd := by
  intro E St M N _ B p st m lam hA h
  obtain ⟨⟨hin, hmore⟩, hmult⟩ := h
  refine ⟨⟨mid_congr B.v B.d B.w B.W _ (B.tab st) _ _ lam hA.1 hmult
        ⟨honest_bits E B.v B.d B.w B.W _ _,
          honest_numKeys E B.v B.d B.W _ _ hA.2.1 hin,
          honest_ident E B.v B.d B.W _ _ hA.2.1 hin lam⟩,
      hmore⟩,
    hmult⟩

theorem ldLkp_lambda_cnt : Spec.ldLkp_lambda_cnt := by
  intro E St M N _ _ p _ B st m hA
  by_cases hin : InTable B.v B.d (B.key st m) (B.tab st)
  · exact (le_of_eq (cnt_false fun lam h => h.2 ⟨hin, h.1.2⟩)).trans (Nat.zero_le _)
  · exact (cnt_mono fun lam h => h.1.1).trans
      (cnt_badAl_le E p B.v B.d B.w B.W _ (B.tab st) (B.bit m) hA.1 hA.2.1 hA.2.2 hin)

theorem ldLkp_lambda : Spec.ldLkp_lambda := by
  intro E _ _ p _ S E₀ St N Wp B on hon q hA
  refine sig_draw E S Unit St (St × E) Wp E E₀ Prod.mk _ _ (2 ^ B.v - 1) q ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro st y w β h
    exact ⟨ldLkp_lambda_fwd E St (Ms S E₀) N B p st (y, w.1) β hA h.1, h.2⟩
  · intro st y m _
    refine (cnt_mono fun β hβ => ?_).trans (ldLkp_lambda_cnt E St (Ms S E₀) N p B st (y, m) hA)
    obtain ⟨wp, h1, h2⟩ := hβ
    exact ⟨h1, h2⟩

theorem ldLkp_root_fwd : Spec.ldLkp_root_fwd := by
  intro E St M N _ _ T x m ϱ h
  obtain ⟨h0, hr⟩ := h
  refine ⟨?_, hr⟩
  show Blocks.ext (0 + T.g) (lvl T.g T.n (T.fac x.1 m) 0) (nat ϱ) +
      ∑ i, (∑ θ ∈ range (2 ^ T.g), eqN T.g 0 (nat ϱ) θ * x.2.1.hf θ i) * T.ent m i =
    ∑ θ ∈ range (2 ^ T.g), eqN T.g 0 (nat ϱ) θ * x.2.1.ht θ
  rw [Nat.zero_add, sum_at]
  unfold Blocks.ext
  rw [← sum_add_distrib]
  exact sum_congr rfl fun θ hθ => by rw [← h0 θ (mem_range.mp hθ)]; ring

theorem ldLkp_root_cnt : Spec.ldLkp_root_cnt := by
  intro E St M N _ _ _ T x m
  by_cases hroots : T.roots x m
  · exact (le_of_eq (cnt_false fun ϱ h => h.2 hroots)).trans (Nat.zero_le _)
  by_cases hr : RowsHold x.2.2 (T.ent m) ∧ T.more x.1 m
  · have hne : ∃ θ < 2 ^ T.g,
        lvl T.g T.n (T.fac x.1 m) 0 θ + ∑ i, x.2.1.hf θ i * T.ent m i - x.2.1.ht θ ≠ 0 := by
      by_contra hcon
      refine hroots ⟨fun θ hθ => ?_, hr⟩
      by_contra hθne
      exact hcon ⟨θ, hθ, sub_ne_zero.mpr hθne⟩
    refine (cnt_mono fun ϱ h => ?_).trans (cnt_ext_zero_le T.g _ hne)
    have h0 : Blocks.ext (0 + T.g) (lvl T.g T.n (T.fac x.1 m) 0) (nat ϱ) +
          ∑ i, (∑ θ ∈ range (2 ^ T.g), eqN T.g 0 (nat ϱ) θ * x.2.1.hf θ i) * T.ent m i =
        ∑ θ ∈ range (2 ^ T.g), eqN T.g 0 (nat ϱ) θ * x.2.1.ht θ := h.1.1
    rw [Nat.zero_add, sum_at] at h0
    unfold Blocks.ext at h0 ⊢
    simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
    rw [h0, sub_self]
  · exact (le_of_eq (cnt_false fun ϱ h => hr h.1.2)).trans (Nat.zero_le _)

theorem ldLkp_root : Spec.ldLkp_root := by
  intro E _ _ S E₀ St N Wp _ T on hon q
  refine sig_draw E S Unit (RX St E N) (TX St E N) Wp (Fin T.g → E) E₀ (rootNx T.g) _ _ _ q ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro st y w β h
    exact ⟨ldLkp_root_fwd E St (Ms S E₀) N T st (y, w.1) β h.1, h.2⟩
  · intro st y m _
    refine (cnt_mono fun β hβ => ?_).trans (ldLkp_root_cnt E St (Ms S E₀) N T st (y, m))
    obtain ⟨wp, h1, h2⟩ := hβ
    exact ⟨h1, h2⟩

theorem ldLkp_rootsK : Spec.ldLkp_rootsK := by
  intro E St M N _ _ B more x m
  exact ldLkp_lev_zero E (St × E) M N (B.treeK more) x m rfl

theorem ldLkp_rootsT : Spec.ldLkp_rootsT := by
  intro E St M N _ _ B more x m
  have hrel := (relT_iff E B.d B.w (B.tab x.1.1) (B.bit m) x.1.2 fun j =>
      tabProd B.d (B.tab x.1.1) (B.bit m) x.1.2 j).mpr fun _ _ => rfl
  have hl : ∀ θ < 2 ^ B.w, lvl B.w B.d (facT B.w (B.tab x.1.1) (B.bit m) x.1.2) 0 θ =
      tabProd B.d (B.tab x.1.1) (B.bit m) x.1.2 θ := fun θ hθ => by
    have e : lvl B.w B.d (facT B.w (B.tab x.1.1) (B.bit m) x.1.2) 0 θ =
        ∏ b ∈ range (2 ^ B.d), facT B.w (B.tab x.1.1) (B.bit m) x.1.2 (b * 2 ^ B.w + θ) := by
      simp [Blocks.lvl]
    exact e.trans (hrel θ hθ)
  constructor
  · rintro ⟨h0, hr⟩
    exact ⟨fun j hj => by rw [← hl j hj]; exact h0 j hj, hr⟩
  · rintro ⟨h0, hr⟩
    exact ⟨fun j hj => (congrArg (· + _) (hl j hj)).trans (h0 j hj), hr⟩

theorem ldLkp_endK : Spec.ldLkp_endK := by
  intro E St M N _ _ B x m
  refine (ldLkp_lev_top E (St × E) M N (B.treeK fun y m => B.more y.1 m) x m).trans
    (and_congr_left fun _ => ?_)
  show Blocks.ext (B.v + 0) (facK (B.key x.1.1 m) x.1.2) x.2.1.pt + ∑ i, x.2.1.mf i * B.ent m i =
      x.2.1.tg ↔
    Blocks.ext B.v (B.key x.1.1 m) x.2.1.pt + ∑ i, - x.2.1.mf i * B.ent m i = x.1.2 - x.2.1.tg
  have hk := key_end E B.v (B.key x.1.1 m) x.2.1.pt x.1.2 (x.2.1.tg - ∑ i, x.2.1.mf i * B.ent m i)
  have hs : ∑ i, - x.2.1.mf i * B.ent m i = - ∑ i, x.2.1.mf i * B.ent m i := by
    simp only [neg_mul, sum_neg_distrib]
  rw [Nat.add_zero, hs]
  constructor
  · intro h
    have := hk.mp (by rw [← h]; ring)
    rw [this]; ring
  · intro h
    have := hk.mpr (by linear_combination h)
    rw [this]; ring

theorem ldLkp_endT : Spec.ldLkp_endT := by
  intro E St M N _ _ B more x m
  refine (ldLkp_lev_top E (St × E) M N (B.treeT more) x m).trans (and_congr_left fun _ => ?_)
  show Blocks.ext (B.d + B.w) (facT B.w (B.tab x.1.1) (B.bit m) x.1.2) x.2.1.pt +
        ∑ i, x.2.1.mf i * B.ent m i = x.2.1.tg ↔
    Blocks.ext (B.d + B.w)
          (fun X => (x.1.2 - 1 - B.tab x.1.1 (X / 2 ^ B.w)) * B.bit m (X / 2 ^ B.w) (X % 2 ^ B.w))
          x.2.1.pt +
        ∑ i, x.2.1.mf i * B.ent m i = x.2.1.tg - 1
  have hk := tab_end E B.d B.w (B.tab x.1.1) (B.bit m) x.2.1.pt x.1.2
    (x.2.1.tg - ∑ i, x.2.1.mf i * B.ent m i)
  constructor
  · intro h
    have := hk.mp (by rw [← h]; ring)
    rw [this]; ring
  · intro h
    have := hk.mpr (by linear_combination h)
    rw [this]; ring

end Cb
