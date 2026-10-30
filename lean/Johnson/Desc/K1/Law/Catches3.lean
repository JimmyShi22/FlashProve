-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Catches3.lean: the left side of the sample row of answer i is answer i of the
message's sample map; the count of seeds.

Main names: Msg.vec, eqW_pointOf, part_sum, val_eq; catchesLaw.

What is not claimed. The count names no verifier. It is a count for one vector; lists and the seeds
that several messages share are in Joined.lean and Fair.lean. Nothing on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.Catches2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Cb Cb.Ood Prob

/-- A message's two tables as a vector of the sample map. -/
def Msg.vec (m : Msg) (u : Part → Nat → GE) : m.J₀ ⊕ Fin m.answers × Fin m.e → GE :=
  Sum.elim (Sum.elim (fun j => u .main j.1) fun j => u .mask j.1)
    fun n => u m.padPart (m.padIdx n.1.val n.2.val)

theorem eqW_pointOf {v : Nat} (z : Fin v → GE) (n : Nat) :
    eqW v (pointOf z) n = Alg.eqk z fun t : Fin v => n.testBit t.val := by
  unfold eqW
  congr 1
  funext t
  simp [pointOf, t.isLt]

/-- One table's part of a row's left side: the entries proper, and the pads if they lie here. -/
theorem Msg.part_sum (m : Msg) (hne : (m.K != 0 || m.Kzk != 0) = true) (hf : m.padFits = true)
    (z : Nat → GE) (β : GE) (i : Fin m.answers) (u : Part → Nat → GE) (part : Part) :
    ∑ j ∈ Finset.range (m.size part), m.weight z β i.val part j * u part j =
      ∑ j ∈ m.proper part, eqW m.v z (m.vertex part j) * u part j +
        if part = m.padPart then
          ∑ n : Fin m.answers × Fin m.e, (if n.1 = i then β * readE (thetaE n.2.val) else 0) *
            u part (m.padIdx n.1.val n.2.val)
        else 0 := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m.size part))
    fun j => m.isPad part j = false]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have h := (m.mem_proper part j).1 hj
    rw [m.weight_proper z β i.val part j h.2.2, if_pos h.1]
  · by_cases hp : part = m.padPart
    · subst hp
      rw [if_pos rfl]
      symm
      refine Finset.sum_nbij (fun n => m.padIdx n.1.val n.2.val) ?_ ?_ ?_ ?_
      · intro n _
        simp only [Finset.mem_filter, Finset.mem_range, Bool.not_eq_false]
        exact ⟨m.padIdx_lt_size hne hf _ _ n.1.isLt n.2.isLt,
          (m.isPad_iff _ _).2 ⟨rfl, _, _, n.1.isLt, n.2.isLt, rfl⟩⟩
      · intro n _ n' _ h
        obtain ⟨h1, h2⟩ := m.padIdx_inj n.2.isLt n'.2.isLt h
        exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      · intro j hj
        simp only [Finset.coe_filter, Finset.mem_range, Bool.not_eq_false, Set.mem_setOf_eq] at hj
        obtain ⟨_, k, t, hk, ht, rfl⟩ := (m.isPad_iff _ _).1 hj.2
        exact ⟨(⟨k, hk⟩, ⟨t, ht⟩), by simp, rfl⟩
      · intro n _
        rw [m.weight_pad z β i.val _ _ n.1.isLt n.2.isLt]
        simp only [Fin.ext_iff]
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_filter, Bool.not_eq_false] at hj
      exact absurd ((m.isPad_iff _ _).1 hj.2).1 hp

/-- **The left side of the row of answer i is answer i of the sample map.** -/
theorem Msg.val_eq (m : Msg) (hne : (m.K != 0 || m.Kzk != 0) = true) (hf : m.padFits = true)
    (ρ : Fin m.answers → (Fin m.v → GE) × GEˣ) (u : Part → Nat → GE) (i : Fin m.answers) :
    m.Z.val ρ (m.vec u) i = m.form (pointOf (ρ i).1) ((ρ i).2 : GE) i.val u := by
  have h1 := m.part_sum hne hf (pointOf (ρ i).1) ((ρ i).2 : GE) i u .main
  have h2 := m.part_sum hne hf (pointOf (ρ i).1) ((ρ i).2 : GE) i u .mask
  show ∑ x, m.Z.mat ρ i x * m.vec u x = _
  unfold Msg.form
  rw [show (if m.has .main then 2 ^ m.bits .main else 0) = m.size .main from rfl,
    show (if m.has .mask then 2 ^ m.bits .mask else 0) = m.size .mask from rfl, h1, h2,
    Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← Finset.sum_coe_sort (m.proper .main), ← Finset.sum_coe_sort (m.proper .mask)]
  simp only [eqW_pointOf]
  have e1 : ∑ j : {j // j ∈ m.proper .main}, m.Z.mat ρ i (Sum.inl (Sum.inl j)) *
      m.vec u (Sum.inl (Sum.inl j)) = ∑ j : {j // j ∈ m.proper .main},
        (Alg.eqk (ρ i).1 fun t : Fin m.v => (m.vertex .main j.1).testBit t.val) * u .main j.1 := rfl
  have e2 : ∑ j : {j // j ∈ m.proper .mask}, m.Z.mat ρ i (Sum.inl (Sum.inr j)) *
      m.vec u (Sum.inl (Sum.inr j)) = ∑ j : {j // j ∈ m.proper .mask},
        (Alg.eqk (ρ i).1 fun t : Fin m.v => (m.vertex .mask j.1).testBit t.val) * u .mask j.1 := rfl
  have e3 : ∑ n : Fin m.answers × Fin m.e, m.Z.mat ρ i (Sum.inr n) * m.vec u (Sum.inr n) =
      ∑ n : Fin m.answers × Fin m.e,
        (if n.1 = i then ((ρ i).2 : GE) * readE (thetaE n.2.val) else 0) *
          u m.padPart (m.padIdx n.1.val n.2.val) := rfl
  rw [e1, e2, e3]
  cases hp : m.padPart <;> simp <;> ring

/-- **CATCHES.** -/
theorem catchesLaw : CatchesLaw := by
  intro m u hf hne hu hF
  obtain ⟨part, j, hp, hj, hu⟩ := hu
  have hv : m.vec u ≠ 0 := by
    intro h0
    apply hu
    cases hpad : m.isPad part j
    · cases part
      · exact congrFun h0 (Sum.inl (Sum.inl ⟨j, (m.mem_proper _ _).2 ⟨hp, hj, hpad⟩⟩))
      · exact congrFun h0 (Sum.inl (Sum.inr ⟨j, (m.mem_proper _ _).2 ⟨hp, hj, hpad⟩⟩))
    · obtain ⟨rfl, k, t, hk, ht, rfl⟩ := (m.isPad_iff _ _).1 hpad
      exact congrFun h0 (Sum.inr (⟨k, hk⟩, ⟨t, ht⟩))
  have hc : cnt (fun ρ : m.Z.D => m.Z.val ρ (m.vec u) = 0) ≤ m.Z.err := by
    rcases m.e_cases with he | he
    · exact m.Z_okOn_E he _ (fun n => ⟨_, rfl⟩) hv
    · exact m.Z_okOn_F he _ (fun n => hF he (n.1.val, m.padIdx n.1.val n.2.val, n.2.val)
        ((m.mem_pads _).2 ⟨_, _, n.1.isLt, n.2.isLt, rfl⟩)) hv
  have e : (fun ρ : Fin m.answers → (Fin m.v → GE) × GEˣ =>
      ∀ i : Fin m.answers, m.form (pointOf (ρ i).1) ((ρ i).2 : GE) i.val u = 0) =
      fun ρ : m.Z.D => m.Z.val ρ (m.vec u) = 0 := by
    funext ρ
    refine propext ⟨fun h => funext fun i => ?_, fun h i => ?_⟩
    · rw [m.val_eq hne hf]
      exact h i
    · rw [← m.val_eq hne hf]
      exact congrFun h i
  rw [e]
  simpa using hc

end VerifiableInference.Desc.K1
