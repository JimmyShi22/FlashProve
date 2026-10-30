-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchWordsProofs.lean: the proofs of the statements of Cb/Ld/LdSwitchWords.lean (the code
switch "with lists", on vectors).

Named tools: `ldAt_pad` (a padded form reads the old part), `cnt_exists_list_le` (the union bound
over a list that is given by a predicate and a bound). Nothing is defined here that a statement
reads.

Main names (statements and hypotheses: Cb/Ld/LdSwitchWords.lean):
  `ldSw_eq_iff`: what the new claim says of a new message: the combination of its gaps with the
    coefficients is 0.
  `ldSw_gap_iff`: what "all gaps are 0" says.
  `ldSw_back`: the backward step: no bad value, u in Lst, the new claim holds of u: then the old
    part of u is a witness of the relaxed old claim.
  `ldSw_complete`: completeness: no exception.
  `cnt_ldSwBad1`: the first error: a list of at most L members, and `W.Zo.OK`: at most (L choose 2)
    · Zo.err seeds at which two different members of Lst have the same answers.
  `cnt_ldSwBad2a`: the second error, first part: at most (|P| - e - 1)^t lists Qs of long positions.
  `cnt_ldSwBad2b`: the second error, second part: a list of at most L members, and `W.Zb.OK`: at
    every Qs at most L · Zb.err seeds ρb.
  `cnt_ldSwBad2`: the second error: under the same two hypotheses, together at most (|P| - e - 1)^t
    · |seeds of Zb| + |P|^t · (L · Zb.err) values of (Qs, ρb).

Limits: see the head of Cb/Ld/LdSwitchWords.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSwitchWords
import Cb.Gen.OodDecProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Cb.Ood

section Tools
variable {E K Qo P Co : Type} [Field E]

theorem ldAt_pad [Fintype K] [Fintype Qo] (f : K → E) (u : K ⊕ Qo → E) :
    ldAt (ldPad (Qo := Qo) f) u = ldAt f (ldOld u) := by
  unfold ldAt ldPad ldOld
  rw [Fintype.sum_sum_type]
  simp

omit [Field E] in
theorem ldOld_new (v : K → E) (ro : Qo → E) : ldOld (ldNew v ro) = v := rfl

/-- The union bound over a list: a predicate with at most L members, each of which spoils at most k
values; then at most L * k values are spoiled by some member. -/
theorem cnt_exists_list_le {U C : Type} [Finite U] [Fintype C] (Lst : U → Prop) (L k : ℕ)
    (hL : ListLE Lst L) (B : U → C → Prop) (hB : ∀ u, Lst u → cnt (B u) ≤ k) :
    cnt (fun c => ∃ u, Lst u ∧ B u c) ≤ L * k := by
  classical
  cases nonempty_fintype U
  have h1 : cnt (fun c => ∃ u, Lst u ∧ B u c) ≤ ∑ u ∈ Finset.univ.filter Lst, cnt (B u) := by
    refine le_trans (cnt_mono fun c hc => ?_) (cnt_exists_mem_le (Finset.univ.filter Lst) B)
    obtain ⟨u, hu, hb⟩ := hc
    exact ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩, hb⟩
  refine h1.trans ((Finset.sum_le_sum fun u hu => hB u (Finset.mem_filter.1 hu).2).trans ?_)
  rw [Finset.sum_const, smul_eq_mul]
  exact Nat.mul_le_mul_right k (hL _ fun u hu => (Finset.mem_filter.1 hu).2)

end Tools

section
variable (E K Qo P Co : Type) [Field E] [Fintype K] [Fintype Qo] [Fintype Co]

theorem ldSw_eq_iff : Spec.ldSw_eq_iff E K Qo P Co := by
  intro W form tgt y ρo ans c u
  have h1 : ldAt (W.form' form ρo c) u = ∑ ν, W.Zb.ze c.2 ν * ldAt (W.rows form ρo c.1 ν) u := by
    unfold ldAt LdSwW.form'
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun n _ => mul_assoc _ _ _
  have h2 : ∑ ν, W.Zb.ze c.2 ν * W.gap form tgt y ρo ans c.1 u ν =
      ldAt (W.form' form ρo c) u - W.tgt' tgt ans y c := by
    rw [h1]
    unfold LdSwW.gap LdSwW.tgt'
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ν _ => mul_sub _ _ _
  rw [h2, sub_eq_zero]

omit [Fintype Co] in
theorem ldSw_gap_iff : Spec.ldSw_gap_iff E K Qo P Co := by
  intro W form tgt y ρo ans Qs u
  constructor
  · intro h
    refine ⟨?_, ?_, fun i => ?_⟩
    · have h1 := congrFun h (Sum.inl ())
      have h2 : ldAt (ldPad (Qo := Qo) form) u - tgt = 0 := h1
      rw [ldAt_pad] at h2
      exact sub_eq_zero.1 h2
    · funext s
      have h1 := congrFun h (Sum.inr (Sum.inl s))
      have h2 : ldAt (W.Zo.mat ρo s) u - ans s = 0 := h1
      exact sub_eq_zero.1 h2
    · funext c
      have h1 := congrFun h (Sum.inr (Sum.inr (i, c)))
      have h2 : ldAt (ldPad (Qo := Qo) (W.G (Qs i) c)) u - y (Qs i) c = 0 := h1
      rw [ldAt_pad] at h2
      exact sub_eq_zero.1 h2
  · rintro ⟨h1, h2, h3⟩
    funext ν
    rcases ν with _ | s | ⟨i, c⟩
    · show ldAt (ldPad (Qo := Qo) form) u - tgt = 0
      rw [ldAt_pad, h1, sub_self]
    · show ldAt (W.Zo.mat ρo s) u - ans s = 0
      rw [← h2]
      exact sub_self _
    · show ldAt (ldPad (Qo := Qo) (W.G (Qs i) c)) u - y (Qs i) c = 0
      rw [ldAt_pad, ← h3 i]
      exact sub_self _

theorem ldSw_back [Finite P] : Spec.ldSw_back E K Qo P Co := by
  intro W Lst e form tgt y ρo ans c u h1 h2 hu heq
  by_contra hn
  have hz := (ldSw_eq_iff E K Qo P Co W form tgt y ρo ans c u).1 heq
  by_cases hg : W.gap form tgt y ρo ans c.1 u = 0
  · exact h2 (Or.inl ⟨h1, u, hu, hg, hn⟩)
  · exact h2 (Or.inr ⟨u, hu, hg, hz⟩)

theorem ldSw_complete : Spec.ldSw_complete E K Qo P Co := by
  intro W form tgt v ro ρo c hv
  rw [ldSw_eq_iff E K Qo P Co W form tgt (ldWord W.G v) ρo _ c (ldNew v ro)]
  have hg : W.gap form tgt (ldWord W.G v) ρo (W.Zo.val ρo (ldNew v ro)) c.1 (ldNew v ro) = 0 :=
    (ldSw_gap_iff E K Qo P Co W form tgt _ ρo _ c.1 _).2 ⟨hv, rfl, fun _ => rfl⟩
  rw [hg]
  simp

end

section
variable (E K Qo P Co : Type)
  [Field E] [Fintype E] [Fintype K] [Fintype Qo] [Fintype P] [Fintype Co]

omit [Fintype E] [Fintype P] [Fintype Co] in
theorem cnt_ldSwBad1 : Spec.cnt_ldSwBad1 E K Qo P Co := fun W Lst L hL hZ =>
  ⟨ood_cnt_clash_sample E _ W.Zo Lst L hL hZ, ood_cnt_clash_sq E _ W.Zo Lst L hL hZ⟩

omit [Fintype Co] in
theorem cnt_ldSwBad2a : Spec.cnt_ldSwBad2a E K Qo P Co := by
  intro W Lst e form tgt y ρo ans
  by_cases hex : ¬ W.Bad1 Lst ρo ∧
    ∃ u, Lst u ∧ W.Zo.val ρo u = ans ∧ ¬ LdNear e y (ldWord W.G (ldOld u))
  · obtain ⟨hc, u₀, hu₀, ha₀, hn₀⟩ := hex
    refine le_trans (cnt_mono fun Qs hQ i => ?_)
      (cnt_miss_le_of_lt (P := fun x => y x ≠ ldWord W.G (ldOld u₀) x) (not_le.1 hn₀) W.t)
    obtain ⟨-, u, hu, hg, -⟩ := hQ
    obtain ⟨-, ha, hw⟩ := (ldSw_gap_iff E K Qo P Co W form tgt y ρo ans Qs u).1 hg
    have huu : u = u₀ := by_contra fun hne => hc ⟨u, u₀, hu, hu₀, hne, ha.trans ha₀.symm⟩
    subst huu
    exact fun hne => hne (hw i).symm
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro Qs ⟨hc, u, hu, hg, hn⟩
      obtain ⟨hf, ha, -⟩ := (ldSw_gap_iff E K Qo P Co W form tgt y ρo ans Qs u).1 hg
      exact hex ⟨hc, u, hu, ha, fun hnear => hn ⟨hnear, hf⟩⟩

omit [Fintype P] in
theorem cnt_ldSwBad2b : Spec.cnt_ldSwBad2b E K Qo P Co := by
  intro W Lst L form tgt y ρo ans Qs hL hZ
  classical
  refine cnt_exists_list_le Lst L W.Zb.err hL
    (fun u ρb =>
      W.gap form tgt y ρo ans Qs u ≠ 0 ∧ ∑ ν, W.Zb.ze ρb ν * W.gap form tgt y ρo ans Qs u ν = 0)
    fun u _ => ?_
  by_cases hg : W.gap form tgt y ρo ans Qs u = 0
  · rw [cnt_false fun _ h => h.1 hg]
    exact Nat.zero_le _
  · exact (cnt_mono fun _ h => h.2).trans (hZ _ hg)

theorem cnt_ldSwBad2 : Spec.cnt_ldSwBad2 E K Qo P Co := by
  intro W Lst e L form tgt y ρo ans hL hZ
  have h := cnt_two_rounds_le (W.Bad2 Lst e form tgt y ρo ans) (W.Bad2a Lst e form tgt y ρo ans) _ _
    (cnt_ldSwBad2a E K Qo P Co W Lst e form tgt y ρo ans) (fun Qs hQ =>
      (cnt_mono fun ρb hb => hb.resolve_left hQ).trans
        (cnt_ldSwBad2b E K Qo P Co W Lst L form tgt y ρo ans Qs hL hZ))
  unfold LdSwW.err2
  rwa [Fintype.card_fun, Fintype.card_fin] at h

end
end Cb
