-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandVProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseDemandV.lean
(what the tests of a closing need of the oracle messages in a batch).
Nothing is defined here that a statement reads.
-/
import Cb.Ld.LdLinCloseDemandV

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldDemandV_her : Spec.ldDemandV_her := by
  intro E S E₀ N sh q₀ b h0 J J' hJ Us ⟨h1, h2, h3⟩
  exact ⟨h0 J J' hJ _ h1,
    fun o ho j => h2 o ho ⟨j.1, hJ j.2⟩,
    fun o ho => (cnt_mono fun x ⟨j, hj⟩ => ⟨⟨j.1, hJ j.2⟩, hj⟩).trans (h3 o ho)⟩

theorem ldDemandV_empty : Spec.ldDemandV_empty := by
  intro E S E₀ N sh q₀ b h0 J
  refine ⟨h0 J, fun o _ j => ?_, fun o _ => ?_⟩
  · rw [cnt_false fun x hx => absurd hx (Finset.notMem_empty _)]
    exact Nat.zero_le _
  · rw [cnt_false fun x ⟨_, hx⟩ => absurd hx (Finset.notMem_empty _)]
    exact Nat.zero_le _

open Classical in
theorem ldDemandV_need : Spec.ldDemandV_need := by
  intro E _ _ S D St₀ Wp E₀ A₀ d d' hD ρ U
  have h := (ldChain_link E S D St₀ Wp E₀ A₀ d d'
    (fun V =>
      ∃ U' : Finset (LdBrE D.G D.kp E₀).Pos,
        U'.toLeft.card ≤ D.t ∧ U'.toRight = U ∧ V = U'.biUnion (ldBrG D.G D.kp E₀).src)
    (fun U₁ => U₁ = U) hD fun U' hU' => ⟨U', hU'.1, hU'.2, rfl⟩).2
  exact (h.bears ρ U rfl).2

/-- one slot: the count at an oracle message -/
theorem ldBrG_cnt {E : Type} {S : Sig E} (G : Grp S) (kp : S.O → Prop) [DecidablePred kp]
    (E₀ : ExtSpec) (inst : DecidableEq (E₀.prod S.ext).Pos) (U : Finset (LdBrE G kp E₀).Pos) (t : ℕ)
    (hU : U.toLeft.card ≤ t) (o : S.O) (b' : (S.sub kp).O → ℕ)
    (hb : ∀ h : kp o,
      cnt (fun x : (S.om o).P => (Sum.inr ⟨⟨o, h⟩, x⟩ : (E₀.prod (S.sub kp).ext).Pos) ∈ U.toRight) ≤
        b' ⟨o, h⟩) :
    cnt (fun x : (S.om o).P =>
        (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈ @Finset.biUnion _ _ inst U (ldBrG G kp E₀).src) ≤
      (if G.mem o then t else 0) + (if h : kp o then b' ⟨o, h⟩ else 0) := by
  classical
  refine (cnt_le_add (ldBrG_mem_inr G kp E₀ inst U o)).trans (Nat.add_le_add ?_ ?_)
  · by_cases h : G.mem o
    · rw [if_pos h, cnt_eq_card_filter]
      refine le_trans
        (le_trans (Finset.card_le_card (t := U.toLeft.image (G.pos ⟨o, h⟩)) fun x hx => ?_)
          Finset.card_image_le) hU
      obtain ⟨_, z, hz, hzx⟩ := (Finset.mem_filter.1 hx).2
      exact Finset.mem_image.2 ⟨z, hz, hzx⟩
    · rw [if_neg h, cnt_false fun x hx => h hx.1]
  · by_cases h : kp o
    · rw [dif_pos h]
      exact (cnt_mono fun x hx => hx.2).trans (hb h)
    · rw [dif_neg h, cnt_false fun x hx => h hx.1]

theorem ldDemandV_shared : Spec.ldDemandV_shared := by
  classical
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N sh q₀ b' hD J ρ Us ⟨h0, hown, hsh⟩
  choose U' hc hr he
    using fun j : J => ldDemandV_need E S D St₀ Wp E₀ A₀ d d' hD (ρ.slot j.1) (Us j)
  refine ⟨?_, fun o ho j => ?_, fun o ho => ?_⟩
  · have e : (fun j : J => ((D.link A₀ d d').R.need (ρ.slot j.1) (Us j)).toLeft) =
        fun j : J => (Us j).toLeft :=
      funext fun j => by rw [he j, ldBrG_toLeft, hr j]
    rw [e]
    exact h0
  · beta_reduce
    rw [he j]
    exact ldBrG_cnt D.G D.kp E₀ _ (U' j) D.t (hc j) o b' fun h => by
      rw [hr j]; exact hown ⟨o, h⟩ ho j
  · by_cases hJ : Nonempty J
    · obtain ⟨j0⟩ := hJ
      haveI : Nonempty J := ⟨j0⟩
      obtain ⟨U2, hc2, hr2, he2⟩ :=
        ldDemandV_need E S D St₀ Wp E₀ A₀ d d' hD (ρ.slot j0.1)
          (@Finset.biUnion J _ (fun a b => Classical.propDecidable (a = b)) Finset.univ Us)
      rw [need_union _ _ _ _ (D.link A₀ d d').R (ρ.slot j0.1) J Us] at he2
      refine (cnt_mono fun x ⟨j, hj⟩ => ?_).trans
        (ldBrG_cnt D.G D.kp E₀ (fun a b => Classical.propDecidable (a = b))
          U2 D.t hc2 o b' fun h => ?_)
      · rw [hr2]
        refine (cnt_mono fun x hx => ?_).trans (hsh ⟨o, h⟩ ho)
        obtain ⟨j, _, hj⟩ := (ldDemand_mem_biUnion _).1 hx
        exact ⟨j, hj⟩
      · have hx1 : (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈
            @Finset.biUnion J _ (fun a b => Classical.propDecidable (a = b)) Finset.univ
              (fun j : J => (D.link A₀ d d').R.need (ρ.slot j0.1) (Us j)) := by
          refine (ldDemand_mem_biUnion _).2 ⟨j, Finset.mem_univ _, ?_⟩
          rw [BatchSeqZk.slot_eq ρ j0.1, ← BatchSeqZk.slot_eq ρ j.1]
          exact hj
        rw [he2] at hx1
        exact (ldDemand_mem_biUnion _).2 ((ldDemand_mem_biUnion _).1 hx1)
    · rw [cnt_false fun x ⟨j, _⟩ => hJ ⟨j⟩]
      exact Nat.zero_le _

theorem ldDemandV_local : Spec.ldDemandV_local := by
  classical
  intro E _ _ S D St₀ Wp E₀ A₀ d d' N sh _ q₀ b' A hD J ρ Us ⟨h0, hown, hsh⟩
  choose U' hc hr he
    using fun j : J => ldDemandV_need E S D St₀ Wp E₀ A₀ d d' hD (ρ.slot j.1) (Us j)
  refine ⟨?_, fun o ho j => ?_, fun o ho => ?_⟩
  · have e : (fun j : J => ((D.link A₀ d d').R.need (ρ.slot j.1) (Us j)).toLeft) =
        fun j : J => (Us j).toLeft :=
      funext fun j => by rw [he j, ldBrG_toLeft, hr j]
    rw [e]
    exact h0
  · beta_reduce
    rw [he j]
    refine le_trans
      (ldBrG_cnt D.G D.kp E₀ _ (U' j) D.t (hc j) o b' fun h => by rw [hr j]; exact hown ⟨o, h⟩ ho j)
      (le_of_eq ?_)
    unfold LdRunD.needV
    rw [if_neg ho]
  · unfold LdRunD.needV
    rw [if_pos ho]
    have hsplit : ∀ x : (S.om o).P,
        (∃ j : J,
          (Sum.inr ⟨o, x⟩ : (E₀.prod S.ext).Pos) ∈ (D.link A₀ d d').R.need (ρ.slot j.1) (Us j)) →
        (∃ h : D.G.mem o,
          ∃ z ∈ Finset.univ.biUnion (fun j : J => (U' j).toLeft), D.G.pos ⟨o, h⟩ z = x) ∨
        ∃ h : D.kp o, ∃ j : J, (Sum.inr ⟨⟨o, h⟩, x⟩ : (E₀.prod (S.sub D.kp).ext).Pos) ∈ Us j := by
      rintro x ⟨j, hj⟩
      rw [he j] at hj
      rcases ldBrG_mem_inr D.G D.kp E₀ _ (U' j) o x hj with ⟨h, z, hz, hzx⟩ | ⟨h, hx⟩
      · exact Or.inl ⟨h, z, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hz⟩, hzx⟩
      · exact Or.inr ⟨h, j, by rw [← hr j]; exact hx⟩
    refine (cnt_le_add hsplit).trans (Nat.add_le_add ?_ ?_)
    · by_cases h : D.G.mem o
      · rw [if_pos h, cnt_eq_card_filter]
        have hcard : (Finset.univ.biUnion fun j : J => (U' j).toLeft).card ≤ N * D.t := by
          refine Finset.card_biUnion_le.trans
            ((Finset.sum_le_card_nsmul _ _ D.t fun j _ => hc j).trans ?_)
          rw [smul_eq_mul, Finset.card_univ, Fintype.card_coe]
          exact Nat.mul_le_mul_right _ ((Finset.card_le_univ J).trans (Fintype.card_fin N).le)
        refine le_trans
          (le_trans (Finset.card_le_card
              (t := (Finset.univ.biUnion fun j : J => (U' j).toLeft).image (D.G.pos ⟨o, h⟩))
              fun x hx => ?_)
            Finset.card_image_le) hcard
        obtain ⟨_, z, hz, hzx⟩ := (Finset.mem_filter.1 hx).2
        exact Finset.mem_image.2 ⟨z, hz, hzx⟩
      · rw [if_neg h, cnt_false fun x hx => h hx.1]
    · by_cases h : D.kp o
      · rw [dif_pos h]
        exact (cnt_mono fun x hx => hx.2).trans (hsh ⟨o, h⟩ ho)
      · rw [dif_neg h, cnt_false fun x hx => h hx.1]

open Classical in
/-- what a step without rounds needs: the sources -/
theorem need_pure {X X' : Type} {Ei Eo : ExtSpec} (f : X → Option X') (g : ExtMap Ei Eo)
    (ρ : Rho (IOR.pure f g).shape) (U : Finset Eo.Pos) :
    (IOR.pure f g).need ρ U = U.biUnion g.src := by
  ext q
  simp [IOR.need, IOR.given, IOR.pure]

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Fintype ι] [Nonempty ι] in
theorem ldDemandV_step : Spec.ldDemandV_step E ι κ J Y := by
  classical
  intro C Stq Bq fq Sn qa N q₀ ba b A hqa hA hW hU hO Jn ρ Us ⟨h0, hown, hsh⟩
  have e : (fun j : Jn => (C.link fq Bq).R.need (ρ.slot j.1) (Us j)) =
      fun j : Jn => (Us j).biUnion C.toE.src :=
    funext fun j => need_pure _ _ _ _
  show C.P.qv5 Sn qa N Jn fun j : Jn => (C.link fq Bq).R.need (ρ.slot j.1) (Us j)
  rw [e]
  refine ⟨⟨⟨fun j => hqa _ ⟨?_, fun a => ?_⟩, fun j a => ?_⟩, fun a => ?_⟩, fun a => ?_⟩
  · have e2 : ((Us j).biUnion C.toE.src).toLeft.toLeft.toLeft.toLeft = (Us j).toLeft := by
      ext p
      rw [Finset.mem_toLeft, Finset.mem_toLeft, Finset.mem_toLeft,
        Finset.mem_toLeft, Finset.mem_toLeft]
      exact C.mem_toE (Us j) (.inl p)
    rw [e2]
    exact h0 j
  · refine ((cnt_mono fun x hx => ?_).trans
      (hown (.inl (.inl (.inl a))) (fun h => h) j)).trans (hA a)
    exact (C.mem_toE (Us j) (.inr ⟨.inl (.inl (.inl a)), x⟩)).1
      (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 hx)))
  · refine ((cnt_mono fun x hx => ?_).trans
      (hown (.inl (.inl (.inr a))) (fun h => h) j)).trans (hW a)
    exact (C.mem_toE (Us j) (.inr ⟨.inl (.inl (.inr a)), x⟩)).1
      (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 hx))
  · refine ((cnt_mono fun x ⟨j, hx⟩ => ⟨j, ?_⟩).trans (hsh (.inl (.inr a)) trivial)).trans (hU a)
    exact (C.mem_toE (Us j) (.inr ⟨.inl (.inr a), x⟩)).1 (Finset.mem_toLeft.1 hx)
  · refine ((cnt_mono fun x ⟨j, hx⟩ => ⟨j, ?_⟩).trans (hsh (.inr a) trivial)).trans (hO a)
    exact (C.mem_toE (Us j) (.inr ⟨.inr a, x⟩)).1 hx

omit [Fintype ι] [Nonempty ι] in
theorem ldDemandV_plan : Spec.ldDemandV_plan E ι κ J Y := by
  intro C p T N b' o c hS hc
  have hmem : p.G₁.mem o → C.isSh o := by
    intro h
    rcases hS o h with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> trivial
  have h2 : (if h : p.kp₁ o then T.D₂.needV N (fun a => C.isSh a.1) b' ⟨o, h⟩ else 0) ≤
      (if C.isSh o then N * T.t₂ else T.t₂) + c := by
    by_cases hk : p.kp₁ o
    · rw [dif_pos hk]
      refine Nat.add_le_add ?_ ?_
      · by_cases hm : p.G₂.mem ⟨o, hk⟩
        · exact le_of_eq (if_pos hm)
        · exact le_trans (le_of_eq (if_neg hm)) (Nat.zero_le _)
      · by_cases hk2 : p.kp₂ ⟨o, hk⟩
        · exact le_trans (le_of_eq (dif_pos hk2)) (hc hk hk2)
        · exact le_trans (le_of_eq (dif_neg hk2)) (Nat.zero_le _)
    · rw [dif_neg hk]
      exact Nat.zero_le _
  show (if p.G₁.mem o then T.t₁ else 0) +
      (if h : p.kp₁ o then T.D₂.needV N (fun a => C.isSh a.1) b' ⟨o, h⟩ else 0) ≤ _
  by_cases hs : C.isSh o
  · rw [if_pos hs] at h2 ⊢
    have h1 : (if p.G₁.mem o then T.t₁ else 0) ≤ T.t₁ := by
      by_cases hm : p.G₁.mem o
      · rw [if_pos hm]
      · rw [if_neg hm]
        exact Nat.zero_le _
    calc _ ≤ T.t₁ + (N * T.t₂ + c) := Nat.add_le_add h1 h2
      _ = T.t₁ + N * T.t₂ + c := (Nat.add_assoc _ _ _).symm
  · rw [if_neg hs] at h2 ⊢
    rw [if_neg fun hm => hs (hmem hm), Nat.zero_add]
    exact h2

omit [Fintype ι] [Nonempty ι] in
theorem ldDemandV_plan_first : Spec.ldDemandV_plan_first E ι κ J Y := by
  intro C p T N b' o c hm hc
  refine (ldDemand_le E C.S T.D₁ _ o).trans (Nat.add_le_add_left ?_ _)
  by_cases hk : p.kp₁ o
  · rw [dif_pos hk]
    show (if p.G₂.mem ⟨o, hk⟩ then _ else 0) + (if h : p.kp₂ ⟨o, hk⟩ then b' ⟨⟨o, hk⟩, h⟩ else 0) ≤
      c
    rw [if_neg (hm hk), Nat.zero_add]
    by_cases hk2 : p.kp₂ ⟨o, hk⟩
    · rw [dif_pos hk2]
      exact hc hk hk2
    · rw [dif_neg hk2]
      exact Nat.zero_le _
  · rw [dif_neg hk]
    exact Nat.zero_le _

end
end Cb
