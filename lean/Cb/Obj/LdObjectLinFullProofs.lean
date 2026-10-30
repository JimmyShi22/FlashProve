-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinFullProofs.lean: the proofs of the statements of Cb/Obj/LdObjectLinFull.lean.

Main names: `ldOLF_items`, `ldOLF_lin`: see their statements in Cb/Obj/LdObjectLinFull.lean.
The step in front of the test is read off the definitions (the two first joints say the same, up to
a Unit in oracles and witness); a piece, then a tail, is a tail (Cb/Ld/LdTowerKit.lean); the test
with its closing is a tail (Cb/Ld/LdLinCloseLinProofs.lean); the four bridging facts are those of
Cb/Obj/LdObjectLinProofs.lean, as they stand; the lists come from the generic rule
(Cb/Obj/LdObjectTail.lean). Nothing is defined here that a statement reads.
-/
import Cb.Obj.LdObjectLinFull
import Cb.Ld.LdLinCloseLinProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] [Fintype E] in
theorem ldOLF_enter : Spec.ldOLF_enter F E := by
  classical
  intro O qa
  refine pieceTr_pure Unit O.P.X0 O.toC.P.X0 O.P.E0 O.toC.P.E0 O.P.W0 O.toC.P.W0 (O.P.j0 O.on0)
    (O.toC.P.j0 O.on0) some O.enG (fun a => (a.1, (a.2.1, (a.2.2, ())))) (fun _ w => (w.1, w.2.1))
    (O.P.q0 (O.qaIn qa)) (O.toC.P.q0 qa)
    { isLocal := ?_
      acc := fun x y w h => ⟨rfl, h⟩
      onOut := ?_
      keeps := fun _ _ => rfl
      know := ?_ } ?_
  · intro y y' q h
    rcases q with p | p | p
    · exact congrArg _ (Sum.inl.inj (h (Sum.inl p) (Finset.mem_singleton_self _)))
    · exact p.elim
    · exact congrArg (fun s => Sum.inr (Sum.inr s))
        (Sum.inr.inj (h (Sum.inr p) (Finset.mem_singleton_self _)))
  · intro x y x' h hx
    obtain rfl := Option.some.inj hx
    exact ⟨h.1, h.2, trivial⟩
  · intro x y x' w' _ hx h
    obtain rfl := Option.some.inj hx
    exact h
  · intro U hU
    refine ⟨le_trans (Finset.card_le_card ?_) hU.1, ?_⟩
    · intro p hp
      obtain ⟨u, hu, hpu⟩ := (ldLkC_mem_biUnion _).1 (Finset.mem_toLeft.1 hp)
      rcases u with u | u | u
      · rw [Sum.inl.inj (Finset.mem_singleton.1 hpu)]
        exact Finset.mem_toLeft.2 hu
      · exact u.elim
      · exact absurd (Finset.mem_singleton.1 hpu) (by simp)
    · refine (congrArg qa ?_).mpr hU.2
      ext p
      rw [Finset.mem_map, Finset.mem_toRight]
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨u, hu, hru⟩ := (ldLkC_mem_biUnion _).1 (Finset.mem_toRight.1 hr)
        rcases u with u | u | u
        · exact absurd (Finset.mem_singleton.1 hru) (by simp)
        · exact u.elim
        · rw [Sum.inr.inj (Finset.mem_singleton.1 hru)]
          exact hu
      · intro hp
        rcases p with p | p
        · exact p.elim
        · exact ⟨p, Finset.mem_toRight.2
              ((ldLkC_mem_biUnion _).2 ⟨Sum.inr (Sum.inr p), hp, Finset.mem_singleton_self _⟩),
            rfl⟩

omit [Fintype F] [Fintype E] in
theorem ldOLF_sub : Spec.ldOLF_sub F E := fun _ _ h _ _ hVU hU =>
  h _ _ (Finset.map_subset_map.2 hVU) hU

theorem ldOLF_tail : Spec.ldOLF_tail F E := by
  intro O _ εf Sn qa Qt fq d d₀ hF hpy hS hSays hQ hq
  exact tailTr_cons Unit _ _ _ _ _ O.enter (O.lkC Sn εf Qt fq d).R _ _ _ O.hEnter
    (O.lkC Sn εf Qt fq d).H _ _ _ _ _ d₀ _ _ _ _ (ldOLF_enter F E O qa)
    (ldLinCl_tail _ _ _ _ _ O.toC O.on0 εf Sn qa d Qt fq hF hpy hS hSays hQ hq)

omit [Fintype F] [Fintype E] in
theorem ldOLF_qFam : Spec.ldOLF_qFam F E := by
  intro O q₀ b U h0
  have e1 : ∀ V : Finset O.P.Ea.Pos,
      (V.map ⟨(Sum.inr : O.S.ext.Pos → (extNone.prod O.S.ext).Pos), Sum.inr_injective⟩).toLeft =
        ∅ := by
    intro V
    ext p
    exact p.elim
  have e2 : ∀ (a : O.S.O) (x : (O.S.om a).P),
      ((Sum.inr ⟨a, x⟩ : (extNone.prod O.S.ext).Pos) ∈
        U.toRight.map ⟨(Sum.inr : O.S.ext.Pos → (extNone.prod O.S.ext).Pos), Sum.inr_injective⟩) ↔
      (Sum.inr ⟨a, x⟩ : O.P.E0.Pos) ∈ U := by
    intro a x
    rw [Finset.mem_map]
    constructor
    · rintro ⟨r, hr, he⟩
      rw [← Sum.inr.inj he]
      exact Finset.mem_toRight.1 hr
    · exact fun h => ⟨⟨a, x⟩, Finset.mem_toRight.2 h, rfl⟩
  constructor
  · rintro ⟨h1, -, h2⟩
    refine ⟨h1, fun a => ?_⟩
    have h := h2 a
    simp only [e2] at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_, fun a => ?_⟩
    · show q₀ _
      rw [e1]
      exact h0
    · simp only [e2]
      exact h2 a

theorem ldOLF_tailF : Spec.ldOLF_tailF F E := by
  intro O _ εf Sn q₀ b Qt fq d d₀ h0 hF hpy hS hSays hQ hq
  exact tailTr_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldOLF_tail F E O εf Sn _ Qt fq d d₀ hF hpy hS hSays hQ hq)
    fun U hU => (ldOLF_qFam F E O q₀ b U h0).1 hU

theorem ldOLF_items :
    Spec.ldOLF_items F E := fun O _ εf Sn qa Qt fq d d0 hd he hF hpy hS hSays hQ hq =>
  ldObj_lin O.Cf.conf O.left O.P.W0 (O.full Sn εf Qt fq d) (O.hFull0 Sn εf Qt fq d) (O.P.j0 O.on0)
    (O.extF Sn εf Qt fq d (fun _ _ => 0, fun _ => (fun _ => 0, fun _ => 0)))
    (O.numsF0 Sn εf Qt fq d) (O.P.q0 (O.qaIn qa)) O.t O.fi (fun w => O.S.msgs w.2) d0
    (ldOLF_tail F E O εf Sn qa Qt fq d _ hF hpy hS hSays hQ hq) (ldOL_rel F E O)
    (fun a => (ldOL_on F E O a).1) (fun a w _ => ldOL_relR F E O hd he a w)
    (ldOL_reads F E O (O.qaIn qa))

theorem ldOLF_lin :
    Spec.ldOLF_lin F E := fun O _ bad L Sn qa Qt fq d d0 hd hdX he he' hm hL hpy hS hSays hQ hq =>
  ldOLF_items F E O _ Sn qa Qt fq d d0 hd he
    (ldLin_foldErr O.toC.P O.Cf.C₀.d bad L hdX he he' hm hL) hpy hS hSays hQ hq

end
end Cb
