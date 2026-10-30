-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFreshManyProofs.lean: the proofs of the statements of Cb/Ld/LdSendFreshMany.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
-/
import Cb.Ld.LdSendFreshMany
import Cb.Ld.LdSendFreshProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- for an injective `at'`: to overwrite at the same places twice is to overwrite once -/
theorem extend_extend {I J V : Type} {at' : I → J} (hi : Function.Injective at')
    (a b : I → V) (k : J → V) :
    Function.extend at' a (Function.extend at' b k) = Function.extend at' a k := by
  funext j
  by_cases h : ∃ i, at' i = j
  · obtain ⟨i, rfl⟩ := h
    exact (hi.extend_apply _ _ _).trans (hi.extend_apply _ _ _).symm
  · exact (Function.extend_apply' _ _ _ h).trans
      ((Function.extend_apply' _ _ _ h).trans (Function.extend_apply' _ _ _ h).symm)

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type} {D : N.Sender W W'} (L : D.Layout)

/-- all blocks' masks, from those of b and the others -/
def Sig.Sender.Layout.glue (b : L.Bk) (M : L.Mk b) (r : L.Oth b) : ∀ j, L.Mk j :=
  (Equiv.piSplitAt b L.Mk).symm (M, r)

omit [Field E] in
theorem Sig.Sender.Layout.glue_self (b : L.Bk) (M : L.Mk b) (r : L.Oth b) : L.glue b M r b = M := by
  simp [Sig.Sender.Layout.glue, Equiv.piSplitAt]

omit [Field E] in
theorem Sig.Sender.Layout.glue_oth (b : L.Bk) (M : L.Mk b) (r : L.Oth b) :
    L.oth b (L.glue b M r) = r := by
  funext j
  simp [Sig.Sender.Layout.glue, Sig.Sender.Layout.oth, Equiv.piSplitAt, j.2]

omit [Field E] in
theorem Sig.Sender.Layout.own_mk (b : L.Bk) (M : L.Mk b) (k₀ : L.Oth b × L.F0) (η : L.Pd) :
    (L.own b).mk' M k₀ η = L.mk' (L.glue b M k₀.1) k₀.2 η := rfl

end

section
variable (E : Type) [Field E]

theorem layout_laws : Spec.layout_laws E := by
  intro N W W' D L Sd b Kc rd put hP hover hb
  obtain ⟨body, hb⟩ := hb
  refine ⟨hover, ⟨body, fun w M k₀ η => ?_⟩, fun s w w' M M' k₀ k₀' => ?_⟩
  · rw [L.own_mk, hb, L.glue_self, L.glue_oth]
    rfl
  · simp only [L.own_mk]
    exact hP s w w' _ _ _ _

theorem layout_laws_entries : Spec.layout_laws_entries E := by
  classical
  intro N W W' D L Sd b J I g Rd at' val hP hi hRd hown hoff
  refine layout_laws E N W W' D L Sd b (J → E) _ _ hP (fun M M' k => extend_extend hi _ _ k)
    ⟨fun w r =>
        cutTo Rd (g (D.upM
              (D.put w (L.mk' (L.glue b (Classical.arbitrary _) r.1) r.2 (Classical.arbitrary _))))
            (D.rest w)),
      fun w ms f η => ?_⟩
  funext j
  by_cases h : ∃ i, at' i = j
  · obtain ⟨i, rfl⟩ := h
    rw [hi.extend_apply]
    exact (if_pos (hRd i)).trans (hown w ms f η i)
  · rw [Function.extend_apply' _ _ _ h]
    by_cases hj : Rd j
    · refine (if_pos hj).trans (Eq.trans ?_ (if_pos hj).symm)
      exact hoff w ms _ f η _ j (L.glue_oth b _ _).symm hj fun i e => h ⟨i, e.symm⟩
    · exact (if_neg hj).trans (if_neg hj).symm

theorem layout_fresh : Spec.layout_fresh E := fun N Sd X W W' E₀ D t Ri L hZ b Kc rd put hU =>
  ldSendFam_fresh E N Sd X W W' E₀ D t Ri (L.Mk b) (L.own b) Kc rd put hU hZ

theorem ldSendSig_fresh_wide : Spec.ldSendSig_fresh_wide E := by
  intro S N Sd St Wp Wp' E₀ D t Ri Mb _ _ U Kc rd put hU hZ
  exact fresh_post _ _ _ _ _ _ _ _ _ _ (ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D) Ri _
    (S.mergeX N St) (S.mergeE N E₀) (S.mergeW N St Wp') Kc Kc (fun v => rd (N.msgs v.1) v.2)
    (fun v => rd (N.msgs (S.right N (T := OMsg.Wit) v.1)) (S.left N (T := OMsg.Wit) v.1, v.2))
    (fun a => ((a.1.1.1, S.join N (T := OMsg.Smp) a.1.1.2 a.1.2), a.2)) Mb put put
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (ldSendFam_fresh E N Sd (St × S.Smp) (S.Wit × Wp) (S.Wit × Wp') (E₀.prod S.ext)
      D t Ri Mb U Kc rd put hU hZ)

theorem own_laws_keep : Spec.own_laws_keep E := by
  intro N W W' D Mb U Sd Kc rd put hU
  obtain ⟨body, hb⟩ := hU.lay
  exact ⟨fun M M' k => Prod.ext (hU.over M M' k.1) rfl,
    ⟨fun w k₀ => (body w k₀, D.rest w), fun w M k₀ η => Prod.ext (hb w M k₀ η) rfl⟩,
    hU.pad⟩

end
end Cb
