-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchLocProofs.lean: the proofs of the statements of Cb/Ld/LdSwitchLoc.lean (the one-round
block "locations": the frame; the verifier and the claims are parameters).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The order: the data; the bad set, the backward step, knowledge soundness; completeness; zero
knowledge; locality (`ldLoc_isLocal`, stated here); the bundle (`ldLoc_good`). Nothing is defined
here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdSwitchLoc.lean):
  `ldLoc_data`: the data: one round; at most t reads of the old word, none of the carried oracles; a
    carried symbol is copied.
  `ldLoc_within`: under hk1 of that head, on a statement whose carried claim fixes the old part: the
    bad set within the error, a count of lists of positions: (|P| - e - 1)^t.
  `ldLoc_clean`: under hk1: the backward step: no bad list; then a witness of the output statement
    in the relaxation is one of the input statement.
  `ldLoc_know`: under hk1 and hk2: round-by-round knowledge soundness; the extractor is the
    identity.
  `ldLoc_acc`: under hc: completeness: perfect.
  `ldLoc_exactWith`: see its statement in Cb/Ld/LdSwitchLoc.lean.
  `ldLoc_isLocal` (stated here): locality (`IOR.IsLocal`).
  `ldLoc_good`: under hk1, hk2, hc, hon: the bundle `IOR.Good` (Ior/Chain.lean).

Limits: see the head of Cb/Ld/LdSwitchLoc.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSwitchLoc
import Blocks.Decode
import Iop.ViewKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks

theorem ldLoc_data : Spec.ldLoc_data := by
  classical
  intro E P Xi Xo _ _ V E₀
  refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun ρ => ?_, fun ρ q h => ?_,
    fun _ _ => rfl, fun _ _ => rfl, ⟨fun p => p.elim (fun x => x.elim) fun x => x.elim⟩⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    exact absurd hi (by simp)

theorem ldLoc_within : Spec.ldLoc_within := by
  intro E P Xi Xo _ _ V E₀ W old e ΦiR ΦoR a hk1 hk2
  refine ⟨fun _ => ?_, fun _ _ => trivial⟩
  by_cases hex : ∃ w, ΦiR a.1 a.2.2 w ∧ ¬ V.Cin.Near e a.2.1 (V.Cin.enc (old w).1 (old w).2)
  · obtain ⟨w₀, hw₀, hn₀⟩ := hex
    refine le_trans (cnt_mono fun Qs hQ i => ?_)
      (cnt_miss_le_of_lt
        (P := fun x => V.Cin.T a.2.1 x ≠ V.Cin.T (V.Cin.enc (old w₀).1 (old w₀).2) x) (not_le.1 hn₀)
        V.t)
    obtain ⟨w, hw, -⟩ := hQ
    obtain ⟨hi, hat⟩ := hk1 Qs _ w hw
    rw [hk2 w₀ w hw₀ hi]
    exact fun hne => hne (congrFun hat i).symm
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro Qs ⟨w, hw, hn⟩
      exact hex ⟨w, (hk1 Qs _ w hw).1, hn⟩

theorem ldLoc_clean : Spec.ldLoc_clean := by
  intro E P Xi Xo _ _ V E₀ W old e ΦiR ΦoR a hk1 τ b w hc hb hw
  obtain ⟨m, Qs, u⟩ := τ
  obtain rfl : (V.out a.1 Qs (V.at a.2.1 Qs), (((), a.2.2) : (extNone.prod E₀).Str)) = b :=
    Option.some.inj hb
  exact ⟨by_contra fun hn => hc.1 ⟨w, hw, hn⟩, (hk1 Qs _ w hw).1⟩

theorem ldLoc_know : Spec.ldLoc_know := by
  intro E P Xi Xo _ _ V E₀ W old e ΦiR ΦoR on hk1 hk2
  exact Reduction.Know.of_badFam (ldLocBad V old e ΦoR)
    (fun a ha =>
      ldLoc_within E P Xi Xo V E₀ W old e ΦiR ΦoR a (fun Qs v w => hk1 a.1 Qs v a.2.2 w) (hk2 a ha))
    fun a τ b w _ hc hb hw =>
      ldLoc_clean E P Xi Xo V E₀ W old e ΦiR ΦoR a
        (fun Qs v w => hk1 a.1 Qs v a.2.2 w) τ b w hc hb hw

theorem ldLoc_acc : Spec.ldLoc_acc := by
  intro E P Xi Xo _ _ V E₀ W old ΦiH ΦoH hc x y w c ρ hR _
  obtain ⟨f, y₀⟩ := y
  obtain ⟨Qs, u⟩ := ρ
  obtain ⟨hy, hx⟩ := hR
  obtain rfl : f = V.Cin.enc (old w).1 (old w).2 := hy
  exact ⟨rfl, hc x y₀ w Qs hx⟩

theorem ldLoc_exactWith : Spec.ldLoc_exactWith := by
  intro E P Xi Xo _ _ V E₀ W old Ri x y w _ ρ _ T _
  obtain ⟨Qs, u⟩ := ρ
  exact if_neg fun h => h.elim id id

theorem ldLoc_isLocal {E P Xi Xo : Type} [Fintype P] [Nonempty P]
    (V : LdLocV E P Xi Xo) (E₀ : ExtSpec) : (ldLocOf V E₀).IsLocal where
  out := by
    classical
    intro x y y' τ τ' hρ _ hy _
    obtain ⟨m, Qs, u⟩ := τ
    obtain ⟨m', Qs', u'⟩ := τ'
    obtain rfl : Qs = Qs' := congrArg Prod.fst hρ
    have hat : V.at y.1 Qs = V.at y'.1 Qs :=
      funext fun i =>
        Sum.inl.inj (hy (Sum.inl (Qs i)) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
    show some (V.out x Qs (V.at y.1 Qs)) = some (V.out x Qs (V.at y'.1 Qs))
    rw [hat]
  imp := by
    intro y y' τ τ' q _ _ hy _
    rcases q with q | q
    · exact q.elim
    · exact congrArg Sum.inr (Sum.inr.inj (hy (Sum.inr q) (Finset.mem_singleton_self _)))

theorem ldLoc_good : Spec.ldLoc_good := by
  intro E P Xi Xo _ _ V E₀ W Kc old core e ΦiH ΦiR ΦoH ΦoR on on' hk1 hk2 hc hon
  exact
    { point := ⟨V.pt⟩
      isLocal := ldLoc_isLocal V E₀
      acc := ldLoc_acc E P Xi Xo V E₀ W old ΦiH ΦoH hc
      onOut := fun a τ b ha hb => by
        obtain ⟨m, Qs, u⟩ := τ
        obtain rfl : (V.out a.1 Qs (V.at a.2.1 Qs), (((), a.2.2) : (extNone.prod E₀).Str)) = b :=
          Option.some.inj hb
        exact hon a Qs ha
      keeps := fun _ _ _ _ => rfl
      prBad := prRho_empty _ fun _ h => h
      cover := fun _ _ => Set.empty_subset _
      prCov := fun _ => prRho_empty _ fun _ h => h
      know := ldLoc_know E P Xi Xo V E₀ W old e ΦiR ΦoR on hk1 hk2
      exact := ⟨ldLocSim V E₀, ldLoc_exactWith E P Xi Xo V E₀ W old _⟩ }

end Cb
