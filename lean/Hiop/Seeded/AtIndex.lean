-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/AtIndex.lean: the bound for the two games of Hiop/Seeded/Game.lean AT ONE INDEX, with
the premise on the simulators asked at that index alone.

Definitions, one statement (`Spec.lifeSeededAt`) and its proof. A general theorem; this file states
no goal of the release.

`Spec.lifeSeededN` (Hiop/Seeded/Total.lean) asks that the simulators be good for the honest sides at
EVERY index (`SimsG.Good`) and concludes at every index. Its proof spends that premise at the index
of the real game alone. Here the premise is `SimsG.GoodAt i`: the three clauses of `SimsG.Good` at
the one index i; the conclusion is at that i. So a caller whose honest sides can be simulated at
some indices alone has the bound at these.
ALONE IT IS NO STATEMENT ON HIDING. It speaks of ONE index, and all its letters stand under "for
all", whose order says nothing: a caller could take other simulators for each index, and at
simulators that show the index outright the premise holds of honest sides that do the same. It says
something on hiding where ONE value of Sm and ONE i₀ are used at two indices or more, that is, where
`SimsG.GoodAt` is had for the same Sm at each of them: then the real games at these indices are all
near one simulated game. (So in Johnson/WrapLaws/AtKit.lean: the simulators are letters of the
premises there, which ask that they be good at every index of a range.) Nothing is asked of the
honest sides at i₀, which is any index. What swaps i for i₀ is the hiding of the encoding
(`ReadsG.hidE`), which is asked at all pairs of indices, as before.

Main names: `SimsG.GoodAt`; `SimsG.Good.at`, `SimsG.good_iff` (good = good at every index);
`near_realG_at`; `Spec.lifeSeededAt`, `lifeSeededAt`; `lifeSeededN_again` (a guard: the statement at
all indices follows). `near_realG_at` follows `near_realG` (Hiop/Seeded/GameProof.lean) line by
line.

Limits: those of Hiop/Seeded/Game.lean.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Total

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Rom Compile.Lifetime
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X}

/-- The simulators are good for the honest sides P AT THE INDEX i: the clauses of `SimsG.Good`
(Hiop/Seeded/Game.lean) at that index. -/
structure SimsG.GoodAt (Sm : SimsG L) (K : Kit L) (P : RecsG L) (Gs : L.OutOfDomainSeed → Prop)
    (Ryes : I → X → Prop) (i : I) (zT zL zO : ℝ≥0∞) : Prop where
  goodT : ∀ e r s, Gs s →
    pr (K.μT e (L.recOf i r s))
      {a | ∃ ρ, K.ρT a = some ρ ∧ (P.T e).output (i, r, s) (L.recOf i r s) ρ ≠
        Sm.T e (L.recOf i r s) ρ (L.offline.extAns (L.recOf i r s) ρ (L.encodeIndex i r))} ≤ zT
  goodL : ∀ e r s r' s', Gs s → Gs s' →
    pr (K.μL e (L.recOf i r s, L.recOf i r' s'))
      {a | ∃ ρ, K.ρL a = some ρ ∧
        (P.Lk e).output (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s') ρ ≠
          Sm.Lk e (L.recOf i r s, L.recOf i r' s') ρ
            (L.link.extAns (L.recOf i r s, L.recOf i r' s') ρ (L.encodeIndex i r, L.encodeIndex i r'))} ≤ zL
  goodB : ∀ e r s x, Gs s → Ryes i x →
    pr (K.μB e (x, L.recOf i r s))
      {a | ∃ ρ, K.ρB a = some ρ ∧ (P.B e).output (i, r, s) (x, L.recOf i r s) ρ ≠
        Sm.B e (x, L.recOf i r s) ρ (L.onlineBatch.loc.extAns (x, L.recOf i r s) ρ (L.encodeIndex i r))} ≤ zO

variable {K : Kit L} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞} {P : RecsG L}
  {Sm : SimsG L}

theorem SimsG.Good.at (h : Sm.Good K P Gs Ryes zT zL zO) (i : I) :
    Sm.GoodAt K P Gs Ryes i zT zL zO :=
  ⟨fun e => h.goodT e i, fun e => h.goodL e i, fun e => h.goodB e i⟩

/-- Good is: good at every index. -/
theorem SimsG.good_iff :
    Sm.Good K P Gs Ryes zT zL zO ↔ ∀ i, Sm.GoodAt K P Gs Ryes i zT zL zO :=
  ⟨fun h i => h.at i, fun h => ⟨fun e i => (h i).goodT e, fun e i => (h i).goodL e,
    fun e i => (h i).goodB e⟩⟩

namespace Spec

/-- The real game on the index i and the simulated game, for simulators that are good at i, and an
adversary with at most n calls for a session, all at instances in the relation with i. -/
def lifeSeededAt : Prop :=
  ∀ (S : OSpec) (I X : Type) (L : HolographicProtocol I X) (K : Kit L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
      (b qT qpar qch qon : ℕ) (zT zL zO : ℝ≥0∞),
    ReadsG L Gs b qT qpar qch qon →
    ∀ P : RecsG L, P.Ext →
      ∀ (Sm : SimsG L) (B : BoundsR), B.Fits b qT qpar qch qon →
        ∀ i : I, Sm.GoodAt K P Gs Ryes i zT zL zO →
          ∀ (i₀ : I) (n : ℕ) (α : Type) (A : Adv S (GOut L K.form) (GIn L K.form) α),
            A.CallsOK (okCall (Ryes i)) → SessLe A n →
              tv ((interact (gameReal L K P i B Gs S) A (none, Table.empty S)).map Prod.fst)
                  ((interact (gameSim L K Sm i₀ B Gs S) A (none, Table.empty S)).map Prod.fst) ≤
                errN B n zT zL zO

end Spec

/-- The real side on the index i is near simulators that are good at i. -/
theorem near_realG_at (hX : P.Ext) {i : I} (hS : Sm.GoodAt K P Gs Ryes i zT zL zO) :
    (realLawsG L K P i).Near (simsFG L K Sm) Gs i (Ryes i) zT zL zO where
  rc := fun _ => rfl
  y := fun _ _ => rfl
  T := fun e u hu => by
    have h0 := hS.goodT e u.1 u.2 hu
    rw [← hX.extT e i u.1 u.2] at h0
    have h1 := tv_runAt_le (P.T e) (Sm.T e) (K.μT e (L.recOf i u.1 u.2)) K.ρT (i, u.1, u.2)
      (L.recOf i u.1 u.2) h0
    rw [hX.extT] at h1
    exact h1
  Lk := fun e u u' hu hu' => by
    obtain ⟨r, s⟩ := u
    obtain ⟨r', s'⟩ := u'
    have h0 := hS.goodL e r s r' s' hu hu'
    rw [← hX.extL e i r s r' s'] at h0
    have h1 := tv_runAt_le (P.Lk e) (Sm.Lk e) (K.μL e (L.recOf i r s, L.recOf i r' s')) K.ρL
      (i, (r, s), (r', s')) (L.recOf i r s, L.recOf i r' s') h0
    rw [hX.extL] at h1
    exact h1
  B := fun e u x _ hu hx => by
    have h0 := hS.goodB e u.1 u.2 x hu hx
    rw [← hX.extB e i u.1 u.2] at h0
    have h1 := tv_runAt_le (P.B e) (Sm.B e) (K.μB e (x, L.recOf i u.1 u.2)) K.ρB (i, u.1, u.2)
      (x, L.recOf i u.1 u.2) h0
    rw [hX.extB] at h1
    refine h1.trans (le_of_eq ?_)
    show zO = ((1 : ℕ) : ℝ≥0∞) * zO
    rw [Nat.cast_one, one_mul]

theorem lifeSeededAt : Spec.lifeSeededAt := by
  intro S I X L K Gs Ryes b qT qpar qch qon zT zL zO hR P hX Sm B hB i hS i₀ n α A hA hn
  exact game_of_view_n S I X L K.form (realLawsG L K P i).host Gs (Ryes i) B n
    (simWholeF L K.form (simsFG L K Sm) i₀) (errN B n zT zL zO)
    (form_laws_n I X L K.form Gs (Ryes i) b qT qpar qch qon zT zL zO hR.hidE (simsFG L K Sm)
      (counts_simsFG hR K Sm) (realLawsG L K P i) i (near_realG_at hX hS) B hB i₀ n) α A hA hn

/-- A guard: the statement at all indices follows from the statement at one. -/
theorem lifeSeededN_again : Spec.lifeSeededN :=
  fun S I X L K Gs Ryes b qT qpar qch qon zT zL zO hR P hX Sm hS B hB i i₀ n α A hA hn =>
    lifeSeededAt S I X L K Gs Ryes b qT qpar qch qon zT zL zO hR P hX Sm B hB i (hS.at i) i₀ n α A
      hA hn

end Hiop.Seeded

#print axioms Hiop.Seeded.lifeSeededAt
#print axioms Hiop.Seeded.lifeSeededN_again
