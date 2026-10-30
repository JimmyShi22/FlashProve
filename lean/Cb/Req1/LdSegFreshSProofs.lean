-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFreshSProofs.lean: the proofs of the statements of Cb/Req1/LdSegFreshS.lean.
-/
import Cb.Req1.LdSegFreshS
import Ior.FreshJoinProofs

set_option autoImplicit false

namespace Iop
open Prob IOR IOR.Chain

namespace IOR.Chain
variable {K : Type} {A B C : Joint K}

theorem okS_one (l : Link K A B) : (Chain.one l).OkS ↔ l.GoodT := by rw [OkS]
theorem okS_snoc (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).OkS ↔
    c.OkS ∧ (l.GoodT ∨ ∃ D : MaskData l.R B.W, l.GoodM D ∧ c.FreshS D.kc D.Mk D.put) := by rw [OkS]

end IOR.Chain

theorem allB_of_okS : Spec.allB_of_okS := by
  intro K A B c
  induction c with
  | one l =>
      rw [okS_one, allB_one]
      exact fun h => ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h).1
  | snoc c l ih =>
      rw [okS_snoc, allB_snoc]
      refine fun h => ⟨ih h.1, ?_⟩
      rcases h.2 with h2 | ⟨D, h2, -⟩
      · exact ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 h2).1
      · exact h2.base

theorem chainS_ok : Spec.chainS_ok := by
  intro K A B c d
  induction c with
  | one l =>
      intro h
      rw [link_one]
      exact (okS_one l).1 h
  | snoc c l ih =>
      intro h
      obtain ⟨h1, h2⟩ := (okS_snoc c l).1 h
      rw [link_snoc]
      rcases h2 with h2 | ⟨D, h2, hF⟩
      · exact goodT_seq K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ (ih h1) h2
      · exact goodT_seq_masked K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ D (ih h1) (hF d) h2

theorem freshS_of_for : Spec.freshS_of_for := fun K A B c Kc kc Mk _ _ put hB hF d =>
  chain_fresh K A B c d Kc kc Mk put hB hF

theorem okS_of_ok : Spec.okS_of_ok := by
  intro K A B c
  induction c with
  | one l => rw [ok_one, okS_one]; exact fun h => h
  | snoc c l ih =>
      rw [ok_snoc, okS_snoc]
      refine fun h => ⟨ih h.1, ?_⟩
      rcases h.2 with h2 | ⟨D, h2, hF⟩
      · exact Or.inl h2
      · exact Or.inr
          ⟨D, h2, freshS_of_for K _ _ c _ D.kc D.Mk D.put ((ok_of_allT K _ _ c).2 h.1) hF⟩

theorem freshS_join : Spec.freshS_join := fun _ _ _ c Kc kc M₁ M₂ _ _ _ _ put₁ put₂ h₁ h₂ d =>
  fresh_join _ _ _ _ _ _ _ (c.link d).H _ _ Kc kc M₁ M₂ put₁ put₂ (h₁ d) (h₂ d)

theorem freshS_conseq : Spec.freshS_conseq := fun _ _ _ c Kc Kc' kc g Mk _ _ put put' hg h d =>
  fresh_conseq _ _ _ _ _ _ _ (c.link d).H _ _ _ _ Kc Kc' kc g Mk put put' (fun _ _ _ h => h)
    (fun _ _ h => h) hg (h d)

theorem freshS_equiv : Spec.freshS_equiv := fun _ _ _ c Kc kc Mk Mk' _ _ _ _ e put h d =>
  fresh_maskEquiv _ _ _ _ _ _ _ (c.link d).H _ _ Kc kc Mk Mk' e put (h d)

theorem freshS_jcl : Spec.freshS_jcl := by
  intro K A B c X hX f hf
  induction hf with
  | base f h => exact hX f h
  | join Kc kc M₁ M₂ put₁ put₂ _ _ ih₁ ih₂ => exact freshS_join K A B c Kc kc M₁ M₂ put₁ put₂ ih₁ ih₂
  | conseq f Kc' g put' hg _ ih => exact freshS_conseq K A B c f.Kc Kc' f.kc g f.Mk f.put put' hg ih
  | equiv f Mk' e _ ih => exact freshS_equiv K A B c f.Kc f.kc f.Mk Mk' e f.put ih

theorem freshS_blind : Spec.freshS_blind := by
  intro K A B C c l Kc' Kc kc' kc Mk _ _ put' put h hB d
  rw [link_snoc]
  exact fresh_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c.link d).P.bud
    l.P.bud Kc' Kc kc' kc Mk put' put (h d) hB

theorem freshS_fresh : Spec.freshS_fresh := by
  intro K A B C c l Kc kc Mk _ _ put hB h d
  rw [link_snoc]
  exact fresh_snd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c.link d).P.bud l.P.bud Kc kc Mk put
    (chain_goodB K _ _ c d hB).acc h

theorem freshS_of_given : Spec.freshS_of_given := by
  intro K A B C c₀ c base
  induction c with
  | one l =>
      intro f h0 _ hb hf
      rw [append_one]
      rcases (freshGiven_one l base f).1 hf with hF | ⟨Kc', kc', put', hg, hBl⟩
      · exact freshS_fresh K _ _ _ c₀ l f.Kc f.kc f.Mk f.put h0 hF
      · exact freshS_blind K _ _ _ c₀ l Kc' f.Kc kc' f.kc f.Mk put' f.put (hb _ hg) hBl
  | snoc c l ih =>
      intro f h0 hc hb hf
      rw [append_snoc]
      have hc' := (allB_snoc c l).1 hc
      rcases (freshGiven_snoc c l base f).1 hf with hF | ⟨Kc', kc', put', hg, hBl⟩
      · exact freshS_fresh K _ _ _ (c₀.append c) l f.Kc f.kc f.Mk f.put
          (((all_append K _ _ _ c₀ c).1).2 ⟨h0, hc'.1⟩) hF
      · exact freshS_blind K _ _ _ (c₀.append c) l Kc' f.Kc kc' f.kc f.Mk put' f.put
          (ih ⟨Kc', kc', f.Mk, put'⟩ h0 hc'.1 hb hg) hBl

theorem okS_of_given : Spec.okS_of_given := by
  intro K A B C c₀ c base h0 hb
  induction c with
  | one l =>
      intro h
      rw [append_one, okS_snoc]
      refine ⟨h0, ?_⟩
      rcases (okGiven_one l base).1 h with h | ⟨D, hD, hg⟩
      · exact Or.inl h
      · exact Or.inr ⟨D, hD, hb _ hg⟩
  | snoc c l ih =>
      intro h
      obtain ⟨h1, h2⟩ := (okGiven_snoc c l base).1 h
      rw [append_snoc, okS_snoc]
      refine ⟨ih h1, ?_⟩
      rcases h2 with h2 | ⟨D, hD, hg⟩
      · exact Or.inl h2
      · exact Or.inr
          ⟨D, hD,
            freshS_of_given K _ _ _ c₀ c base D.fact (allB_of_okS K _ _ c₀ h0)
              (allB_of_okGiven K _ _ c base h1) hb hg⟩

end Iop
