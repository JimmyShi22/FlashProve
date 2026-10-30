-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCarryKit.lean: facts on fresh masks: a coarser reading; another type for the same
masks.

Statements (Iop.Spec.*) and proofs. No protocol, no code occurs here.
Cb/Req1/LdSegFresh.lean has facts (a reading of a witness, with some mask entries in it) and "after
the chain the masks of f are fresh, given the facts of base at its start" (`Chain.FreshGiven`). A
link: `IOR.Link` (Ior/KnowCollRulesChain.lean). The rules here are needed when facts are carried
from move to move.

Main names:
  `Spec.freshGiven_conseq`: a coarser reading at the end of the chain (g after kc, g commuting with
    the overwriting). Along a chain the wide reading is carried (all that later honest provers
    read); a masked block reads less.
  `Spec.fresh_maskEquiv`: the same masks under another type, at the link that sends them: if
    e : Mk ≃ Mk' (both finite and non-empty), then Fresh for (Mk, put) gives Fresh for (Mk', put
    after the inverse of e). (Say: functions on a one-point set, and scalars.)
  `Spec.blind_maskMap`: a link that does not look at the masks, for masks named through any map
    φ : Mk' → Mk.

Limits: no rule changes the type of masks of a fact that is given at the start of a chain: the set
"base" would have to be closed under the change.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFresh
import Ior.KnowCollRulesChainConseq

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Spec
open IOR

/-- Fresh after the chain, given facts at its start, for a coarser reading. -/
def freshGiven_conseq : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (base : MaskFact A.W → Prop) (f : MaskFact B.W)
      (Kc' : Type) (g : f.Kc → Kc') (put' : f.Mk → Kc' → Kc'),
    (∀ M k, g (f.put M k) = put' M (g k)) → c.FreshGiven base f →
    c.FreshGiven base ⟨Kc', fun w => g (f.kc w), f.Mk, put'⟩

/-- The same masks under another type. -/
def fresh_maskEquiv : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (Kc : Type)
      (kc : Wo → Kc) (Mk Mk' : Type) [Fintype Mk] [Nonempty Mk] [Fintype Mk'] [Nonempty Mk']
      (e : Mk ≃ Mk') (put : Mk → Kc → Kc),
    H.Fresh Ri bud kc Mk put → H.Fresh Ri bud kc Mk' fun M k => put (e.symm M) k

def blind_maskMap : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ki Ko : Type) (kci : Wi → Ki) (kco : Wo → Ko) (Mk Mk' : Type) (φ : Mk' → Mk)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    H.Blind kci kco Mk puti puto →
    H.Blind kci kco Mk' (fun M k => puti (φ M) k) fun M k => puto (φ M) k

end Spec

open IOR IOR.Chain

theorem freshGiven_conseq : Spec.freshGiven_conseq := by
  intro K A B c base f Kc' g put' hg h
  cases c with
  | one l =>
      refine (freshGiven_one l base _).2 ?_
      rcases (freshGiven_one l base f).1 h with h | ⟨Kc₀, kc₀, put₀, h1, h2⟩
      · exact Or.inl
          (fresh_conseq _ _ _ _ _ _ _ _ _ _ _ _ f.Kc Kc' f.kc g f.Mk f.put put'
            (fun _ _ _ h => h) (fun _ _ h => h) hg h)
      · exact Or.inr
          ⟨Kc₀, kc₀, put₀, h1,
            blind_conseq _ _ _ _ _ _ _ _ _ _ _ kc₀ f.kc g f.Mk put₀ f.put put' hg h2⟩
  | snoc c l =>
      refine (freshGiven_snoc c l base _).2 ?_
      rcases (freshGiven_snoc c l base f).1 h with h | ⟨Kc₀, kc₀, put₀, h1, h2⟩
      · exact Or.inl
          (fresh_conseq _ _ _ _ _ _ _ _ _ _ _ _ f.Kc Kc' f.kc g f.Mk f.put put'
            (fun _ _ _ h => h) (fun _ _ h => h) hg h)
      · exact Or.inr
          ⟨Kc₀, kc₀, put₀, h1,
            blind_conseq _ _ _ _ _ _ _ _ _ _ _ kc₀ f.kc g f.Mk put₀ f.put put' hg h2⟩

theorem fresh_maskEquiv : Spec.fresh_maskEquiv := by
  intro Xi Xo Ei Eo R Wi Wo H Ri bud Kc kc Mk Mk' _ _ _ _ e put hF x y w hw ρ hρ T hT
  refine Eq.trans ?_ (hF x y w hw ρ hρ T hT)
  exact MaskKit.map_unif_of_equiv ((Equiv.refl H.Coin).prodCongr e.symm)
    (fun a : H.Coin × Mk =>
      ((H.seen kc w x ρ T a.1).1, (H.seen kc w x ρ T a.1).2.1, put a.2 (H.seen kc w x ρ T a.1).2.2))

theorem blind_maskMap : Spec.blind_maskMap :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ _ _ hB w w' M x c ρ h => hB w w' (φ M) x c ρ h

end Iop
