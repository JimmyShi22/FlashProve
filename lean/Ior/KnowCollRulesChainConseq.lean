-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesChainConseq.lean: "the masks are fresh after the chain" (`Chain.FreshFor`,
Ior/KnowCollRulesChain.lean), for a coarser reading.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean): a rule
of consequence for one property of a chain.
Statements and proofs. No protocol, no code occurs here.
A link is here an IOR with its honest side, as a step of a chain (as a record with extractor and
numbers: `IOR.Link`, Ior/KnowCollRulesChain.lean).

Why: along a chain it is convenient to carry the finest reading for which the masks are fresh (all
of the witness but the pads and the encoding randomness of the oracle that holds the masks): then
every later link is easily seen not to look at the masks. A masked block reads less.

Main names:
  `Spec.blind_conseq`: a link that does not look at the masks (Ior/KnowCollRulesMask.lean:
    `Blind`), read more coarsely at its output (by g, which commutes with the overwriting).
  `Spec.freshFor_conseq`, for non-empty Mk: `c.FreshFor kc Mk put` (Ior/KnowCollRulesChain.lean)
    gives `c.FreshFor` (g after kc) Mk put', if g (put M k) = put' M (g k).
  `Spec.blind_hand`: a link whose honest prover's messages, explicit part and last witness
    do not depend on the witness but for handing it on is Blind for every reading. Stated for the
    form "the run on w' is the run on w, with the last witness w' for w".

Limits: on every reading, a finer one too: `Spec.blind_hand` (see its row); beyond it this file
says nothing on finer readings.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesChain

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Spec
open IOR

def blind_conseq : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ki Ko Ko' : Type) (kci : Wi → Ki) (kco : Wo → Ko) (g : Ko → Ko') (Mk : Type)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko) (puto' : Mk → Ko' → Ko'),
    (∀ M k, g (puto M k) = puto' M (g k)) → H.Blind kci kco Mk puti puto →
    H.Blind kci (fun w => g (kco w)) Mk puti puto'

/-- Fresh after the chain, for a coarser reading. -/
def freshFor_conseq : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (Kc Kc' : Type) (kc : B.W → Kc) (g : Kc → Kc')
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc) (put' : Mk → Kc' → Kc'),
    (∀ M k, g (put M k) = put' M (g k)) → c.FreshFor kc Mk put →
    c.FreshFor (fun w => g (kc w)) Mk put'

/-- A link that only hands its witness on is blind for every reading. -/
def blind_hand : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (W : Type) (H : R.Honest W W) (Kc : Type)
      (kc : W → Kc) (Mk : Type) (put : Mk → Kc → Kc),
    (∀ w w' x c ρ,
      ((H.strat w' x c).run ρ).1 = ((H.strat w x c).run ρ).1 ∧
      ((H.strat w' x c).run ρ).2.1 = ((H.strat w x c).run ρ).2.1) →
    (∀ w x c ρ, ((H.strat w x c).run ρ).2.2 = w) → H.Blind kc kc Mk put put

end Spec

open IOR IOR.Chain

theorem blind_conseq :
    Spec.blind_conseq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ g _ _ _ _ hg hB w w' M x c ρ h =>
  ⟨(hB w w' M x c ρ h).1,
    (hB w w' M x c ρ h).2.1,
    (congrArg g (hB w w' M x c ρ h).2.2).trans (hg M _)⟩

theorem freshFor_conseq : Spec.freshFor_conseq := by
  intro K A B c Kc Kc' kc g Mk _ _ put put' hg h
  cases c with
  | one l =>
      exact (freshFor_one l _ Mk put').2
        (fresh_conseq _ _ _ _ _ _ _ _ _ _ _ _ Kc Kc' kc g Mk put put' (fun _ _ _ h => h)
          (fun _ _ h => h) hg ((freshFor_one l kc Mk put).1 h))
  | snoc c l =>
      refine (freshFor_snoc c l _ Mk put').2 ?_
      rcases (freshFor_snoc c l kc Mk put).1 h with h | ⟨Kc₀, kc₀, put₀, h1, h2⟩
      · exact Or.inl
          (fresh_conseq _ _ _ _ _ _ _ _ _ _ _ _ Kc Kc' kc g Mk put put'
            (fun _ _ _ h => h) (fun _ _ h => h) hg h)
      · exact Or.inr
          ⟨Kc₀, kc₀, put₀, h1, blind_conseq _ _ _ _ _ _ _ _ _ _ _ kc₀ kc g Mk put₀ put put' hg h2⟩

theorem blind_hand : Spec.blind_hand := fun _ _ _ _ _ _ _ _ _ _ _ h1 h2 w w' _ x c ρ h =>
  ⟨(h1 w w' x c ρ).1, (h1 w w' x c ρ).2, by rw [h2, h2]; exact h⟩

end Iop
