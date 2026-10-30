-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkPairFull.lean: the test that two encodings hold the same index, as a chain of
reductions whose last part is a parameter, at any pair of conditions that the holographic IOP's own
condition implies (in the form `K.FitsK on0 on1`, which asks more than that:
Cb/Obj/LdObjectLinkPair.lean): the properties that the IOP requires of it, as a theorem with
hypotheses.

Definitions, statements (in `Cb.Spec`) and proofs.
For "link", "joint" and "tail" see the head of Cb/Obj/LdObjectLink.lean; for the pair, that of
Cb/Obj/LdObjectLinkPair.lean.

Main names:
  `K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d`: the link on chains (Cb/Ld/LdLinkChain.lean) with the closing
    of Cb/Ld/LdLinkClose.lean. At (`K.free`, `K.free`) it is `K.full` of
    Cb/Obj/LdObjectLinkFull.lean, by definition.
  `Spec.ldOlA_chainC`, `Spec.ldOlA_full`: `Hiop.LinkListR` and `Hiop.LinkKnowR` (Hiop/RecSubs.lean),
    from: the code has a position (`Nonempty (Fin Cf.C₀.n)`); `Cf.OK L`; `K.FitsK on0 on1`
    (Cb/Obj/LdObjectLinkPair.lean); bounds ε₀, ε₁ on the bad points of the two folds at the pair
    (`K.P.FoldErr on0 on1 ε₀ ε₁`); distinct places (`Function.Injective K.pl`); what the sending
    asks (`S.OK`); what the closing asks (`cZ.OkFrom`, `cZ.SidesCT` of a closing chain; `Kc.OK`, and
    `Kc.t ≤ S.t a` for every a, of the closing `Kc`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkPair
import Cb.Obj.LdObjectLinkFull
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdCf.LinkPar
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E} (K : Cf.LinkPar)
variable (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop)
variable [Fintype E] [Nonempty (Fin Cf.C₀.n)]

/-- the link with a closing chain, as a tail from the first joint -/
def ofChainCAt (S : K.P.Snd) (ε₀ ε₁ : ℕ) (cZ : Chain Unit K.P.J4 ldJT) (d : K.P.W0) :
    K.Tail :=
  ⟨(K.P.linkC on0 on1 S ε₀ ε₁ cZ d).R,
    (K.P.linkC on0 on1 S ε₀ ε₁ cZ d).H,
    (K.P.linkC on0 on1 S ε₀ ε₁ cZ d).ext,
    (K.P.linkC on0 on1 S ε₀ ε₁ cZ d).P⟩

/-- The link of the object: core, then the closing Kc. -/
def fullAt (S : K.P.Snd) (ε₀ ε₁ : ℕ) (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0) :
    K.Tail :=
  K.ofChainCAt on0 on1 S ε₀ ε₁ (Kc.cZ d₂) d

end LdCf.LinkPar

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOlA_chainC : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (S : K.P.Snd) (L ε₀ ε₁ : ℕ)
      (cZ : Chain Unit K.P.J4 ldJT) (d : K.P.W0),
    Cf.OK L → K.FitsK on0 on1 → K.P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective K.pl → S.OK →
    cZ.OkFrom (K.P.coreC on0 on1 S ε₀ ε₁) → cZ.SidesCT (K.P.q3 S) →
    LinkListR (C := Cf.conf) (K.link (K.ofChainCAt on0 on1 S ε₀ ε₁ cZ d))
      (K.hLink (K.ofChainCAt on0 on1 S ε₀ ε₁ cZ d)) (K.nums (K.ofChainCAt on0 on1 S ε₀ ε₁ cZ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.ofChainCAt on0 on1 S ε₀ ε₁ cZ d))
      (K.nums (K.ofChainCAt on0 on1 S ε₀ ε₁ cZ d)).err

/-- The link with its closing: `LinkListR` and `LinkKnowR`, under the hypotheses below. -/
def ldOlA_full : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (S : K.P.Snd) (L ε₀ ε₁ : ℕ)
      (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0),
    Cf.OK L → K.FitsK on0 on1 → K.P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective K.pl → S.OK →
    Kc.OK → (∀ a, Kc.t ≤ S.t a) →
    LinkListR (C := Cf.conf) (K.link (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d))
      (K.hLink (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)) (K.nums (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d))
      (K.nums (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)).err

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOlA_chainC :
    Spec.ldOlA_chainC F E := fun Cf _ K on0 on1 S L ε₀ ε₁ cZ d hOK hFit hF hpl hS hZ hs =>
  ldOlA_object F E Cf K on0 on1 (K.ofChainCAt on0 on1 S ε₀ ε₁ cZ d) L hOK hFit
    (ldLc_tail K.P on0 on1 ε₀ ε₁ S cZ d hF hpl hS hZ hs)

theorem ldOlA_full :
    Spec.ldOlA_full F E := fun Cf _ K on0 on1 S L ε₀ ε₁ Kc d₂ d hOK hFit hF hpl hS hK ht =>
  ldOlA_chainC F E Cf K on0 on1 S L ε₀ ε₁ (Kc.cZ d₂) d hOK hFit hF hpl hS
    (ldLkC_chain _ _ _ _ _ K.P Kc d₂ S _ (K.P.coreC on0 on1 S ε₀ ε₁) hK ht).1
    (ldLkC_chain _ _ _ _ _ K.P Kc d₂ S _ (K.P.coreC on0 on1 S ε₀ ε₁) hK ht).2

end
end Cb
