-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkChain.lean: the test that two encodings hold the same index, written as a chain
of reductions with any last part, has the properties that the holographic IOP requires of it, under
the hypotheses of its statement.

One definition, one statement, its proof. For "link", "joint" and "tail" see the head of
Cb/Obj/LdObjectLink.lean.
Cb/Ld/LdLinkChain.lean: under the hypotheses of its statement (`Spec.ldLc_tail`), the link's core as
a chain, with any closing chain that stands behind it, is a tail from the first joint.
Cb/Obj/LdObjectLink.lean: under `Cf.OK L`, every tail from the first joint meets the object's two
lists for the link (`Hiop.LinkListR`, `Hiop.LinkKnowR`), over the configuration `Cf.conf`. Here the
two are put together.

Main names:
  `Spec.ldOl_chainC`: from:
      the code has a position (`Nonempty (Fin Cf.C₀.n)`);
      `Cf.OK L`;
      bounds ε₀, ε₁ on the bad points of the two folds on the tables without a collision at their
        record's seed;
      the places of the layout on the cube are distinct;
      what the sending asks (`S.OK`);
      the closing chain cZ stands behind the core (`cZ.OkFrom`) and has the budgets' half
        (`cZ.SidesCT`):
    `Hiop.LinkListR` and `Hiop.LinkKnowR` of `K.link (K.ofChainC S ε₀ ε₁ cZ d)`.

So a closing whose splittings use mask-only messages sent in the core is reached.

Notation: `K.free` (Cb/Obj/LdObjectLink.lean): the condition of the chain on each index: no
collision at the record's seed; `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says
that it bounds the lists at the radius of decoding); `d`: a value of `K.P.W0` (Cb/Ld/LdLink.lean):
two tables of full messages.

Limits: no closing chain is given.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinkChain
import Cb.Obj.LdObjectLinkProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the link with a closing chain, as a tail from the first joint -/
def LdCf.LinkPar.ofChainC {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E]
    {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
    (cZ : Chain Unit K.P.J4 ldJT) (d : K.P.W0) : K.Tail :=
  ⟨(K.P.linkC K.free K.free S ε₀ ε₁ cZ d).R,
    (K.P.linkC K.free K.free S ε₀ ε₁ cZ d).H,
    (K.P.linkC K.free K.free S ε₀ ε₁ cZ d).ext,
    (K.P.linkC K.free K.free S ε₀ ε₁ cZ d).P⟩

def Spec.ldOl_chainC (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (L ε₀ ε₁ : ℕ)
      (cZ : Chain Unit K.P.J4 ldJT) (d : K.P.W0),
    Cf.OK L → K.P.FoldErr K.free K.free ε₀ ε₁ → Function.Injective K.pl → S.OK →
    cZ.OkFrom (K.P.coreC K.free K.free S ε₀ ε₁) → cZ.SidesCT (K.P.q3 S) →
    LinkListR (C := Cf.conf) (K.link (K.ofChainC S ε₀ ε₁ cZ d))
      (K.hLink (K.ofChainC S ε₀ ε₁ cZ d)) (K.nums (K.ofChainC S ε₀ ε₁ cZ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.ofChainC S ε₀ ε₁ cZ d))
      (K.nums (K.ofChainC S ε₀ ε₁ cZ d)).err

theorem ldOl_chainC (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOl_chainC F E :=
  fun Cf _ K S L ε₀ ε₁ cZ d hOK hF hpl hS hZ hs =>
    ldOl_object F E Cf K (K.ofChainC S ε₀ ε₁ cZ d) L hOK
      (ldLc_tail K.P K.free K.free ε₀ ε₁ S cZ d hF hpl hS hZ hs)

end Cb
