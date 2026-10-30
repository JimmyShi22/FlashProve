-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkFull.lean: the test that two encodings hold the same index, as a chain of
reductions whose last part is a parameter that tests the oracle messages of the link's family as one
group: the properties that the holographic IOP requires of it, as a theorem with hypotheses.

What stays a parameter with a property, one level lower: the whole test T (`Kc.T`) on the one group
(`T.OK`). One definition, one statement (`Cb.Spec.ldOl_full`), its proof: an assembly. For "link",
"joint" and "tail" see the head of Cb/Obj/LdObjectLink.lean.

  Cb/Ld/LdLinkChain.lean: the link's core as a chain; with any closing chain that stands behind it
    (`IOR.Chain.OkFrom`, Ior/KnowCollPiece.lean): a tail. (not all hypotheses are named here: see
    `Spec.ldLc_tail`)
  Cb/Ld/LdLinkClose.lean: the closing: one step without rounds (the rows that are left, as forms on
    the complex of one group), the bridge, a whole test T on that group; under the hypotheses of its
    statement (`Spec.ldLkC_chain`), it stands behind every chain.
  Cb/Obj/LdObjectLink.lean (for the link with a closing chain: Cb/Obj/LdObjectLinkChain.lean): under
    `Cf.OK L`, every tail from the link's first joint meets the object's two lists for the link
    (`Hiop.LinkListR`, `Hiop.LinkKnowR`), over the configuration `Cf.conf`.
  `Spec.ldOl_full`: so: `Hiop.LinkListR` ∧ `Hiop.LinkKnowR` for the link with this closing.

What is still asked, all in the statement's own text but the last:
  the code has a position (`Nonempty (Fin Cf.C₀.n)`);
  `Cf.OK L` (code, format and model of the configuration);
  ε₀, ε₁ bound the bad points of the two folds on tables without a collision (from agreement and
    lists, at radii within a radius of decoding below the distance: `Cb.ldLk_foldErr_rec`);
  the layout's places on the cube are distinct;
  what the sending of the two folded rows asks (`S.OK`);
  `Kc.OK`: the bridge's evader evades, the group's complex has lists of at most `Kc.L` members at
    the joint radius, the joint radius implies each member's, and the whole test T is a tail
    (`LdEnd.OK`, that is `TailTr`, Cb/Ld/LdTowerKit.lean, whose `good : GoodT`
    (Ior/KnowCollGood.lean) has `acc`, `know` and `exact` among its clauses; for towers with
    `LdTower.OK` a theorem: `Cb.ldTower_tail`);
  the test needs no more positions than the sent words bear;
  whatever the arguments hold as proofs (among them `Cf.hp`, `Kc.all`, `Kc.neP`).

Limits: no tower is chosen. No bound on a list or on agreement is proved here. This file does not
say that `Cf.OK L`, `S.OK` and `Kc.OK` can be met together: no instance is given.



Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkChain
import Cb.Ld.LdLinkCloseProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The link of the object: core, then the closing Kc. -/
def LdCf.LinkPar.full {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E]
    {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
    (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0) : K.Tail :=
  K.ofChainC S ε₀ ε₁ (Kc.cZ d₂) d

def Spec.ldOl_full (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (L ε₀ ε₁ : ℕ)
      (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0),
    Cf.OK L → K.P.FoldErr K.free K.free ε₀ ε₁ → Function.Injective K.pl → S.OK →
    Kc.OK → (∀ a, Kc.t ≤ S.t a) →
    LinkListR (C := Cf.conf) (K.link (K.full S ε₀ ε₁ Kc d₂ d))
      (K.hLink (K.full S ε₀ ε₁ Kc d₂ d)) (K.nums (K.full S ε₀ ε₁ Kc d₂ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.full S ε₀ ε₁ Kc d₂ d)) (K.nums (K.full S ε₀ ε₁ Kc d₂ d)).err

theorem ldOl_full (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOl_full F E :=
  fun Cf _ K S L ε₀ ε₁ Kc d₂ d hOK hF hpl hS hK ht =>
    ldOl_chainC F E Cf K S L ε₀ ε₁ (Kc.cZ d₂) d hOK hF hpl hS
      (ldLkC_chain _ _ _ _ _ K.P Kc d₂ S _ (K.P.coreC K.free K.free S ε₀ ε₁) hK ht).1
      (ldLkC_chain _ _ _ _ _ K.P Kc d₂ S _ (K.P.coreC K.free K.free S ε₀ ε₁) hK ht).2

end Cb
