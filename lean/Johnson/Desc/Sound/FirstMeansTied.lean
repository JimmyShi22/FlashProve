-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FirstMeansTied.lean: THE CHAIN OF PROMISES HAS A USER: what the rule for a file
asks of the first chain (`EachGoodIn` at the table's promises and relations, with the map to the
model at the first border) FROM `EachTied` (Johnson/Desc/Sound/ChainOfPromises.lean) AND hs
    (`TieStart`, FirstMeans.lean), in the place
of
`EachOwn`. One theorem: `firstChainMeans` (Johnson/Desc/Sound/FirstMeans.lean) with
`chainOfPromises` in the place of `jointsJoin`.

Limits: those of the two files. A rule over letters. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FirstMeans
import Johnson.Desc.Sound.ChainOfPromises

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

/-- **Every block tied, and the tie at the chain's start: the first chain's premise of the rule for
a file.** -/
theorem firstChainMeans_of_tied {C : CK} {D : WholeD} {all : List LeftT}
    {Y P S₁ S₂ S₃ X₁ X₂ Cl W : Type} (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (N : Numbers)
    (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (get : S₁ → P × First.S)
    (R₀ : S₁ × (EAll D all).Str → W → Prop) (Q : Places D all S₁ S₂ S₃ W)
    (hT : EachTied (Fr := frameAt D all D.key₁ T.ft₁) N Mg links ps get 0 (T.p₁ :: T.l₁))
    (hs : TieStart T.ft₁ N Mg links ps get R₀) :
    EachGoodIn (placesM T.ft₁ N Mg links ps get R₀ Q).on₁
      (placesM T.ft₁ N Mg links ps get R₀ Q).R₁ 0 (T.p₁ :: T.l₁) :=
  eachGoodInFront S₁ Cl W C (frameAt D all D.key₁ T.ft₁) _ _ R₀ T.p₁ T.l₁ hs
    (chainOfPromises N Mg links ps get (T.p₁ :: T.l₁) 0 hT)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.firstChainMeans_of_tied
