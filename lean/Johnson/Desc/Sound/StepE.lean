-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StepE.lean: THE KEY AND THE STEP OF THE SHARED CHAIN's LAWS IN THE PLAIN FORM FOR A BATCH, AT THE TABLE's OWN TERMS. Two definitions.
WHY. The two stood in Johnson/Desc/Sound/SharedChainLeadsBN.lean [not in this library], beside a statement (written as "def … : Prop"; never proved) whose premise "the front sub-protocol hands on its statement unchanged" is false at every real chain: that file is withdrawn. Other files spend these two definitions alone. Here they stand by themselves, word for word; the withdrawn statement and its two helpers are not carried over.
  keyE N p l k a: the key at border k: the acting part there: one type at all borders.
  stepE N Mg Pm Oc split p l E k a b: what the law of sub-protocol number k leads to: the promise behind holds; and every witness behind gives, by the named extractor E k, a witness in front.

Limits. Definitions. WHOEVER IMPORTS THIS FILE MUST NOT IMPORT SharedChainLeadsBN.lean BESIDE IT: the two names would stand twice. (SharedChainLeadsBN.lean is not in this library.)
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersSharedQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)
open VerifiableInference.Desc.Shared

section
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (E : ℕ → (P₁ × S₂) × Fr.E.Str → (P₁ × S₂) × Fr.E.Str → Wt → Wt)

/-- The key at border k: the acting part there. One type at all borders. -/
def keyE (k : ℕ) (a : (P₁ × S₂) × Fr.E.Str) :
    S₂ × (oneExternalString (2 ^ Fr.a) SgX).Str × (ℕ → ℕ → Option (List UInt64)) :=
  (actQ N p l k).2 a

/-- **What the law of sub-protocol number k leads to**: the promise behind holds; and every witness behind gives, by the
named extractor, a witness in front. -/
def stepE (k : ℕ) (a b : (P₁ × S₂) × Fr.E.Str) : Prop :=
  onQ₂ N Pm Oc split p l (k + 1) b ∧
    ∀ w, relQ₂ N Mg split p l (k + 1) b w → relQ₂ N Mg split p l k a (E k a b w)

end

end VerifiableInference.Desc.Sound
