-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkAt.lean: the sub-protocol for equality of two encoded indices (the link) with its
closing, within a third of the distance; the first index decodes (the second regime).

Statements; the proofs are in Cb/Obj/LdObjectLinkAtProofs.lean.
The closing `Kc` is a group that holds all members of the family (`all`) and has a long position
(`neP`), a zero-evader and a whole test, with two numbers `L` and `t` (`LdLkP.Cl`,
Cb/Ld/LdLinkClose.lean).
`K.fullAt` (Cb/Obj/LdObjectLinkPairFull.lean) is the link with its closing at a pair of conditions
on the two encoded indices. By `Cf.Third` the index code has distance at least d (`Cf.C₀.d`); eM
(`Cf.eM`) is the radius of decoding, e₀ and e₁ (`K.e₀`, `K.e₁`) the radii at which the folds of the
two indices are tested.

Main names:
  `Spec.ldT3_link_far` (no hypothesis on lists or agreement, but the clause `ev` ("evades") of
    `S.Third dN`): `Cf.Third`; e₀ + eM < d (in place of e₀ ≤ eM); e₁ ≤ eM; the other hypotheses
    below (they are those of `ldT3_link`, Cb/Obj/LdObjectThirdTests.lean) ⇒ `Hiop.LinkListR` and
    `Hiop.LinkKnowR` (Hiop/RecSubs.lean) of the link with its closing, at ε₀ = 0, ε₁ = εThird e₁ and
    the pair `K.dec0` (the first index decodes with its record: Cb/Obj/LdObjectLinkPair.lean),
    `K.free` (the further one has no collision at its record's seed: Cb/Obj/LdObjectLink.lean).
  `Spec.ldT3e_link_far`: if every `S.L a` and `Kc.L` are 1, the errors in the order of the rounds,
    for any pair and any ε₀, ε₁: ε₀ + ε₁ + v q^(v-1) at γ; 0; 0; the locations; φ; the bridge; then
    the whole test's.
  In both statements `Fin Cf.C₀.n` is non-empty (instance binder).

Why the pair matters: if the first index decodes and e₀ + eM is below the distance, no point γ is
bad for its fold (`Spec.ldLk_foldErr`, Cb/Ld/LdLink.lean; proved in Cb/Ld/LdLinkProofs.lean), and
the radius e₀ at which its fold is tested may exceed eM, up to d - eM - 1. So fewer locations t₀
reach the same factor (n - e₀ - 1)^t₀ of the locations' error (`errLoc`, Cb/Ld/LdLink.lean: the
larger of two products). This is the pairing of this protocol's technical report (lean/CREDITS.md)
where 2 eM is below the distance.

Limits: what the heads of Cb/Obj/LdObjectLink.lean and Cb/Obj/LdObjectThirdTests.lean list as not
said is not said here either.
Two points of the second are excepted. The link's errors in the order of the rounds are stated here,
under its hypotheses (`Spec.ldT3e_link_far`). Of that head's "nothing beyond a third of the
distance": here the radius e₀ may exceed a third of the distance, up to d - eM - 1.
εThird e₁ keeps the summand for members of the list that violate the record.


Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectThirdErr
import Cb.Obj.LdObjectLinkPairFull

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The link with its closing, within a third, the first index by the second regime. -/
def ldT3_link_far : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (dN : K.P.N.O → ℕ)
      (Kc : K.P.Cl) (dG : ℕ) (d₂ : K.P.W2) (d : K.P.W0),
    Cf.Third → K.e₀ + Cf.eM < Cf.C₀.d → K.e₁ ≤ Cf.eM → Function.Injective K.pl → S.Third dN →
    Kc.G.Third dG → Kc.L = 1 → Kc.Z.OK → Kc.T.OK Kc.t → (∀ a, Kc.t ≤ S.t a) →
    LinkListR (C := Cf.conf) (K.link (K.fullAt K.dec0 K.free S 0 (Cf.εThird K.e₁) Kc d₂ d))
      (K.hLink (K.fullAt K.dec0 K.free S 0 (Cf.εThird K.e₁) Kc d₂ d))
      (K.nums (K.fullAt K.dec0 K.free S 0 (Cf.εThird K.e₁) Kc d₂ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.fullAt K.dec0 K.free S 0 (Cf.εThird K.e₁) Kc d₂ d))
      (K.nums (K.fullAt K.dec0 K.free S 0 (Cf.εThird K.e₁) Kc d₂ d)).err

/-- Its errors, in the order of the rounds. -/
def ldT3e_link_far : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
      (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0),
    (∀ a, S.L a = 1) → Kc.L = 1 →
    (K.nums (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)).err.toList =
      [K.P.errGam ε₀ ε₁, 0, 0, K.P.errLoc, K.P.errPhi, Kc.Z.err] ++ Kc.T.N.err.toList

end
end Spec
end Cb
