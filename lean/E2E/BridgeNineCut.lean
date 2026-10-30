-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BridgeNineCut.lean: THE NINE CLAUSES OF `OnBytes.Prover.HonFit` THAT DO NOT READ THE SESSION's
PROVER (`NineFit`, E2E/BridgeAccept.lean), CUT IN TWO, in general letters: `KeyFive`: the five on
the key file's prover and on the measure of the OOD seeds that are set aside; `LinkFour`: the four
on the link's prover. Each clause in `NineFit`'s own words. `nineFit_of`: the five and the four are
the nine.

A file of its own, over E2E/BridgeAccept.lean alone: where much more is imported, Lean's search for
an instance in one of these clauses runs out of its budget.

Limits. Definitions and one theorem by projection. No member of `KeyFive` or of `LinkFour` is shown
here. No property is had.


-/
import E2E.BridgeAccept

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}
  (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
  {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
  (FT : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → hT.Coin → Set (Rho L.offline.shape))
  (FL : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → hL.Coin → Set (Rho L.link.shape))
  (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed)

/-- The five of the nine that do not read the link's prover, in `NineFit`'s own words. -/
structure KeyFive (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (Yes : I → X → Prop) (ζ pT : ℝ≥0∞) : Prop where
  extT : ∀ i r e, hT.ext (i, r, e) = L.encodeIndex i r
  whT : ∀ w x c ρ, RoundsQueryLayout.zero L.offline.shape aT (wTC W).sh ρ ∈ hT.withheld w x ∪ FT w x c →
    ρ ∈ hT.withheld w x ∪ FT w x c
  accT : ∀ i x r e c, Yes i x → e ∉ Z i r →
    AccLaw (batTC L aT) (wTC W) (L.recOf i r e) (hT.ext (i, r, e))
      (hT.strat (i, r, e) (L.recOf i r e) c)
      (hT.withheld (i, r, e) (L.recOf i r e) ∪ FT (i, r, e) (L.recOf i r e) c)
  prZ : ∀ i x r, Yes i x → pr (unif (Fin W.K → Dig lam)) {a | S.seed a ∈ Z i r} ≤ ζ
  prT : ∀ i x r e c, Yes i x →
    prRho (hT.withheld (i, r, e) (L.recOf i r e) ∪ FT (i, r, e) (L.recOf i r e) c) ≤ pT

/-- The four on the link's prover, in `NineFit`'s own words. -/
structure LinkFour (Yes : I → X → Prop) (pL : ℝ≥0∞) : Prop where
  extL : ∀ i r e r' e', hL.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')
  whL : ∀ w x c ρ, RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ hL.withheld w x ∪ FL w x c →
    ρ ∈ hL.withheld w x ∪ FL w x c
  accL : ∀ i x r e r' e' c, Yes i x → e ∉ Z i r → e' ∉ Z i r' → AccLaw (batLC L aL) (wLC W)
    (L.recOf i r e, L.recOf i r' e') (hL.ext (i, (r, e), (r', e')))
    (hL.strat (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c)
    (hL.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      FL (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c)
  prL : ∀ i x r e r' e' c, Yes i x →
    prRho (hL.withheld (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∪
      FL (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') c) ≤ pL

variable {hT hL W FT FL Z}

/-- The five and the four are the nine. -/
theorem nineFit_of {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {Yes : I → X → Prop} {ζ pT pL : ℝ≥0∞}
    (k : KeyFive hT W FT Z S Yes ζ pT) (l : LinkFour hL W FL Z Yes pL) :
    NineFit hT hL W FT FL Z S Yes ζ pT pL :=
  ⟨k.extT, l.extL, k.whT, l.whL, k.accT, l.accL, k.prZ, k.prT, l.prL⟩

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.nineFit_of
