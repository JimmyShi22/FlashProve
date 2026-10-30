-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeSeedsOut.lean: `SeedsOut S Gs δ` is a name for one inequality: the out-of-domain (OOD)
seed that the OOD-seed wire S (a `OutOfDomainSampleQueryLayout`, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) makes by its field
`seed` from K uniform digests lies outside the set Gs with probability at most δ. At K := `W.K` this
is the hypothesis hδ of `keyFive_of` (E2E/BridgeKeyFive.lean) and, at δ := `N.δ`, word for word the
clause `seeds` of `OnBytes.WholeKey.PremW` (Johnson/WholeKey/Premises.lean). It is for files that
have this inequality as a hypothesis. General: L, K, S, Gs and δ are free parameters.

  `SeedsOut S Gs δ`: a definition: `pr (unif (Fin K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ`
  `keyFive_of_out`: `keyFive_of` with `SeedsOut S Gs δ` as its hypothesis hδ; its other hypotheses
    and its conclusion are unchanged
  `seedsOut_all`: `SeedsOut S (fun _ => True) 0`: where Gs is the set of all seeds, the inequality
    holds at δ := 0

This is a file of its own, with few imports: where much more is imported, Lean's search for an
instance in that inequality runs out of its budget; a file that writes `SeedsOut` makes no such
search.

By what. `keyFive_of_out` is `keyFive_of` at the same arguments: `SeedsOut S Gs δ` unfolds to hδ.
`seedsOut_all`: no digests give a seed outside the set of all seeds, and the empty set has
probability 0 (`pr_empty`, Prob/Count.lean).

Limits. A definition, a restatement, and one trivial value that meets the definition. At no other
set Gs is `SeedsOut` proved here, so no δ is shown to be small at any other set. `keyFive_of_out`
has all limits of `keyFive_of`: see the head of E2E/BridgeKeyFive.lean. No property of a protocol is
stated: nothing on completeness, soundness or hiding.
-/
import E2E.BridgeKeyFive

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.KeyBridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open AtPublicFiles.Bridge (KeyFive asideOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The seed that `S.seed` makes from K uniform digests is outside Gs with probability at most δ. -/
def SeedsOut {K : ℕ} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞) : Prop :=
  pr (unif (Fin K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ

/-- Where Gs is the set of all seeds, `SeedsOut` holds at δ := 0. -/
theorem seedsOut_all {K : ℕ} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) : SeedsOut S (fun _ => True) 0 := by
  have e : {u : Fin K → Dig lam | ¬ (fun _ => True) (S.seed u)} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ hu => hu trivial
  unfold SeedsOut
  rw [e, pr_empty]

/-- `keyFive_of` (E2E/BridgeKeyFive.lean) with `SeedsOut S Gs δ` as its hypothesis hδ. -/
theorem keyFive_of_out {hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {sim : SimT L} {Tied TiedM : TiedT L} {FT : FallT hT}
    {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {RV : Type} {pv : Plains L.offline.shape → RV}
    {rv : hT.Coin → RV} {okV : RV → Prop} {z zB pF : ℝ≥0∞}
    (h : Sentences hT W sim Tied TiedM FT ok Gs pv rv okV z zB pF)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) {Yes : I → X → Prop} {δ : ℝ≥0∞} (hy : ∀ i x, Yes i x → ok i)
    (hδ : SeedsOut S Gs δ) :
    KeyFive hT W (guardT hT (asideOf Gs) FT) (asideOf Gs) S Yes δ (zB + z + pF) :=
  keyFive_of h S hy hδ

end AtPublicFiles.KeyBridge

#print axioms AtPublicFiles.KeyBridge.seedsOut_all
#print axioms AtPublicFiles.KeyBridge.keyFive_of_out
#print axioms AtPublicFiles.KeyBridge.SeedsOut
