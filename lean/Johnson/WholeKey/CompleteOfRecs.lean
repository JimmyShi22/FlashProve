-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/WholeKey/CompleteOfRecs.lean: TWO OF THE PREMISES OF complete_argW
(Johnson/WholeKey/Complete.lean) AT STRATEGIES AND STOPS THAT ARE READ OFF THE THREE STRUCTURES OF
AN HONEST PROVER (ThreeProvers, Johnson/Prover/All/OfHonest.lean; Plays.ofRecs,
Johnson/WholeKey/OfRecs.lean): StopsIn holds by the stops' make; AccLaws follows from HonFit
(Johnson/Prover/All/OfHonest.lean). The sets are the three structures' own with the falls at the
sample's coins (ThreeProvers.bads): a stop decides a withheld set alone, and reads no fall.

Main names (namespace OnBytes.WholeKey).
  badsOf   the family of sets: ThreeProvers.bads at the sample's encoding randomness, number and coins.
  stopsIn_ofRecs   StopsIn, with no premise.
  accLaws_of_honFit   AccLaws at the three structures' strategies, from HonFit.
  complete_of_honFit   THE JOIN: HonFit, LawFit, WiresFit, SideFit give the library's constant at
    every honest side whose strategies are Plays.ofRecs Hs dc ((Plays.ofRecs Hs dc).joint is
    Hs.strats by unfolding: ofRecs_joint). No honest side is defined here.

Limits. HonFit is a premise: its one member that is shown is idle (Johnson/Prover/At/IdleAt.lean).
LawFit, WiresFit and SideFit stay premises. Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Complete
import Johnson.WholeKey.OfRecs

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (Hs : ThreeProvers L) (F : Falls Hs)

/-- The three structures' sets, as a family in the sample. -/
def badsOf (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (i : I) (r₁ : L.EncodingRandomness) (x : X)
    (d : Draw lam L Bd aT aL (Hs.T.Coin × Hs.Lk.Coin × Hs.B.Coin)) : Bads L :=
  Hs.bads F Z i r₁ d.r x d.n d.κ

/-- **The stops that decide the three structures' withheld sets lie in their sets.** -/
theorem stopsIn_ofRecs (dc : Decs Hs) (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed) :
    StopsIn (Plays.ofRecs Hs dc)
      (badsOf (lam := lam) (Bd := Bd) (aT := aT) (aL := aL) Hs F Z) where
  T := fun i r₁ _ _ e ρ hs =>
    Or.inl (@of_decide_eq_true _ (dc.T (i, r₁, e) (L.recOf i r₁ e) ρ) hs)
  Lk := fun i r₁ _ d e e' ρ hs => Or.inl
    (@of_decide_eq_true _ (dc.Lk (i, (r₁, e), (d.r, e')) (L.recOf i r₁ e, L.recOf i d.r e') ρ) hs)
  B := fun i _ x d e ρ hs =>
    Or.inl (@of_decide_eq_true _ (dc.B (i, d.r, e, d.n) (x, L.recOf i d.r e) ρ) hs)

/-- **The accept laws at all coins, from the conditional form at the three structures.** -/
theorem accLaws_of_honFit {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {Yes : I → X → Prop} {Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (hf : HonFit Hs F W S Yes Z ζ pT pL pO) :
    AccLaws W S Hs.strats Yes (badsOf Hs F Z) ζ ζ pT pL pO where
  acc := fun i r₁ x d hY => accAt_of_honest hf i r₁ x d hY
  small := fun i r₁ x d hY => small_of_honest hf i r₁ d.r x d.n d.κ hY

/-- **THE JOIN: completeness of the scheme with the whole key at the three structures of an honest
prover**, from the conditional form at them and the premises on wires and lengths: at EVERY honest
side whose strategies, with the types of their coins, are those read off them (hst: at a side that
is made so, by unfolding). -/
theorem complete_of_honFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
    (dc : Decs Hs)
    (hst : (⟨h.KT, h.KL, h.KB, h.st⟩ : Σ KT : Type, Σ KL : Type, Σ KB : Type, Plays L KT KL KB) =
      ⟨Hs.T.Coin, Hs.Lk.Coin, Hs.B.Coin, Plays.ofRecs Hs dc⟩)
    {Yes : I → X → Prop} {Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (hf : HonFit Hs F W S Yes Z ζ pT pL pO) (hL : LawFit W S h.capT h.capL h.capB)
    (hW : WiresFit W cA) (hF : SideFit W p h) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (argW W S cA r₀ p h) 1 (alphaAll W h.capT h.capL h.capB ζ ζ pT pL pO) := by
  cases h
  cases hst
  refine complete_argW W S cA r₀ p _ Yes
    (badsOf (lam := lam) (Bd := Bd) (aT := aT) (aL := aL) Hs F Z) hL hW hF ?_ ?_
  · exact accLaws_of_honFit Hs F hf
  · exact stopsIn_ofRecs Hs F dc Z

end OnBytes.WholeKey
