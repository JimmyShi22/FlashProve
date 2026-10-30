-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide2/ExtIn.lean: A POSITION OF AN EXTERNAL STRING STANDS AT A LEAF THAT A TABLE's TREE
HAS (ExtIn, Johnson/LateSide/Good.lean): it follows from the wires' laws.

General lemmas. This file states no goal of the release.

The wires' laws (OKA, Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean; QueryLayout.OKG, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean)
say that position p of an encoded index stands at leaf number p of its tree, and that the word's
length is at most 2 ^ depth. So ExtIn is no premise of its own.

-/
import Johnson.LateSide.Good

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

theorem extIn_of_okg {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} (h : W.OKG) : ExtIn W where
  T := fun p => by
    have e : (wTC W).ext.leaf p = p.val := (h.extT p).2
    rw [e]
    exact lt_of_lt_of_le p.isLt h.fits
  Lk := fun p => by
    cases p with
    | inl p =>
        have e : (wLC W).ext.leaf (.inl p) = p.val := (h.extL.1 p).2
        rw [e]
        exact lt_of_lt_of_le p.isLt h.fits
    | inr p =>
        have e : (wLC W).ext.leaf (.inr p) = p.val := (h.extL.2 p).2
        rw [e]
        exact lt_of_lt_of_le p.isLt h.fits
  B := fun p => by
    have e : (wBC W).ext.leaf p = p.val := (h.extB p).2
    rw [e]
    exact lt_of_lt_of_le p.isLt h.fits

theorem extIn_of_oka {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    (h : OKA W cA) : ExtIn W := extIn_of_okg h.base

end OnBytes.LateSide

#print axioms OnBytes.LateSide.extIn_of_oka
