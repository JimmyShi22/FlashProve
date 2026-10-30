-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/FitGivesSmall.lean: the yes of the one test on numbers (`sizeNumbersFitAtFullSize`, Johnson/Flat/Dec/FailsClosed.lean) gives the
three tests on data that a coding of the queries asks: `kindsAndWorkBelow256` (OnBytes/Maker/Page) of both whole files' data, at every depth of the
stored table, and K + 2 < 2^49. One theorem: `FrameFitFullD.three`; `frameFitFullD_three`: the same off the test's yes.
Limits: a law on tests on numbers. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.FailsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes.Maker

theorem FrameFitFullD.three {K v depthReq depthReqT : ℕ} {DK DP : WholeD}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    (h : FrameFitFullD K v depthReq depthReqT DK DP ds xs) (a : ℕ) :
    OnBytes.Maker.Page.kindsAndWorkBelow256 (DK.at a) = true ∧ OnBytes.Maker.Page.kindsAndWorkBelow256 (DP.at a) = true ∧
      K + 1 + 1 < 2 ^ 49 :=
  ⟨OnBytes.Maker.Page.smallD_of_work _ h.wK, OnBytes.Maker.Page.smallD_of_work _ h.wP, h.hK⟩

theorem frameFitFullD_three {K v depthReq depthReqT : ℕ} {DK DP : WholeD}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    (h : sizeNumbersFitAtFullSize K v depthReq depthReqT DK DP ds xs = true) (a : ℕ) :
    OnBytes.Maker.Page.kindsAndWorkBelow256 (DK.at a) = true ∧ OnBytes.Maker.Page.kindsAndWorkBelow256 (DP.at a) = true ∧
      K + 1 + 1 < 2 ^ 49 :=
  (frameFitFullD_parts h).three a

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.frameFitFullD_three
