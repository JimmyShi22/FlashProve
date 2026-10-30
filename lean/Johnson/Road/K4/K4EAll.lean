-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4EAll.lean: THE STRUCK PARTS' DATA E OF THE WIDER MEANING (`WideData`,
Johnson/Desc/Sound/MgWide.lean) AS A TERM OFF THE PROOF FILE's PUBLIC PART, beside the composed
meaning's closed parameters (the structure written out in Johnson/P5J/LettersAll.lean): each field
is its own authors' term. A definition and seven equations by rfl.

  `eAll Zp cF L`: d12 := the closed parameters' own `At.d12 Zp L` (ft := 0 · the laid list L, handed
    in · the chain's messages' shapes) · dP := the pending claim on the weights' authors' three: tl
    := `FillP1.tlAt Zp` · fvs := `FillP1.fvsAt Zp` · free0 := `FillP1.free0Of` at the closed code
    table, these shapes and the closed numbers' index of the index masks' message · reqW :=
    `At.reqW`.
  `eAll_ft` · `eAll_L` · `eAll_M` · `eAll_tl` · `eAll_fvs` · `eAll_free0` · `eAll_reqW`: what each
  field is.

WHY. E was a free letter: at a wrong E (tl m = none; fvs := []) no unmarked state is inside the
promise at the wider meaning, or a test on E asks too little.

Limits. L IS HANDED IN: the closed parameters' test laidB says that there is one. Definitions:
nothing is shown of any state. THE WIDER MEANING IS A BRIDGE's SIDE. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Desc.Sound.MgWide
import Johnson.P5J.LettersAt2
import Johnson.Top.H0.Fill.D1At

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open VerifiableInference.Desc.First (FillP1.tlAt FillP1.fvsAt FillP1.free0Of)
open VerifiableInference.Desc.Sound (WideData)

variable (Zp : ProofFile.Pub) (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl)
  (L : VerifiableInference.Desc.K12.Door.Laid)

/-- **The struck parts' data, as a term.** -/
def eAll : WideData ProofFile.InstPub where
  d12 := P5J.At.d12 Zp L
  dP :=
    { tl := FillP1.tlAt Zp
      fvs := FillP1.fvsAt Zp
      free0 := FillP1.free0Of (P5J.At.cs Zp) (P5J.At.d12 Zp L).M (P5J.At.N Zp cF).indexNo }
  reqW := P5J.At.reqW

theorem eAll_ft : (eAll Zp cF L).d12.ft = 0 := rfl

theorem eAll_L : (eAll Zp cF L).d12.L = L := rfl

theorem eAll_M : (eAll Zp cF L).d12.M = (P5J.At.d12 Zp L).M := rfl

theorem eAll_tl : (eAll Zp cF L).dP.tl = FillP1.tlAt Zp := rfl

theorem eAll_fvs : (eAll Zp cF L).dP.fvs = FillP1.fvsAt Zp := rfl

theorem eAll_free0 : (eAll Zp cF L).dP.free0 =
    FillP1.free0Of (P5J.At.cs Zp) (eAll Zp cF L).d12.M (P5J.At.N Zp cF).indexNo := rfl

theorem eAll_reqW : (eAll Zp cF L).reqW = P5J.At.reqW := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.eAll_free0
