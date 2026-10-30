-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/CmsSide.lean: copies of `wTC`, `wLC`, `wBC` (Johnson/TypedOracleCompiler/RecCompile/Cms.lean)
and of the records `FullKey`, `RequestProof`, typed over the verifier's side of the object (`LHV`:
Hiop/RecSide.lean says what that is and why it is there).

Main names: `KeyCV`, `PrfCV`, `FullKey.v`, `RequestProof.v`, `wTCV`, `wLCV`, `wBCV`.
The ties (`wTC_v`, `wLC_v`, `wBC_v`): each of these at L equals its copy here at `L.v`, at every
argument. If one of the two copies is changed alone, this file no longer compiles: do not drop the
ties in a clean-up.
Limits: definitions and these equations. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.Cms
import Johnson.TypedOracleCompiler.RecCompile.SeedsSide

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- The key. -/
structure KeyCV (lam : ℕ) (L : LHV X) (aT : RoundSplits L.test.shape) (aL : RoundSplits L.link.shape) where
  cm : Dig lam
  rcd : L.Rec
  piT : Option (OneProtocolProof lam (batTV L aT))
  links : List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLV L aL)))

/-- A proof. -/
structure PrfCV (lam : ℕ) (L : LHV X) where
  /-- the place of the entry in the key's list -/
  leaf : ℕ
  /-- the number of the stored copy, as the session's chain takes it in. The number tested is the
  prover's free choice, tied to the entry picked by nothing. -/
  copy : ℕ
  piB : Option (OneProtocolProof lam L.bat)

/-- The record at the object's verifier's side, field by field. -/
@[reducible] def FullKey.v {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : FullKey lam L aT aL) :
    KeyCV lam L.v aT aL where
  cm := k.cm
  rcd := k.rcd
  piT := k.piT
  links := k.links

/-- The record at the object's verifier's side, field by field. -/
@[reducible] def RequestProof.v {L : HolographicProtocol I X} (π : RequestProof lam L) :
    PrfCV lam L.v where
  leaf := π.leaf
  copy := π.copy
  piB := π.piB

section RunV

variable {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (carrierV L Bd aT aL)) (S : SeedV lam W.K L Bd aT aL)

def wTCV : ProtocolQueryLayout lam W.K (batTV L aT) :=
  ⟨W.T.sh, W.T.ext, W.T.decO, W.T.nOpen, W.T.maxDepth⟩

def wLCV : ProtocolQueryLayout lam W.K (batLV L aL) :=
  ⟨W.Lk.sh, W.Lk.ext, W.Lk.decO, W.Lk.nOpen, W.Lk.maxDepth⟩

def wBCV : ProtocolQueryLayout lam W.K L.bat := ⟨W.B.sh, W.B.ext, W.B.decO, W.B.nOpen, W.B.maxDepth⟩

end RunV

/-! ## The ties -/

section Ties

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

theorem wTC_v : wTC W = wTCV (L := L.v) W := rfl

theorem wLC_v : wLC W = wLCV (L := L.v) W := rfl

theorem wBC_v : wBC W = wBCV (L := L.v) W := rfl

end Ties

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.wTC_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.wLC_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.wBC_v
