-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/FrontRootSide.lean: copies of the key `KeyRoot` and the proof `OfflineLinkOnlineProof` of
Johnson/TypedOracleCompiler/RecCompile/FrontRoot.lean, and of `KeyRoot.full` and `OfflineLinkOnlineProof.low`, typed over the
verifier's side of the object (`LHV`: Hiop/RecSide.lean says what that is and why it is there).

Main names: `KeyRootV`, `PrfRootV`, `KeyRoot.v`, `OfflineLinkOnlineProof.v`, `KeyRootV.full`, `PrfRootV.low`.
The ties stand in Johnson/TypedOracleCompiler/RecCompile/SideTies.lean: field by field, the maps back,
`KeyRoot.full_v`, `OfflineLinkOnlineProof.low_v`.
Limits: definitions alone. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot
import Johnson.TypedOracleCompiler.RecCompile.CmsSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- The key: the root of the first encoded index, and its record. -/
structure KeyRootV (lam : ℕ) (L : LHV X) where
  cm : Dig lam
  rcd : L.Rec

/-- A proof: the test's proof on the first encoded index, one further encoded index (root, record,
link), the session's proof. -/
structure PrfRootV (lam : ℕ) (L : LHV X) (aT : RoundSplits L.test.shape) (aL : RoundSplits L.link.shape) where
  /-- the number of the stored copy -/
  copy : ℕ
  piT : Option (OneProtocolProof lam (batTV L aT))
  link : Dig lam × L.Rec × Option (OneProtocolProof lam (batLV L aL))
  piB : Option (OneProtocolProof lam L.bat)

/-- The record at the object's verifier's side, field by field. -/
@[reducible] def KeyRoot.v {L : HolographicProtocol I X} (k : KeyRoot lam L) :
    KeyRootV lam L.v where
  cm := k.cm
  rcd := k.rcd

/-- The record at the object's verifier's side, field by field. -/
@[reducible] def OfflineLinkOnlineProof.v {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) :
    PrfRootV lam L.v aT aL where
  copy := π.copy
  piT := π.piT
  link := π.link
  piB := π.piB

section RunV

variable {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape} {aL : RoundSplits L.link.shape}

/-- CmsSide.lean's key, put together from the key and the proof. -/
def KeyRootV.full (k : KeyRootV lam L) (π : PrfRootV lam L aT aL) : KeyCV lam L aT aL :=
    ⟨k.cm, k.rcd, π.piT, [π.link]⟩

/-- CmsSide.lean's proof: the one link, the session's proof. -/
def PrfRootV.low (π : PrfRootV lam L aT aL) : PrfCV lam L := ⟨0, π.copy, π.piB⟩

end RunV

end TypedOracleCompiler.Compile.Batch.Cms
