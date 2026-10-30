-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/SideTies.lean: the five records over an object (`OutOfDomainSampleQueryLayout`, `FullKey`, `RequestProof`,
`KeyRoot`, `OfflineLinkOnlineProof`) and their forms at the object's verifier's side, field by field, with the maps
back.

Each `‹R›.v` lays the fields of a record into its form at `L.v`. The statements here say, each by
unfolding, that every field is the record's own; that `‹R›.ofV` leads back, with both round trips;
and that `KeyRoot.full` and `OfflineLinkOnlineProof.low` agree with their namesakes at the verifier's side.

They keep the two texts one: if a field changes on one side alone, this file no longer compiles. A
clean-up that drops them as unused would lose the check.

Main names: `‹R›.v_‹field›` (22); `‹R›.ofV`, `‹R›.ofV_v`, `‹R›.v_ofV` (five each); `KeyRoot.full_v`,
`OfflineLinkOnlineProof.low_v`.
Limits. Nothing else is proved here. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRootSide

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ}

/-! `OutOfDomainSampleQueryLayout.v`, field by field. -/

theorem OutOfDomainSampleQueryLayout.v_t {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.t = S.t := rfl

theorem OutOfDomainSampleQueryLayout.v_cfg {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.cfg = S.cfg := rfl

theorem OutOfDomainSampleQueryLayout.v_shape {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.shape = S.shape := rfl

theorem OutOfDomainSampleQueryLayout.v_pl0 {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.pl0 = S.pl0 := rfl

theorem OutOfDomainSampleQueryLayout.v_pl1 {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.pl1 = S.pl1 := rfl

theorem OutOfDomainSampleQueryLayout.v_seed {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.seed = S.seed := rfl

theorem OutOfDomainSampleQueryLayout.v_code {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.code = S.code := rfl

theorem OutOfDomainSampleQueryLayout.v_num {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.num = S.num := rfl

theorem OutOfDomainSampleQueryLayout.v_decS {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    S.v.decS = S.decS := rfl

/-! `FullKey.v`, field by field. -/

theorem FullKey.v_cm {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : FullKey lam L aT aL) :
    k.v.cm = k.cm := rfl

theorem FullKey.v_rcd {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : FullKey lam L aT aL) :
    k.v.rcd = k.rcd := rfl

theorem FullKey.v_piT {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : FullKey lam L aT aL) :
    k.v.piT = k.piT := rfl

theorem FullKey.v_links {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : FullKey lam L aT aL) :
    k.v.links = k.links := rfl

/-! `RequestProof.v`, field by field. -/

theorem RequestProof.v_leaf {L : HolographicProtocol I X} (π : RequestProof lam L) :
    π.v.leaf = π.leaf := rfl

theorem RequestProof.v_copy {L : HolographicProtocol I X} (π : RequestProof lam L) :
    π.v.copy = π.copy := rfl

theorem RequestProof.v_piB {L : HolographicProtocol I X} (π : RequestProof lam L) :
    π.v.piB = π.piB := rfl

/-! `KeyRoot.v`, field by field. -/

theorem KeyRoot.v_cm {L : HolographicProtocol I X} (k : KeyRoot lam L) :
    k.v.cm = k.cm := rfl

theorem KeyRoot.v_rcd {L : HolographicProtocol I X} (k : KeyRoot lam L) :
    k.v.rcd = k.rcd := rfl

/-! `OfflineLinkOnlineProof.v`, field by field. -/

theorem OfflineLinkOnlineProof.v_copy {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) :
    π.v.copy = π.copy := rfl

theorem OfflineLinkOnlineProof.v_piT {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) :
    π.v.piT = π.piT := rfl

theorem OfflineLinkOnlineProof.v_link {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) :
    π.v.link = π.link := rfl

theorem OfflineLinkOnlineProof.v_piB {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) :
    π.v.piB = π.piB := rfl

/-! The maps back, field by field, and both round trips: every record at the verifier's side is the
image of one at the object. -/

/-- The way back from `SeedV`, field by field. -/
@[reducible] def OutOfDomainSampleQueryLayout.ofV {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : SeedV lam K L.v Bd aT aL) : OutOfDomainSampleQueryLayout lam K L Bd aT aL where
  t := S.t
  cfg := S.cfg
  shape := S.shape
  pl0 := S.pl0
  pl1 := S.pl1
  seed := S.seed
  code := S.code
  num := S.num
  decS := S.decS

theorem OutOfDomainSampleQueryLayout.ofV_v {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) : OutOfDomainSampleQueryLayout.ofV S.v = S := rfl

theorem OutOfDomainSampleQueryLayout.v_ofV {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape}
    (S : SeedV lam K L.v Bd aT aL) : (OutOfDomainSampleQueryLayout.ofV S).v = S := rfl

/-- The way back from `KeyCV`, field by field. -/
@[reducible] def FullKey.ofV {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : KeyCV lam L.v aT aL) : FullKey lam L aT aL where
  cm := k.cm
  rcd := k.rcd
  piT := k.piT
  links := k.links

theorem FullKey.ofV_v {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : FullKey lam L aT aL) : FullKey.ofV k.v = k := rfl

theorem FullKey.v_ofV {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : KeyCV lam L.v aT aL) : (FullKey.ofV k).v = k := rfl

/-- The way back from `PrfCV`, field by field. -/
@[reducible] def RequestProof.ofV {L : HolographicProtocol I X}
    (π : PrfCV lam L.v) : RequestProof lam L where
  leaf := π.leaf
  copy := π.copy
  piB := π.piB

theorem RequestProof.ofV_v {L : HolographicProtocol I X}
    (π : RequestProof lam L) : RequestProof.ofV π.v = π := rfl

theorem RequestProof.v_ofV {L : HolographicProtocol I X}
    (π : PrfCV lam L.v) : (RequestProof.ofV π).v = π := rfl

/-- The way back from `KeyRootV`, field by field. -/
@[reducible] def KeyRoot.ofV {L : HolographicProtocol I X}
    (k : KeyRootV lam L.v) : KeyRoot lam L where
  cm := k.cm
  rcd := k.rcd

theorem KeyRoot.ofV_v {L : HolographicProtocol I X}
    (k : KeyRoot lam L) : KeyRoot.ofV k.v = k := rfl

theorem KeyRoot.v_ofV {L : HolographicProtocol I X}
    (k : KeyRootV lam L.v) : (KeyRoot.ofV k).v = k := rfl

/-- The way back from `PrfRootV`, field by field. -/
@[reducible] def OfflineLinkOnlineProof.ofV {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : PrfRootV lam L.v aT aL) : OfflineLinkOnlineProof lam L aT aL where
  copy := π.copy
  piT := π.piT
  link := π.link
  piB := π.piB

theorem OfflineLinkOnlineProof.ofV_v {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) : OfflineLinkOnlineProof.ofV π.v = π := rfl

theorem OfflineLinkOnlineProof.v_ofV {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : PrfRootV lam L.v aT aL) : (OfflineLinkOnlineProof.ofV π).v = π := rfl

/-! The two functions that return one of the five records stand in two texts. -/

theorem KeyRoot.full_v {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (k : KeyRoot lam L) (π : OfflineLinkOnlineProof lam L aT aL) : (k.full π).v = k.v.full π.v := rfl

theorem OfflineLinkOnlineProof.low_v {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    (π : OfflineLinkOnlineProof lam L aT aL) : π.low.v = π.v.low := rfl

end TypedOracleCompiler.Compile.Batch.Cms
