-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/SeedsSide.lean: copies of `seedQ0`, `seedQ1`, `outOfDomainSeedIs`
(Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) and of the record `OutOfDomainSampleQueryLayout`, typed over the verifier's side of the
object (`LHV`: Hiop/RecSide.lean says what that is and why it is there).

Main names: `SeedV`, `OutOfDomainSampleQueryLayout.v`, `seedQ0V`, `seedQ1V`, `seedIsV`.
The ties (`seedQ0_v`, `seedQ1_v`, `seedIs_v`): each of these at L equals its copy here at `L.v`, at
every argument. If one of the two copies is changed alone, this file no longer compiles: do not drop
the ties in a clean-up.
Limits: definitions and these equations. Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.Seeds
import Johnson.TypedOracleCompiler.RecCompile.CarrierSide

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- The wire of the record: the tag of the seeds' queries; what a table's name holds behind the
root; the fixed plain parts of the two queries; how K digests give a seed; how a record is written
as a list of digests; where a session's proof string holds the number of the stored copy. -/
structure SeedV (lam K : ℕ) (L : LHV X) (Bd : Type) (aT : RoundSplits L.test.shape)
    (aL : RoundSplits L.link.shape) where
  /-- the tag of the Fiat-Shamir oracle that gives the seeds: one for all tables -/
  t : Tag
  /-- the digests of a table's name behind the root -/
  cfg : List (Dig lam)
  /-- the rest of a table's name; it rides in the salt's field of the first query (F1) -/
  shape : Bits
  pl0 : PlainPart (shapeOf (carrierV L Bd aT aL) t) (annOf (carrierV L Bd aT aL) t)
  pl1 : PlainPart (shapeOf (carrierV L Bd aT aL) t) (annOf (carrierV L Bd aT aL) t)
  seed : (Fin K → Dig lam) → L.Seed
  code : L.Rec → List (Dig lam)
  /-- meant as: do the plain parts of a session's proof string hold this number of a stored copy, at
  the place where the first query of the session's chain takes it in? A letter; no law. -/
  num : ℕ → Plains L.bat.loc.shape → Bool
  /-- equality of seeds, as data: the verifier compares two seeds -/
  decS : DecidableEq L.Seed

/-- The record at the object's verifier's side, field by field. -/
@[reducible] def OutOfDomainSampleQueryLayout.v {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) :
    SeedV lam K L.v Bd aT aL where
  t := S.t
  cfg := S.cfg
  shape := S.shape
  pl0 := S.pl0
  pl1 := S.pl1
  seed := S.seed
  code := S.code
  num := S.num
  decS := S.decS

section RunV

variable {L : LHV X} {Bd : Type} {aT : RoundSplits L.test.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (carrierV L Bd aT aL)) (S : SeedV lam W.K L Bd aT aL)

/-- The first query of a seed: the table's name, with the root first. -/
def seedQ0V (cm : Dig lam) : FbIn lam (carrierV L Bd aT aL) S.t :=
  ⟨1, .f1 (cm :: S.cfg) none S.shape, [], S.pl0⟩

/-- The second query of a seed: the chain value of the first answer. -/
def seedQ1V (v : Bits) : FbIn lam (carrierV L Bd aT aL) S.t := ⟨2, .f2 none v, [], S.pl1⟩

/-- ask the two queries of the seed at the root cm; is the seed s? -/
def seedIsV (cm : Dig lam) (s : L.Seed) : TypedOracleComputation lam W.K (carrierV L Bd aT aL) Bool :=
  (OComp.ask (S := typedOracleFamily lam W.K (carrierV L Bd aT aL)) (OracleName.fb S.t)
    (seedQ0V W S cm)).bind fun a0 =>
    (OComp.ask (S := typedOracleFamily lam W.K (carrierV L Bd aT aL)) (OracleName.fb S.t)
      (seedQ1V W S (link (show FsAns lam W.K from a0)))).bind fun a1 =>
      OComp.pure (@decide _ (S.decS (S.seed (show FsAns lam W.K from a1).1) s))

end RunV

/-! ## The ties -/

section Ties

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

theorem seedQ0_v (cm : Dig lam) : seedQ0 W S cm = seedQ0V (L := L.v) W S.v cm := rfl

theorem seedQ1_v (v : Bits) : seedQ1 W S v = seedQ1V (L := L.v) W S.v v := rfl

theorem seedIs_v (cm : Dig lam) (s : L.OutOfDomainSeed) :
    outOfDomainSeedIs W S cm s = seedIsV (L := L.v) W S.v cm s := rfl

end Ties

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.seedQ0_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.seedQ1_v
#print axioms TypedOracleCompiler.Compile.Batch.Cms.seedIs_v
