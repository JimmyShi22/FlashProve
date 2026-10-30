-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FrontRun.lean: under every fixed hash function, the committer and the prover of
the schemes frontArg and frontArgK are those of the scheme readOne (Front.lean) with the re-packing
applied to what they output. Four equations between distributions, with their proofs; no premise.
Terms and the limits that go with any quote: Spec.lean.

What this file proves.
  run_C_frontArg, run_P_frontArg     at frontArg and frontWrap (Front.lean).
  run_C_frontArgK, run_P_frontArgK   at frontArgK and frontWrapK (FrontK.lean).
The outer committer's output is the inner committer's with the re-packing's key computed from it;
the outer prover's is the inner prover's with the re-packing's map on proofs. These are the two
premises hC and hP of the general step strongPrivacy_of_wrap (WrapAll.lean).

Limits. The equations say what the definitions say, in the form in which that step takes it. Nothing
on hiding, completeness or binding is said here.
-/
import Johnson.FrontRoad.FrontK
import ZKCP.DigestKey

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance) (back : R.Instance → List Token × List Token)

/-- Under every hash function f, the output of the committer of frontArg at w is that of the
committer of readOne at idx w, with the key of frontWrap computed from the inner key and from the
answer of f to the further query. -/
theorem run_C_frontArg
    (Vf : KeyF R → List Token × List Token → RequestProof 256 R.protocol → ZKCP.OComp 256 Bool) (w : J)
    (f : ZKCP.Oracle 256) :
    ((frontArg T h idx x₀ Vf).C w).run f =
      (((readOne T h).C (idx w)).run f).map fun keys =>
        ((frontWrap T x₀ back).key keys.1 (((frontWrap T x₀ back).ask keys.1).map f), keys.2) := by
  show (((readOne T h).C (idx w)).bind fun keys =>
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
      ((dg, keys.1.2), keys.2)).run f = _
  rw [ZKCP.run_bind]
  show _ = (((readOne T h).C (idx w)).run f).bind fun keys => PMF.pure _
  refine congrArg _ (funext fun keys => ?_)
  rw [ZKCP.OComp.run_mapO, ZKCP.run_keyDigest, PMF.pure_map]
  rfl

/-- Under every hash function, the prover of frontArg is the prover of readOne at the instance and
witness that frontWrap gives, with the map of frontWrap on proofs (the identity). -/
theorem run_P_frontArg
    (Vf : KeyF R → List Token × List Token → RequestProof 256 R.protocol → ZKCP.OComp 256 Bool)
    (f : ZKCP.Oracle 256) (keys : KeyT R × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (x' : List Token × List Token) (u : Unit) :
    ((frontArg T h idx x₀ Vf).P keys.2 x' u).run f =
      (((readOne T h).P keys.2 ((frontWrap T x₀ back).inst x') ((frontWrap T x₀ back).wit u)).run
        f).map ((frontWrap T x₀ back).proof keys.1) :=
  (PMF.map_id _).symm

variable (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')

/-- The same as run_C_frontArg for frontArgK and frontWrapK; the prover's key also holds the whole
key. -/
theorem run_C_frontArgK (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool) (w : J)
    (f : ZKCP.Oracle 256) :
    ((frontArgK T h idx x₀ κ ϖ Vf).C w).run f =
      (((readOne T h).C (idx w)).run f).map fun keys =>
        ((frontWrapK T x₀ back κ ϖ).key keys.1 (((frontWrapK T x₀ back κ ϖ).ask keys.1).map f),
          (keys.1.2, keys.2)) := by
  show (((readOne T h).C (idx w)).bind fun keys =>
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
      (κ dg keys.1.2, (keys.1.2, keys.2))).run f = _
  rw [ZKCP.run_bind]
  show _ = (((readOne T h).C (idx w)).run f).bind fun keys => PMF.pure _
  refine congrArg _ (funext fun keys => ?_)
  rw [ZKCP.OComp.run_mapO, ZKCP.run_keyDigest, PMF.pure_map]
  rfl

/-- The same as run_P_frontArg for frontArgK and frontWrapK, whose map on proofs is ϖ at the whole
key. -/
theorem run_P_frontArgK (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)
    (f : ZKCP.Oracle 256) (keys : KeyT R × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))
    (x' : List Token × List Token) (u : Unit) :
    ((frontArgK T h idx x₀ κ ϖ Vf).P (keys.1.2, keys.2) x' u).run f =
      (((readOne T h).P keys.2 ((frontWrapK T x₀ back κ ϖ).inst x')
        ((frontWrapK T x₀ back κ ϖ).wit u)).run f).map
          ((frontWrapK T x₀ back κ ϖ).proof keys.1) :=
  ZKCP.OComp.run_mapO f _ _

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.run_C_frontArg
#print axioms OnBytes.FrontRoad.run_P_frontArg
#print axioms OnBytes.FrontRoad.run_C_frontArgK
#print axioms OnBytes.FrontRoad.run_P_frontArgK
