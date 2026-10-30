-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/Front.lean: definitions only: the scheme with the whole key published, changed so
that it is over one hash function, reads its parameters off that function, has the commitment ID
in front of its key, takes its index through a map from another type of indices, and has prompts
with output tokens as instances.
Terms and the limits that go with any quote: Spec.lean.

What this file has. The family T, the honest sides h, the map idx of indices and the verifier Vf are
variables. The steps, from the lowest:
  toldAt T h d   the scheme at d over one hash function (wholeAt, Johnson/PublicAt/Whole.lean) with
                 the told part of d put in front of its key (mapKeyArg, MapKey.lean). The told part
                 is LayoutsByPublicReading.part, and the code of a key is LayoutsByPublicReading.encT
                 (Johnson/Top/InnerCompiledVerifierByPublicReading.lean).
  readTold T h   the public reading, then toldAt at the value d that it returns (glueArg,
                 ZKCP/PublicRead/Spec.lean).
  readOne T h    the same as a ZKCP.Arg (ZKCP/Defs.lean): one hash function, one request a call.
  frontWrap      one re-packing that does all the rest. The committer queries the hash function once
                 more, at the code of (told part, root and out-of-domain sample); the answer is the
                 commitment ID. The published key is the ID and the whole key, and the told part is
                 dropped. A prompt with output tokens is built into an instance, with no further
                 tokens.
  frontArg       the scheme: committer and prover as that re-packing prescribes, at the index idx w.
                 The verifier is the variable Vf, which index privacy does not read.
  frontSim       the simulator, an explicit term made of the simulators at d over the typed oracles.

Why the told part goes in before the public reading, and the ID after it. The query for the ID
depends on d only through the told part: the code encT is one function for all d. Added in a later
step than the reading, that query need not satisfy the premise "the committer queries no public
string". A re-packing's further query can read only the inner key, so the told part must be in it.

Limits. Definitions: nothing on hiding, completeness or binding is proved here.
-/
import Johnson.PublicAt.Whole
import Johnson.FrontRoad.MapKey
import ZKCP.PrivacyWrap

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The key of toldAt: the told part, then the whole key. -/
abbrev KeyT (R : InnerCompilerInput) : Type := Dig 256 × FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits

/-- The key of frontArg: the commitment ID, then the whole key. -/
abbrev KeyF (R : InnerCompilerInput) : Type := ZKCP.Digest 256 × FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)

/-- The scheme at d over one hash function, with the told part of d in front of its key. Its
verifier tests that the key's first component is the told part of d, and then runs the verifier at
d. -/
def toldAt (d : T.D) : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (KeyT R) (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  mapKeyArg (wholeAt T h d) (fun k => (T.part d, k)) fun ck x π =>
    if ck.1 = T.part d then (wholeAt T h d).V ck.2 x π else .pure false

/-- The public reading, then toldAt at the value d that it returns. The prover's key holds d. -/
def readTold : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (KeyT R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  glueArg T.Pub (toldAt T h)

/-- readTold as a ZKCP.Arg (ZKCP/Defs.lean): one hash function, one request a call. -/
def readOne : ZKCP.Arg 256 R.Index R.Instance Unit (KeyT R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (RequestProof 256 R.protocol) :=
  ZKCP.SpecialAny.oneOf (readTold T h)

variable {J : Type} (idx : J → R.Index) (x₀ : R.Instance) (back : R.Instance → List Token × List Token)

/-- The instance that R.buildInstance makes from a prompt with output tokens and no further tokens; the
default x₀ where R.buildInstance returns none. -/
def instOf (R : InnerCompilerInput) (x₀ : R.Instance) (x' : List Token × List Token) : R.Instance :=
  (R.buildInstance x' []).getD x₀

/-- The one re-packing (ZKCP.Wrap). The further query is at the code of (told part, root and
out-of-domain sample). The outer key is the answer, which is the commitment ID, with the whole key;
for a key without a code the ID is the all-zero digest. Proofs and witnesses are unchanged, and
instances are built by instOf. -/
def frontWrap : ZKCP.Wrap 256 (KeyT R) R.Instance Unit (RequestProof 256 R.protocol) (KeyF R) (List Token × List Token)
    Unit (RequestProof 256 R.protocol) where
  ask := fun ck => T.encT (ck.1, lowKey ck.2)
  key := fun ck a => (a.getD fun _ => false, ck.2)
  proof := fun _ π => π
  inst := instOf R x₀
  wit := id
  back := back

/-- The scheme. The committer runs that of readOne at the index idx w, queries the hash function for
the commitment ID, and publishes the ID with the whole key. The prover is that of readOne at the
instance instOf R x₀ x'. The verifier is the variable Vf. -/
def frontArg (Vf : KeyF R → List Token × List Token → RequestProof 256 R.protocol → ZKCP.OComp 256 Bool) :
    ZKCP.Arg 256 J (List Token × List Token) Unit (KeyF R) (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
      (RequestProof 256 R.protocol) where
  C := fun w => ((readOne T h).C (idx w)).bind fun keys =>
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
      ((dg, keys.1.2), keys.2)
  P := fun isk x' _ => (readOne T h).P isk (instOf R x₀ x') ()
  V := Vf

variable {PP PP' : Type}

/-- The simulator for readTold. It samples the answers to the public reading's queries itself and
runs the simulator at the resulting d, through the coding at d, with the told part in front of its
key. A query at one of the reading's strings gets the sampled answer; every other query is answered
by that simulator. -/
def readSim (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol)) :
    ZKCP.Gen.Simulator (rom 256) PP (KeyT R) R.Instance (RequestProof 256 R.protocol) :=
  glueSim T.Pub fun d => mapKeySim (simOne (T.m d) (Sim d)) fun k => (T.part d, k)

/-- The simulator for frontArg: the simulator of frontWrap (ZKCP.Wrap.sim) over readSim, with one
request a call. It passes hp of the public parameter that it is given on to readSim. -/
def frontSim (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol)) (hp : PP' → PP) :
    ZKCP.Simulator 256 PP' (KeyF R) (List Token × List Token) (RequestProof 256 R.protocol) :=
  (frontWrap T x₀ back).sim (ZKCP.Special.simOf (readSim T Sim)) hp

end OnBytes.FrontRoad
