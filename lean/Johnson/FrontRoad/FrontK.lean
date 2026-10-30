-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FrontK.lean: the scheme of Front.lean with any form of key and proof, and the
statement that index privacy passes to it under the premises of Spec.frontPrivacy. Conditional, of a
shell. What is published is any function κ of the commitment ID and the whole key, and a proof is
any function ϖ of the whole key and the proof of frontArg. Definitions and one statement; proved in
FrontProof.lean.
Terms and the limits that go with any quote: Spec.lean.

What this file has.
  frontWrapK   the one re-packing of Front.lean, with κ on (ID, whole key) and ϖ on (whole key,
               proof).
  frontArgK    the scheme: committer and prover as that re-packing prescribes. The prover's key
               holds the whole key too, since ϖ reads it. The verifier is a variable.
  frontSimK    the simulator, an explicit term.
  Spec.frontPrivacyK
               Under exactly the premises of Spec.frontPrivacy (Spec.lean, "What is required"):
               ZKCP.HasStrongIndexPrivacyWith for Rel, frontArgK and frontSimK, at all indices of J,
               with the bound ζ at one query more. Nothing is required of κ and ϖ.
At κ := the pair and ϖ := the proof itself this is frontArg, except for the prover's key, which is
not in the adversary's view (by inspection, not proved). At κ := the ID alone and ϖ := an encoding
of (root key, root proof), the key is a commitment and a proof is a form, as in the library's
system. It is not that system: the prover's key differs, and committer and prover are this folder's,
not the description's own (FrontId.lean, Limits). κ and ϖ are not given the told part of d, which
the re-packing drops.

Why. The statements of Spec.lean are at typed keys and proofs. A scheme on byte strings publishes
encodings: of the key's parts, and of a proof together with the key's entry for the copy that the
proof names. An encoding that queries no oracle is a function of what was published before. A
re-packing takes any function for the outer key, and any function of inner key and inner proof for
an outer proof. So encodings come in at the step of frontWrap (Front.lean), with the same added
error.

Limits. All that Spec.lean lists under "What must go with any quote of it", among it that the public
parameters are variables: where the public parameter is the index the statement says nothing. And:
that a parser inverts an encoding is needed for completeness, not here. A κ or ϖ that discards
everything satisfies this statement.
-/
import Johnson.FrontRoad.Front

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
  {J K' P' : Type} (idx : J → R.Index) (x₀ : R.Instance) (back : R.Instance → List Token × List Token)
  (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
  (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')

/-- The one re-packing of Front.lean with any form of key and proof: the outer key is κ of the
commitment ID and the whole key, and an outer proof is ϖ of the whole key and the inner proof. -/
def frontWrapK : ZKCP.Wrap 256 (KeyT R) R.Instance Unit (RequestProof 256 R.protocol) K' (List Token × List Token) Unit
    P' where
  ask := fun ck => T.encT (ck.1, lowKey ck.2)
  key := fun ck a => κ (a.getD fun _ => false) ck.2
  proof := fun ck π => ϖ ck.2 π
  inst := instOf R x₀
  wit := id
  back := back

/-- The scheme. The committer is that of frontArg, but publishes κ of (ID, whole key) and puts the
whole key into the prover's key. The prover applies ϖ, at that whole key, to the proof of readOne.
The verifier is the variable Vf. -/
def frontArgK (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool) :
    ZKCP.Arg 256 J (List Token × List Token) Unit K'
      (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits × (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) P' where
  C := fun w => ((readOne T h).C (idx w)).bind fun keys =>
    (ZKCP.keyDigest (fun ck : KeyT R => T.encT (ck.1, lowKey ck.2)) keys.1).mapO fun dg =>
      (κ dg keys.1.2, (keys.1.2, keys.2))
  P := fun isk x' _ => ((readOne T h).P isk.2 (instOf R x₀ x') ()).mapO (ϖ isk.1)
  V := Vf

variable {PP PP' : Type}

/-- The simulator for frontArgK: the simulator of frontWrapK (ZKCP.Wrap.sim) over readSim
(Front.lean). -/
def frontSimK (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol)) (hp : PP' → PP) :
    ZKCP.Simulator 256 PP' K' (List Token × List Token) P' :=
  (frontWrapK T x₀ back κ ϖ).sim (ZKCP.Special.simOf (readSim T Sim)) hp

/-- Under the premises of Spec.frontPrivacy (Spec.lean), for all κ and ϖ:
ZKCP.HasStrongIndexPrivacyWith for Rel, frontArgK and frontSimK, with the bound ζ at one query more.
Conditional, of a shell. Statement only; proved as frontPrivacyK in FrontProof.lean. -/
def Spec.frontPrivacyK : Prop :=
  ∀ (R : InnerCompilerInput) (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (J K' P' PP PP' : Type) (idx : J → R.Index) (x₀ : R.Instance) (back : R.Instance → List Token × List Token)
    (κ : ZKCP.Digest 256 → FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → K')
    (ϖ : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits → RequestProof 256 R.protocol → P')
    (Vf : K' → List Token × List Token → P' → ZKCP.OComp 256 Bool)
    (R₁ : ZKCP.IndexedRelation R.Index R.Instance Unit PP)
    (Rel : ZKCP.IndexedRelation J (List Token × List Token) Unit PP') (hp : PP' → PP)
    (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
      (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol))
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : R.Index → Prop),
    T.Pub.NoCoin → (T.Pub.AsksIn fun _ s => T.Pt s) → NoRepeat T.Pub →
    (∀ d s, T.Pt s → IsOther (T.m d) s) →
    (∀ d, ZKCP.Gen.PrivacyOn (ZKCP.Special.toPair R₁) (typedAt T h d) 1 (Sim d) ζ ok) →
    (∀ w, ok (idx w)) → (∀ w, R₁.pp (idx w) = hp (Rel.pp w)) →
    (∀ w x', Rel.rel w x' () →
      R₁.rel (idx w) (instOf R x₀ x') () ∧ back (instOf R x₀ x') = x') →
    ZKCP.HasStrongIndexPrivacyWith Rel (frontArgK T h idx x₀ κ ϖ Vf)
      (frontSimK T x₀ back κ ϖ Sim hp) fun t N => ζ (t + 1) N

end OnBytes.FrontRoad
