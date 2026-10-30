-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FrontProof.lean: if the scheme with the whole key published has index privacy over
the typed oracles at every value d of the type T.D, whether or not the public reading can return it,
with one bound, and under the further premises of Spec.lean, "What is required", then index privacy
passes, at one query more, to the scheme that reads d off the hash function and publishes the
commitment ID with the whole key, or any function of the two. Conditional, of a shell. The proofs of
Spec.frontPrivacyK (FrontK.lean), Spec.frontPrivacy and Spec.frontPrivacyAt (Spec.lean).
Terms and the limits that go with any quote: Spec.lean.

What this file proves. The three statements are written out, with all that they require, in the two
files named.
  frontPrivacyK    Spec.frontPrivacyK: any form of key and proof.
  frontPrivacy     Spec.frontPrivacy: the typed key and proof.
  frontPrivacyAt   Spec.frontPrivacyAt: at the shell frontAt. frontAt is frontArg at one verifier,
                   so this is frontPrivacy at one more parameter.
  privacy_readTold, privacy_readOne   steps 1 to 4 below and step 5: readTold, readOne (Front.lean).

Limits. This is a bridge, not a result on hiding. None of the three theorems is one of the release's
goal statements; frontPrivacyAt could be read as one: it counts as none.
The only parameters at which this folder shows PremW at every d, under premises on public data
alone, which gives the main premise, have two placeholder provers, which send fixed messages
(premAll_laid, LaidAll.lean, at the built description with the number of the honest committer's
coins set anew: flashProveDescription.reBound b, AtHomeT.lean).
No honest side with the protocol's three provers (the key file's, the link's, the sessions') is
written.
The public parameters are variables: where the public parameter is the index the statement says
nothing (Spec.lean).
All that the heads of Spec.lean ("What must go with any quote of it") and FrontK.lean (Limits) say
of the statements holds of the theorems.

How the proof goes, one call each. Every bound is ζ until the last step, which gives ζ at one query
more.
  1. The premise: index privacy at every d over the typed oracles (typedAt).
  2. Over one hash function, through the coding at d: ZKCP.privacyOn_overOne (ZKCP/OnRange.lean).
  3. The told part of d into the key: privacyOn_mapKey (MapKey.lean).
  4. Across the public reading: ZKCP.PublicRead.privacy_pub (ZKCP/PublicRead/Privacy.lean), with
     asks_mapKey_C (MapKey.lean), wholeAt_C and wholeAt_P (Johnson/PublicAt/Whole.lean): committer
     and prover query no public string.
  5. One request a call: ZKCP.strongPrivacyOn_of_gen (ZKCP/OnRange.lean).
  6. The one re-packing: strongPrivacy_of_wrap (WrapAll.lean), with the equations of FrontRun.lean.
-/
import Johnson.FrontRoad.Spec
import Johnson.FrontRoad.FrontRun
import Johnson.FrontRoad.WrapAll

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Steps
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) {PP : Type}
  (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol))
  (ζ : ℕ → ℕ → ℝ≥0∞) (ok : R.Index → Prop)

/-- Under the four premises on the public reading: if index privacy (ZKCP.Gen.PrivacyOn) holds at
every d over the typed oracles, with the simulators Sim d and one bound ζ on the range ok, then it
holds of readTold, with the simulator readSim, at the same bound and range. -/
theorem privacy_readTold (Rl : ZKCP.Gen.RelPair R.Index R.Instance Unit PP) (B : ℕ) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.PrivacyOn Rl (typedAt T h d) B (Sim d) ζ ok) :
    ZKCP.Gen.PrivacyOn Rl (readTold T h) B (readSim T Sim) ζ ok :=
  privacy_pub 256 _ _ _ _ _ _ _ _ Rl (toldAt T h) _ B ζ ok T.Pt T.Pub noCoin asks once
    (fun d i => asks_mapKey_C (wholeAt T h d) _ _ _ i (wholeAt_C h spare d i))
    (wholeAt_P h spare)
    fun d => privacyOn_mapKey Rl (wholeAt T h d) B (simOne (T.m d) (Sim d)) ζ ok _ _
      (ZKCP.privacyOn_overOne (T.m d) Rl (typedAt T h d) B (Sim d) ζ ok (hA d))

/-- Under the same premises, at one request a call: ZKCP.StrongPrivacyOn holds of readOne, at the
same bound and range. -/
theorem privacy_readOne (R₁ : ZKCP.IndexedRelation R.Index R.Instance Unit PP) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.PrivacyOn (ZKCP.Special.toPair R₁) (typedAt T h d) 1 (Sim d) ζ ok) :
    ZKCP.StrongPrivacyOn R₁ (readOne T h) (ZKCP.Special.simOf (readSim T Sim)) ζ ok :=
  ZKCP.strongPrivacyOn_of_gen R₁ (ZKCP.SpecialAny.agrees_oneOf _) (readSim T Sim) ζ ok
    (privacy_readTold T h Sim ζ ok (ZKCP.Special.toPair R₁) 1 noCoin asks once spare hA)

end Steps

/-- Proof of Spec.frontPrivacyK (FrontK.lean). Under its premises index privacy passes to frontArgK,
with any form of key and proof, at one query more. Conditional, of a shell. -/
theorem frontPrivacyK : Spec.frontPrivacyK :=
  fun R T h _ _ _ _ _ idx x₀ back κ ϖ Vf R₁ Rel hp Sim ζ ok noCoin asks once spare hA hok hpp
      hrel =>
    strongPrivacy_of_wrap (frontWrapK T x₀ back κ ϖ) R₁ Rel (readOne T h)
      (frontArgK T h idx x₀ κ ϖ Vf) (ZKCP.Special.simOf (readSim T Sim)) ζ ok idx hp
      (fun keys => (keys.1.2, keys.2)) (fun w f => run_C_frontArgK T h idx x₀ back κ ϖ Vf w f)
      (fun f keys x' u => run_P_frontArgK T h idx x₀ back κ ϖ Vf f keys x' u) hpp
      (fun w x' u hr => by cases u; exact hrel w x' hr) hok
      (privacy_readOne T h Sim ζ ok R₁ noCoin asks once spare hA)

/-- Proof of Spec.frontPrivacy (Spec.lean). Under its premises index privacy passes to frontArg,
with the typed key and proof, at one query more. Conditional, of a shell. -/
theorem frontPrivacy : Spec.frontPrivacy :=
  fun R T h _ _ _ idx x₀ back Vf R₁ Rel hp Sim ζ ok noCoin asks once spare hA hok hpp hrel =>
    strongPrivacy_of_wrap (frontWrap T x₀ back) R₁ Rel (readOne T h) (frontArg T h idx x₀ Vf)
      (ZKCP.Special.simOf (readSim T Sim)) ζ ok idx hp (fun keys => keys.2)
      (fun w f => run_C_frontArg T h idx x₀ back Vf w f)
      (fun f keys x' u => run_P_frontArg T h idx x₀ back Vf f keys x' u) hpp
      (fun w x' u hr => by cases u; exact hrel w x' hr) hok
      (privacy_readOne T h Sim ζ ok R₁ noCoin asks once spare hA)

/-- Proof of Spec.frontPrivacyAt (Spec.lean). Under its premises index privacy passes, at one query
more, to the shell frontAt, whose verifier is, by definition, the definition of VerifierAndGoals.verify, and
whose committer and prover are this folder's, not the description's own. Conditional, of a shell. -/
theorem frontPrivacyAt : Spec.frontPrivacyAt :=
  fun D Z c₀ m₀ T h _ idx x₀ back _ _ _ PP PP' R₁ Rel hp Sim ζ ok noCoin asks once spare hA hok
      hpp hrel =>
    frontPrivacy (D.input Z c₀ m₀) T h _ PP PP' idx x₀ back _ R₁ Rel hp Sim ζ ok noCoin asks once
      spare hA hok hpp hrel

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.privacy_readTold
#print axioms OnBytes.FrontRoad.privacy_readOne
#print axioms OnBytes.FrontRoad.frontPrivacyK
#print axioms OnBytes.FrontRoad.frontPrivacy
#print axioms OnBytes.FrontRoad.frontPrivacyAt
