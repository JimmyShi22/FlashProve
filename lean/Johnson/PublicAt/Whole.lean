-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/PublicAt/Whole.lean: THE SCHEME WITH THE WHOLE KEY PUBLISHED, WITH ITS LETTERS READ OFF THE
HASH FUNCTION: over a family of inputs in the public reading's value d (LayoutsByPublicReading,
Johnson/Top/InnerCompiledVerifierByPublicReading.lean) the committer, the prover and the verifier at d ask no public
string; so index privacy and completeness at each fixed d, OVER THE TYPED ORACLES, pass to the
scheme "read d, then run at d" over one hash function. Definitions, and theorems with their proofs.

General theorems: the family T, the honest sides h and the simulators are letters. This file states
no goal of the release.

What is laid together here.
  The typed committer, prover and verifier ask no point of the spare oracle: no_commitW, no_proveW
  (Johnson/WholeKey/Work.lean), asksIn_VRA (Johnson/Top/InnerCompiledVerifierByPublicReading.lean).
  Over one hash function, through the coding at d, they then ask no string that codes a point of the
  spare oracle: asksIn_overOne (Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublicArm.lean).
  The premise "spare", as in the library's step for soundness: at every d every public string codes
  a point of the spare oracle under the coding at d.
  The step from typed oracles to one hash function at each fixed d: ZKCP.privacyOn_overOne
  (ZKCP/OnRange.lean), Rom.completeness_overOne.
  The step over d: privacy_pub, privacy_pub_on, complete_pub, complete_pub_on (ZKCP/PublicRead/).

Main names (namespace OnBytes.PublicAt).
  typedAt T h d, typedAt_eq   the scheme at d over the typed oracles: wholeKeySchemeOverTypedOracles at the input T.at d
                  (Johnson/WholeKey/AtInput.lean), by unfolding. THE HONEST SIDE MAY HANG ON d.
  wholeAt T h d   the same over one hash function, through the coding at d.
  wholeRead T h   THE SCHEME: the public reading, then wholeAt at its value.
  off_public      an algorithm that asks no point of the spare oracle asks no public string.
  wholeAt_C, wholeAt_P, wholeAt_V   the three algorithms at d ask no public string.
  privacy_wholeRead, privacy_wholeRead_on, complete_wholeRead, complete_wholeRead_on   THE THEOREMS.

Limits. Index privacy and completeness at each fixed d are PREMISES here, asked at every d of the
type T.D (in the forms _on: of Dok), with one bound for all d. So are the four laws of the reading
(no coins; public strings alone; none twice; spare). No member T, h is built. The key holds no told
part and no commitment ID. That the release's committer and prover are wholeRead's is not shown. All
limits of the head of ZKCP/PublicRead/Spec.lean stand.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Work
import Johnson.WholeKey.AtInput
import Johnson.Top.InnerCompiledVerifierByPublicReading
import ZKCP.PublicRead.Privacy

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.PublicAt
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (h : T.D → HonestSide 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)

/-- The scheme with the whole key published at d, over the typed oracles. -/
def typedAt (d : T.D) : ZKCP.Gen.Arg (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) R.Index R.Instance Unit
    (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (RequestProof 256 R.protocol) :=
  argW R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters (h d)

/-- It is the scheme at the input at d. -/
theorem typedAt_eq (d : T.D) : typedAt T h d = wholeKeySchemeOverTypedOracles (T.at d) (h d) := rfl

/-- The same over one hash function, through the coding at d. -/
def wholeAt (d : T.D) : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)
    (Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (RequestProof 256 R.protocol) :=
  schemeOverOneHashFunction (T.m d) (typedAt T h d)

/-- **The scheme whose letters are read off the hash function.** -/
def wholeRead : ZKCP.Gen.Arg (rom 256) R.Index R.Instance Unit (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits)
    (T.D × Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (RequestProof 256 R.protocol) :=
  glueArg T.Pub (wholeAt T h)

variable {T}

/-- An algorithm over the typed oracles that asks no point of the spare oracle asks, over one hash
function through the coding at d, no public string. -/
theorem off_public (spare : ∀ d s, T.Pt s → IsOther (T.m d) s) (d : T.D) {α : Type}
    (c : Rom.OComp (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) α)
    (hc : c.AsksIn (NotOther 256 (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))) :
    (c.overOne (T.m d)).AsksIn fun _ s => ¬ T.Pt s :=
  OComp.AsksIn.mono (fun _ s hs hp => hs (spare d s hp)) (asksIn_overOne (T.m d) _ c hc)

theorem wholeAt_C (spare : ∀ d s, T.Pt s → IsOther (T.m d) s) (d : T.D) (i : R.Index) :
    ((wholeAt T h d).C i).AsksIn fun _ s => ¬ T.Pt s :=
  off_public spare d _ (no_commitW R.queryLayout (T.Sd d) (T.cA d) (h d) i)

theorem wholeAt_P (spare : ∀ d s, T.Pt s → IsOther (T.m d) s) (d : T.D)
    (isk : Isk 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) (b : List (R.Instance × Unit)) :
    ((wholeAt T h d).P isk b).AsksIn fun _ s => ¬ T.Pt s :=
  off_public spare d _ (no_proveW R.queryLayout (T.cA d) R.fixedSample (h d) isk b)

theorem wholeAt_V (spare : ∀ d s, T.Pt s → IsOther (T.m d) s) (d : T.D)
    (k : FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) (x : R.Instance) (π : RequestProof 256 R.protocol) :
    ((wholeAt T h d).V k x π).AsksIn fun _ s => ¬ T.Pt s :=
  off_public spare d _ (asksIn_VRA R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters (lowKey k) x (lowPrf k π))

variable {PP : Type} (Rl : ZKCP.Gen.RelPair R.Index R.Instance Unit PP)

/-- **Index privacy**: from index privacy at every d over the typed oracles, with the simulator
Sim d, to the scheme whose letters are read off the hash function, at the same bound. The simulator:
it draws the public reading's answers itself; then the simulator at d, seen through the coding at d,
with these answers in front. -/
theorem privacy_wholeRead
    (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
      (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol))
    (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : R.Index → Prop) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.PrivacyOn Rl (typedAt T h d) B (Sim d) ζ ok) :
    ZKCP.Gen.PrivacyOn Rl (wholeRead T h) B (glueSim T.Pub fun d => simOne (T.m d) (Sim d)) ζ ok :=
  privacy_pub 256 _ _ _ _ _ _ _ _ Rl (wholeAt T h) _ B ζ ok T.Pt T.Pub noCoin asks once
    (wholeAt_C h spare) (wholeAt_P h spare)
    fun d => ZKCP.privacyOn_overOne (T.m d) Rl (typedAt T h d) B (Sim d) ζ ok (hA d)

/-- **Index privacy, where it is known at the d of Dok alone**: β, the probability that the real
reading's value lies outside Dok, is added. At the other d the simulator, seen through the coding,
is asked for consistent answers. -/
theorem privacy_wholeRead_on
    (Sim : T.D → ZKCP.Gen.Simulator (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)) PP
      (FullKey 256 R.protocol R.offlineRoundSplits R.linkRoundSplits) R.Instance (RequestProof 256 R.protocol))
    (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) (β : ℝ≥0∞) (ok : R.Index → Prop) (Dok : T.D → Prop)
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, Dok d → ZKCP.Gen.PrivacyOn Rl (typedAt T h d) B (Sim d) ζ ok)
    (hS : ∀ d, ¬ Dok d → ConsistentOn Rl B (simOne (T.m d) (Sim d)) ok)
    (hβ : Rom.Pr T.Pub (fun _ => {d | ¬ Dok d}) ≤ β) :
    ZKCP.Gen.PrivacyOn Rl (wholeRead T h) B (glueSim T.Pub fun d => simOne (T.m d) (Sim d))
      (fun t N => ζ t N + β) ok :=
  privacy_pub_on 256 _ _ _ _ _ _ _ _ Rl (wholeAt T h) _ B ζ β ok T.Pt Dok T.Pub noCoin asks once
    (fun d _ => wholeAt_C h spare d) (fun d _ => wholeAt_P h spare d)
    (fun d hd => ZKCP.privacyOn_overOne (T.m d) Rl (typedAt T h d) B (Sim d) ζ ok (hA d hd)) hS hβ

/-- **Completeness**: from completeness at every d over the typed oracles, at the same error. -/
theorem complete_wholeRead (B : ℕ) (α : ℝ≥0∞) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, ZKCP.Gen.HasCompletenessError Rl (typedAt T h d) B α) :
    ZKCP.Gen.HasCompletenessError Rl (wholeRead T h) B α :=
  complete_pub 256 _ _ _ _ _ _ _ _ Rl (wholeAt T h) B α T.Pt T.Pub noCoin asks once
    (wholeAt_C h spare) (wholeAt_P h spare) (wholeAt_V h spare)
    fun d => completeness_overOne (T.m d) Rl (typedAt T h d) B α (hA d)

/-- **Completeness, where it is known at the d of Dok alone.** -/
theorem complete_wholeRead_on (B : ℕ) (α β : ℝ≥0∞) (Dok : T.D → Prop) (noCoin : T.Pub.NoCoin)
    (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (hA : ∀ d, Dok d → ZKCP.Gen.HasCompletenessError Rl (typedAt T h d) B α)
    (hβ : Rom.Pr T.Pub (fun _ => {d | ¬ Dok d}) ≤ β) :
    ZKCP.Gen.HasCompletenessError Rl (wholeRead T h) B (α + β) :=
  complete_pub_on 256 _ _ _ _ _ _ _ _ Rl (wholeAt T h) B α β T.Pt Dok T.Pub noCoin asks once
    (fun d _ => wholeAt_C h spare d) (fun d _ => wholeAt_P h spare d)
    (fun d _ => wholeAt_V h spare d)
    (fun d hd => completeness_overOne (T.m d) Rl (typedAt T h d) B α (hA d hd)) hβ

end OnBytes.PublicAt

#print axioms OnBytes.PublicAt.privacy_wholeRead
#print axioms OnBytes.PublicAt.privacy_wholeRead_on
#print axioms OnBytes.PublicAt.complete_wholeRead
#print axioms OnBytes.PublicAt.complete_wholeRead_on
