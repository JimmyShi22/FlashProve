-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/HonAt.lean: the premises of completeness at every value d of the type T.D, whether
or not the public reading can return it, as one premise (HonAll), at the same honest sides as the
premises of index privacy. Under it, if α bounds the explicit error at every d (AlphaLe), and under
the other premises of Spec.frontComplete (Complete.lean), the shell frontAt is complete with the
error α. Conditional, no member known, of a shell.
Terms and the limits that go with any quote: Spec.lean.

What this file has. F : SidesAt T holds PremAll's parameters (PremAt.lean), which may depend on d.
  FallsAt F   The parameters of completeness that may depend on d: the falls (Falls,
      Johnson/Prover/All/OfHonest.lean: sets of lists of challenges at which no acceptance is
      required), the seeds that are set aside (no acceptance is required at these either), and four
      bounds: on the measure of these seeds, and on that of withheld set and fall together for each
      of the three provers.
  HonAll G Yes Dok   At every d with Dok d, the four named premises of complete_of_honFit
      (Johnson/WholeKey/CompleteOfRecs.lean). HonFit at (F.a d).Hs, among its clauses: the three
      provers' strategies are accepted outside these sets, whose measures are bounded. LawFit:
      conditions on the wires and the search limits. WiresFit: conditions on the wires, the marks
      and the three verifiers, as in the theorems on soundness, and at most maxRt trees a component.
      SideFit: the lengths that the format requires of the honest side's salts and coins.
  AlphaLe G Dok α   One error for all d: alphaAll at every d with Dok d is at most α.
  complete_typedAt   Under HonAll and AlphaLe, at each d with Dok d, typedAt T F.side d is complete
      for one request with the error α, for the relation of the true instances Yes.
  frontComplete_hon   The statement of the title, at the honest sides F.side, with Dok := all d.
  completeness_mono   Completeness with an error holds with every larger error.

Limits. HonAll is required at every d of the type. No member is built. The clauses of HonFit on
acceptance are premises: no honest side with the protocol's three provers is written
(FrontProof.lean, Limits). That α is below 1 means little: what counts is the number (argued, not
proved: Johnson/WholeKey/Bundle.lean, head). All limits of Johnson/WholeKey/Complete.lean and of
Complete.lean hold here too.

How it fits. PremAll is PremW at every d with Dok d, and PremW does not exclude a sessions' prover
that always aborts (said here without a theorem; Complete.lean, "How it fits"). So HonAll is stated
over the same F: the honest sides are (F.a d).Hs in both.
-/
import Johnson.FrontRoad.PremAt
import Johnson.FrontRoad.Complete
import Johnson.WholeKey.CompleteOfRecs

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- Completeness at an error holds at every larger error. -/
theorem completeness_mono {S : OSpec} {I X W PP IVK ISK Pf : Type} {R : ZKCP.Gen.RelPair I X W PP}
    {A : ZKCP.Gen.Arg S I X W IVK ISK Pf} {B : ℕ} {α α' : ℝ≥0∞}
    (h : ZKCP.Gen.HasCompletenessError R A B α) (hα : α ≤ α') :
    ZKCP.Gen.HasCompletenessError R A B α' :=
  fun i b hb => (h i b hb).trans hα

variable {R : InnerCompilerInput} {T : LayoutsByPublicReading R} (F : SidesAt T)

/-- The parameters of completeness that may depend on the public reading's value d. -/
structure FallsAt where
  /-- the falls of the three honest provers' structures (F.a d).Hs -/
  falls : (d : T.D) → Falls (F.a d).Hs
  /-- the seeds that are set aside -/
  Zs : T.D → R.Index → R.protocol.EncodingRandomness → Set R.protocol.OutOfDomainSeed
  /-- a bound on the measure of the seeds that are set aside -/
  ζc : T.D → ℝ≥0∞
  /-- a bound on the measure of withheld set and fall together, for the prover Hs.T -/
  pT : T.D → ℝ≥0∞
  /-- the same for the link's prover Hs.Lk -/
  pL : T.D → ℝ≥0∞
  /-- the same for the sessions' prover Hs.B -/
  pO : T.D → ℝ≥0∞

variable {F} (G : FallsAt F)

/-- The four named premises of complete_of_honFit (HonFit, LawFit, WiresFit, SideFit) at every d
with Dok d, at the honest sides of F. -/
structure HonAll (Yes : R.Index → R.Instance → Prop) (Dok : T.D → Prop) : Prop where
  hon : ∀ d, Dok d →
    HonFit (F.a d).Hs (G.falls d) R.queryLayout (T.Sd d) Yes (G.Zs d) (G.ζc d) (G.pT d) (G.pL d) (G.pO d)
  law : ∀ d, Dok d → LawFit R.queryLayout (T.Sd d) (F.a d).capT (F.a d).capL (F.a d).capB
  wires : ∀ d, Dok d → WiresFit R.queryLayout (T.cA d)
  side : ∀ d, Dok d → SideFit R.queryLayout R.compilerParameters (F.a d).side

/-- The explicit error alphaAll at every d with Dok d is at most α: one error for all these d. -/
def AlphaLe (Dok : T.D → Prop) (α : ℝ≥0∞) : Prop :=
  ∀ d, Dok d →
    alphaAll R.queryLayout (F.a d).capT (F.a d).capL (F.a d).capB (G.ζc d) (G.ζc d) (G.pT d) (G.pL d)
      (G.pO d) ≤ α

variable {G} {Yes : R.Index → R.Instance → Prop} {Dok : T.D → Prop} {α : ℝ≥0∞}

/-- Under HonAll and AlphaLe, at each d with Dok d: typedAt T F.side d, over the typed oracles, is
complete for one request with the error α, for the relation ZKCP.languageRelation Yes. -/
theorem complete_typedAt (hH : HonAll G Yes Dok) (hα : AlphaLe G Dok α) (d : T.D) (hd : Dok d) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (typedAt T F.side d) 1 α :=
  completeness_mono
    (complete_of_honFit (F.a d).Hs (G.falls d) R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters (F.a d).side
      (F.a d).dc rfl (hH.hon d hd) (hH.law d hd) (hH.wires d hd) (hH.side d hd))
    (hα d hd)

/-- If HonAll and AlphaLe hold at every d of the type, and the other premises of Spec.frontComplete
hold at the honest sides F.side and the relation of Yes, the shell frontAt at F.side is complete
with the error α. Conditional, no member known, of a shell. -/
theorem frontComplete_hon (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (F : SidesAt T) (G : FallsAt F)
    (Yes : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) (α : ℝ≥0∞)
    (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
    (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : VerifierAndGoals.Parser D Z Form)
    (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form) (pair : Digest → D.More → T.D) (PP' : Type)
    (Rel : ZKCP.IndexedRelation (ModelWeights s) (List Token × List Token) Unit PP')
    (noCoin : T.Pub.NoCoin) (asks : T.Pub.AsksIn fun _ s => T.Pt s) (once : NoRepeat T.Pub)
    (spare : ∀ d s, T.Pt s → IsOther (T.m d) s)
    (fits : ∀ c m commitment prompt output (proof : VerifierAndGoals.TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof)
    (reads : ∀ hash : Hash,
      (VerifierAndGoals.Fit.readBoth D Z c₀ m₀ T pair).evaluate hash = T.Pub.det fun _ => hash)
    (scope : VerifierAndGoals.InScope Z = true)
    (hparse : UndoOn D Z c₀ m₀ T F.side idx Yes parse encF)
    (hcode : ∀ ck, ∃ code, T.encT ck = some code)
    (hH : HonAll G Yes fun _ => True) (hα : AlphaLe G (fun _ => True) α)
    (hrel : ∀ w x', Rel.rel w x' () →
      ∃ x, (D.input Z c₀ m₀).buildInstance x' [] = some x ∧ Yes (idx w) x) :
    ZKCP.HasCompletenessError Rel (frontAt D Z c₀ m₀ T F.side s idx x₀ Form parse encF) α :=
  frontComplete D Z c₀ m₀ T F.side s idx x₀ Form parse encF pair Unit PP'
    (ZKCP.languageRelation Yes) Rel α noCoin asks once spare fits reads scope hparse hcode
    (fun d => complete_typedAt hH hα d trivial) hrel

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.frontComplete_hon
#print axioms OnBytes.FrontRoad.complete_typedAt
