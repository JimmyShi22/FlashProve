-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompilerAtVerifyProofs.lean: the two propositions of
CompilerTheoremsAtVerify.lean, proved at any description.

1.  WHAT IS CLAIMED: each proposition is an implication from named premises. The premises on the
    provers are not proved here: this file proves neither completeness nor zero knowledge of the
    protocol.
2.  HOW: the compiler's theorems at each value of the public reading, then the library's passage from
    typed oracles to one hash function and to the commitment alone, then the passage to the argument
    system, which compile is by compile_eq_slotSystemF: what holds at slotSystem carries, since committer
    and prover keep their law at every hash function.
-/
import VerifiableInference.Final.CompilerTheoremsAtVerify
import VerifiableInference.Final.CompilerComplete
import Johnson.T3.CompiledPrivacy
import Johnson.FrontRoad.CompleteUpTo
import Johnson.FrontRoad.FitsOf
import Johnson.FrontRoad.PremAt

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch.Cms (NoRepeat IsOther)

/-- Completeness on a domain passes along an equation between argument systems. -/
theorem completeOn_of_eq {W : Type} {A B : ArgumentSystem} (e : A = B) (hA : A.Weights = W)
    (hB : B.Weights = W) (domain : W → List Token → List Token → Prop) (α : ℝ≥0∞)
    (h : CompleteOn B (fun w => domain (cast hB w)) α) :
    CompleteOn A (fun w => domain (cast hA w)) α := by
  subst e
  exact h

/-- Zero knowledge on a domain passes along an equation between argument systems. -/
theorem zeroKnowledgeOn_of_eq {W : Type} {A B : ArgumentSystem} (e : A = B) (hA : A.Weights = W)
    (hB : B.Weights = W) (domain : W → List Token → List Token → Prop) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : ZeroKnowledgeOn B (fun w => domain (cast hB w)) ζ) :
    ZeroKnowledgeOn A (fun w => domain (cast hA w)) ζ := by
  subst e
  exact h

section AtADescription

variable (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
  (idx : ModelWeights s → (D.C Z).I) (c₀ : Digest) (m₀ : D.More) (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (pair : Digest → D.More → T.D) (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X)
  (provers : HonestProvers ((D.F Z).withProvers (D.P Z)))
  (settings : (reading : T.D) →
    CompiledSettings ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers)
  (firstBlockTest : (reading : T.D) → Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256
    (D.input Z c₀ m₀).queryLayout.K (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier (D.input Z c₀ m₀).protocol
                (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

set_option quotPrecheck false

local notation "𝕀" =>
  atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound Form parse write
local notation "ℍ" =>
  fun reading => AtRecs.side (honestSide
    ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers (settings reading))

/-- **ZERO KNOWLEDGE OF compile, at a description.** -/
theorem zeroKnowledgeOfCompile_holds (budget : ℕ) : ZeroKnowledgeOfCompile 𝕀 budget := by
  intro N sessionsPerCopy inRange Served simulators fixedIndex domain back ζ parserError t3
    hPub hSet hTie hFormat hζ
  have hp : ZKCP.HasStrongIndexPrivacyWith
      (ZKCP.languageRelation fun w (x : List Token × List Token) =>
        domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2)
      (frontId D Z c₀ m₀ T ℍ s idx x₀ Form parse write)
      (compiledSimulatorAtVerify 𝕀 simulators fixedIndex sessionsPerCopy back)
      fun t n => ζ (t + 1) n :=
    privacy_frontId D Z c₀ m₀ T ℍ s idx x₀ Form parse write back
      (ZKCP.languageRelation Served) _ (fun _ => ())
      (fun d => compiledSimulator ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading d)
        provers (settings d) simulators fixedIndex sessionsPerCopy)
      ζ inRange hPub.noCoin hPub.asks hPub.once hPub.spare
      (fun d => privacyOn_mono
        (compiled_indexPrivacy _ _ _ _ _ _ provers (settings d) simulators inRange Served N
          sessionsPerCopy (ZKCP.Special.toPair (ZKCP.languageRelation Served)) fixedIndex (t3 d)
          (hFormat.runValues d) (hSet.fit d).coins (hPub.forIndexPrivacy d) fun _ _ _ hy => hy)
        (hζ d))
      hTie.range (fun _ => rfl)
      fun w x' hr => by
        obtain ⟨x, hb, hy, hbk⟩ := hTie.tie w x'.1 x'.2 hr.1 hr.2
        have hb' : (D.input Z c₀ m₀).buildInstance x' [] = some x := hb
        have hi : instOf (D.input Z c₀ m₀) x₀ x' = x := by
          unfold instOf
          rw [hb']
          rfl
        rw [hi]
        exact ⟨hy, hbk⟩
  exact ⟨zeroKnowledgeOn_of_eq
      (compile_eq_slotSystemF D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest
        coinBound Form parse write) rfl rfl domain _
      (zeroKnowledgeOn_slotSystemF hPub.noCoin (hPub.firstBlockFits _)
        (slot_zeroKnowledgeOn_of_relationOn D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound domain
          _ _ hPub.noCoin hSet.coinRange hp)),
    strongPrivacy_frontArgKF _ _ _ _ _ (hPub.firstBlockFits _) hp⟩

/-- **COMPLETE OF compile, at a description.** -/
theorem completeOfCompile_holds (budget : ℕ) : CompleteOfCompile 𝕀 budget := by
  intro N sessionsPerCopy inRange Served E domain back α parserError t2 hPub
    hSet hTie hFormat hα
  have hc : ZKCP.HasCompletenessError
      (ZKCP.languageRelation fun w (x : List Token × List Token) =>
        domain w x.1 x.2 ∧ ModelOutput s w x.1 x.2)
      (frontId D Z c₀ m₀ T ℍ s idx x₀ Form parse write) (α + parserError) :=
    frontIdCompleteUpTo D Z c₀ m₀ T ℍ s idx x₀ Form parse write pair Unit Unit
      (ZKCP.languageRelation Served) _ α parserError hPub.noCoin hPub.asks hPub.once hPub.spare
      (fits_of_eq D Z c₀ m₀ T pair agree) hPub.reads hPub.inScope hFormat.parserUpTo
      hPub.total
      (fun d => completeness_mono
        (compiled_complete_holds _ _ _ _ _ _ provers (settings d) Served E
          (t2 d) (hSet.fit d).lengths (hPub.forCompleteness d))
        (hα d))
      fun w x' hr => by
        obtain ⟨x, hb, hy, -⟩ := hTie.tie w x'.1 x'.2 hr.1 hr.2
        exact ⟨x, hb, hy⟩
  exact completeOn_of_eq
    (compile_eq_slotSystemF D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest coinBound
      Form parse write) rfl rfl domain _
    (completeOn_slotSystemF hPub.noCoin (hPub.firstBlockFits _)
      (slot_completeOn_of_relationOn D Z c₀ m₀ T ℍ s idx x₀ Form parse write coinBound domain _
        hPub.noCoin hSet.coinRange hc))

end AtADescription
end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledgeOfCompile_holds
#print axioms VerifiableInference.Compilation.completeOfCompile_holds
