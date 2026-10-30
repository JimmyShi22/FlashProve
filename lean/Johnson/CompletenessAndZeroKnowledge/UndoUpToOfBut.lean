-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/UndoUpToOfBut.lean: UndoUpTo (Johnson/FrontRoad/CompleteUpTo.lean) from UndoOnBut (Johnson/Face/UndoOfFits.lean) and a bound on the
event that is excepted. So frontIdCompleteUpTo then gives completeness at α + γ.

1.  WHAT IS CLAIMED: where the parser undoes the writer outside an event of the honest side's keys and proofs, and that event has chance at
    most γ, the parser undoes the writer up to γ. Nothing else.
-/
import Johnson.CompletenessAndZeroKnowledge.BadExp

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  {J : Type} (idx : J → (D.input Z c₀ m₀).Index)
  (Tr : (D.input Z c₀ m₀).Index → (D.input Z c₀ m₀).Instance → Prop) {Form : Type}
  (parse : VerifierAndGoals.Parser D Z Form) (encF : VerifierAndGoals.TypedProof (D.F Z) (D.P Z) → Form)
  (Bad : FullKey 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits →
    RequestProof 256 (D.input Z c₀ m₀).protocol → Prop)

/-- **The bridge.** hU is UndoOnBut (Johnson/Face/UndoOfFits.lean), by unfolding. -/
theorem undoUpTo_of_undoOnBut (γ : ℝ≥0∞)
    (hU : ∀ (w : J) (f : ZKCP.Oracle 256), ∀ keys ∈ (((readOne T h).C (idx w)).run f).support,
      ∀ (x' : List Token × List Token) x, (D.input Z c₀ m₀).buildInstance x' [] = some x → Tr (idx w) x →
        ∀ π ∈ (((readOne T h).P keys.2 x ()).run f).support,
          true ∈ (((readOne T h).V keys.1 x π).run f).support → ¬ Bad keys.1.2 π →
            (parse x'.1 x'.2 (encF ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))).evaluate f =
              ([], (lowKey keys.1.2, lowPrf keys.1.2 π)))
    (hγ : ∀ i x, Tr i x → ZKCP.Pr (badExp (readOne T h) i x ()) (fun _ => {o | Bad o.1.1.2 o.2}) ≤ γ) :
    UndoUpTo D Z c₀ m₀ T h idx Tr parse encF γ := by
  intro w x' x hb hTr
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_) (hγ _ x hTr)
  show ZKCP.prob (((((readOne T h).C (idx w)).bind fun keys => ((readOne T h).P keys.2 x ()).bind fun π =>
      ((readOne T h).V keys.1 x π).mapO fun b => (keys.1, π, b))).run f) _ ≤
    ZKCP.prob (((((readOne T h).C (idx w)).bind fun keys => ((readOne T h).P keys.2 x ()).bind fun π =>
      ZKCP.OComp.pure (keys, π))).run f) _
  rw [ZKCP.run_bind, ZKCP.prob_bind, ZKCP.run_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun keys hk => ?_
  rw [ZKCP.run_bind, ZKCP.prob_bind, ZKCP.run_bind, ZKCP.prob_bind]
  refine ZKCP.expect_le_on_support _ fun π hπ => ?_
  by_cases hB : Bad keys.1.2 π
  · refine le_trans (ZKCP.prob_le_one _ _) (le_of_eq ?_)
    show (1 : ℝ≥0∞) = ZKCP.prob (PMF.pure (keys, π)) _
    exact ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2
      (by rw [PMF.support_pure]; exact Set.singleton_subset_iff.2 hB)).symm
  · refine le_trans (le_of_eq ?_) (zero_le _)
    rw [ZKCP.OComp.run_mapO]
    refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun o ho hE => ?_)
    obtain ⟨hb', hne⟩ := hE
    obtain ⟨b, hbs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ho
    have hbt : b = true := hb'
    subst hbt
    exact hne (hU w f keys hk x' x hb hTr π hπ hbs hB)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.undoUpTo_of_undoOnBut
