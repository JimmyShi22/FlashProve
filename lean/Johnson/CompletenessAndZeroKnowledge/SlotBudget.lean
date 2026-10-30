-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/SlotBudget.lean: HOW MANY HASH QUERIES THE HONEST SIDE OF slotSystem ASKS
(Johnson/FrontRoad/Slot.lean), in the form of WithinBudget (VerifiableInference/AtEveryRequest.lean):
sampling, one run of the committer, one run of the prover. The prover runs the committer again, so
the committer's count stands twice. Upper bounds at letters; nothing here is a goal.

slotBudget is what the road's counts give: each typed query counts as Bk hash queries, the largest
number of blocks of a typed answer (queryBound_overOne). slotBudget_over_two_pow_48: at depth 32 and
K = 24087 that number is above 2 ^ 48 at any number of copies and any search limits, so
WithinBudget at 2 ^ 48 does not follow from this count. That says nothing of the true count.
-/
import Johnson.FrontRoad.Slot
import Johnson.FrontRoad.CompleteK
import Johnson.WholeKey.Work
import VerifiableInference.AtEveryRequest

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt VerifiableInference
open VerifiableInference.OnPublicFiles ZKCP.PublicRead VerifierAndGoals
open VerifiableInference.AtEveryRequest (WithinBudget)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The count: no query to sample; the committer: the public reading, NC typed queries of at most Bk
blocks, one for the ID; the prover: the committer again, NP typed queries. -/
def slotBudget (q₀ Bk NC NP : ℕ) : ℕ := 2 * (q₀ + NC * Bk + 1) + NP * Bk

section Slot
variable (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
  (T : LayoutsByPublicReading (D.input Z c₀ m₀))
  (h : T.D → HonestSide 256 (D.input Z c₀ m₀).protocol (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits
    (D.input Z c₀ m₀).linkRoundSplits)
  (s : IntegerTransformer.Settings) (idx : ModelWeights s → (D.input Z c₀ m₀).Index)
  (x₀ : (D.input Z c₀ m₀).Instance) (Form : Type) (parse : Parser D Z Form)
  (encF : TypedProof (D.F Z) (D.P Z) → Form) (bound : ℕ)

/-- **The honest side of slotSystem stays within slotBudget.** NC and NP count TYPED queries;
the budget counts HASH queries. Bk is the largest number of blocks of a typed answer, charged to
every typed query, so tree queries, which have one block, are overcharged. -/
theorem slotSystem_withinBudget {q₀ Bk NC NP : ℕ} (hq : T.Pub.QueryBound q₀)
    (hB : ∀ d o, (T.m d).blocks o ≤ Bk) (hp : ∀ d, PathsFit (D.input Z c₀ m₀).queryLayout (h d))
    (hC : ∀ d, commitN (D.input Z c₀ m₀).queryLayout (h d) ≤ NC)
    (hP : ∀ d, proveN (D.input Z c₀ m₀).queryLayout (h d) ≤ NP) :
    WithinBudget (slotSystem D Z c₀ m₀ T h s idx x₀ Form parse encF bound)
      (slotBudget q₀ Bk NC NP) := by
  have hC' : ∀ w, ((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).C w).QueryBound
      (q₀ + NC * Bk + 1) := fun w =>
    queryBound_frontKC T h idx x₀ _ _ _ q₀ Bk NC hq hB
      (fun d i => (queryBound_commitW _ _ _ _ (hp d) i).mono (hC d)) w
  have hP' : ∀ isk x', ((frontId D Z c₀ m₀ T h s idx x₀ Form parse encF).P isk x' ()).QueryBound
      (NP * Bk) := fun isk x' =>
    queryBound_frontKP T h idx x₀ _ _ _ Bk NP hB
      (fun d isk b => (queryBound_proveW _ _ _ _ (hp d) isk b).mono (hP d)) isk x'
  refine ⟨0, q₀ + NC * Bk + 1, (q₀ + NC * Bk + 1) + NP * Bk, le_of_eq ?_, fun _ => trivial,
    fun w coins => ?_, fun w coins prompt output => ?_⟩
  · unfold slotBudget
    ring
  · exact queryBound_deterministicOf _ _
      (ZKCP.OComp.QueryBound.mapO _ _ _ (ZKCP.OComp.QueryBound.withCoins _ _ _ (hC' w)))
  · exact (RandomizedAlgorithm.queryBound_ofUpload _ _).2
      (ZKCP.queryBound_P_coinsFirst _ bound w coins (prompt, output) () _ _ (hC' w)
        fun isk => hP' isk _)

end Slot

section Count
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (h : HonestSide lam L Bd aT aL)

/-- The committer's typed count: M + 2 tables, the key's test, M + 1 links. -/
theorem commitN_eq : commitN W h = (h.M + 2) * tabN W +
    chainN L.offline.shape aT (wTC W).sh h.capT 0 W.depthReqT + (h.M + 1) * linkN W h := by
  unfold commitN
  ring

/-- The count at the road's numbers: the reading's 8, blocks at most K + 1. -/
theorem slotBudget_road (NP : ℕ) :
    slotBudget 8 (W.K + 1) (commitN W h) NP =
      18 + (W.K + 1) * (2 * ((h.M + 2) * tabN W +
        chainN L.offline.shape aT (wTC W).sh h.capT 0 W.depthReqT + (h.M + 1) * linkN W h) + NP) := by
  rw [commitN_eq]
  unfold slotBudget
  ring

/-- **At depth 32 and K = 24087 the road's count is above 2 ^ 48**: the tables alone, at any number
of copies and any search limits. -/
theorem slotBudget_over_two_pow_48 (hd : W.depth = 32) (hK : W.K = 24087) (NP : ℕ) :
    2 ^ 48 < slotBudget 8 (W.K + 1) (commitN W h) NP := by
  have ht : tabN W = 2 * 2 ^ 32 + (2 + 0) := by
    unfold tabN
    rw [hd]
  have h2 : 2 * tabN W ≤ commitN W h := by
    rw [commitN_eq]
    nlinarith [Nat.zero_le (h.M * tabN W), Nat.zero_le (tabN W)]
  have h3 : (2 * tabN W) * (W.K + 1) ≤ commitN W h * (W.K + 1) := Nat.mul_le_mul_right _ h2
  unfold slotBudget
  rw [ht, hK] at *
  norm_num at h3 ⊢
  omega

end Count

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.slotSystem_withinBudget
#print axioms OnBytes.FrontRoad.commitN_eq
#print axioms OnBytes.FrontRoad.slotBudget_road
#print axioms OnBytes.FrontRoad.slotBudget_over_two_pow_48
