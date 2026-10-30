-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/Ties.lean: how the goals of Ladder.lean follow from one another, that its verifier refuses
public files out of scope, and a proof of the facts about its fixed terms (`FixedFacts`). Theorems
with proofs; Ladder.lean itself holds definitions only.

What this file states.
  The verifier: `refuses_out_of_scope`, `not_accepts_out_of_scope`.
  Soundness: `g7_of_g8` (by `soundAt_of_soundUnderPolicyAt`); `g7_of_g7'`. The like for the goals
    at `soundnessErrorInQueries`: Ladder/BitsTies.lean.
  The honest side: `completeOn_of_completeFor`: where 2^8 ≤ theta, completeness for "can be served
    and meets the files' policy" gives completeness for the model's own outputs that can be served.
  The fixed terms: `fixedFacts`, with no hypothesis (by `zeroWeights_isSome`, `canServe_zero_one`,
    `not_modelOutput_zero_one`, `voting_served`, `valid_of_read`).

What it does not show. That any goal holds of any description. No converse: G8 speaks of every
policy in scope and G7 of exact match alone; at exact match the claim of G8 says one clause more
than that of G7 (the output is not empty); and G8 names its extractor where G7 says that there is
one. Ladder/Guards.lean evaluates `FilesRead` and does not prove it; nor does this file. All weights
in the proof of `fixedFacts` are made up, and all their layers are zero: the all-zero weights, at
which every logit is 0, and the library's weights under which the model answers one fixed token
after any one token (`modelNextToken_atVotingWeights`, VerifiableInference/ModelGuards.lean).
So `fixedFacts` shows that such weights and outputs exist, and nothing of a model with real scores.
"Valid settings" are settings that pass the test `settingsAreValid`
(VerifiableInference/ModelWeights.lean).
-/
import Ladder
import Policy.Front.TrueUnder
import Policy.Front.MeetsPolicyGuards
import VerifiableInference.MapWeights
import IntegerModel.Arrays.SameModel
import IntegerModel.ReplyOnWindow
import Inst.Model.ProgramRGuards
import VerifiableInference.ModelGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals
open VerifiableInference Inst.Model
open scoped ENNReal

/-! ## 1. The verifier -/

/-- **At public files that are out of scope the verifier is "no"**, whatever `D`, the parser and its
other arguments are. -/
theorem refuses_out_of_scope (D : Description) (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form)
    (commitment : Commitment) (prompt output : List Token) (form : Form)
    (out : InScope Z = false) :
    verify D Z parse commitment prompt output form = .done false := by
  unfold verify verifyAt
  rw [out]
  rfl

/-- So there the argument system of the goals accepts nothing, at any hash function. -/
theorem not_accepts_out_of_scope (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (Form : Type)
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) (out : InScope Z = false) :
    (system D Z s Form prove parse).accepts hash commitment prompt output form = false := by
  show (verify D Z parse commitment prompt output form).evaluate hash = false
  rw [refuses_out_of_scope D Z parse commitment prompt output form out]
  rfl

/-! ## 2. Soundness -/

/-- Soundness under the files' policy gives soundness at the files of exact match, at one error. -/
theorem soundAt_of_soundUnderPolicyAt (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (h : SoundUnderPolicyAt D eps) : SoundAt D eps := by
  intro Z pp ht hr hx
  refine ⟨(h Z pp ht hr).1, fun Form prove parse n hn => ?_⟩
  have h1 := (h Z pp ht hr).2 Form prove parse n hn
  rw [hx] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) prove id
    (system D Z (settingsOfRead pp) Form prove parse).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_exact_iff w p o).1 hm).2)
  have h3 : SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
      (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id)
      (system D Z (settingsOfRead pp) Form prove parse).IsModelOutput (fun t => eps t n) := h2
  exact (sound_iff_soundFor _ _).2 ⟨_, h3⟩

/-- **G8 gives G7**, at the same error. -/
theorem g7_of_g8 (D : SecondHashFunctionType → Description) (h : G8 D) : G7 D :=
  let ⟨eps, below, sound⟩ := h
  ⟨eps, below, soundAt_of_soundUnderPolicyAt _ _ sound⟩

/-- **G7' gives G7**, at the same error. -/
theorem g7_of_g7' (D : SecondHashFunctionType → Description) (h : G7' D) : G7 D :=
  let ⟨eps, below, sound⟩ := h
  ⟨eps, below, sound _⟩

/-! ## 3. The honest side -/

/-- What the reader returns gives valid settings. -/
theorem valid_of_read {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) :
    settingsAreValid (settingsOfRead pp) = true :=
  settingsAreValid_settingsOf (Cm.lawful_of (OnBytes.Flat.settingsAtRef_lawful hr))

set_option maxRecDepth 100000 in
/-- `CompleteOn` on `CanServe` is `ProofAcceptedWhere` at well-formed requests and the model's
result, at one system of record. -/
theorem completeOn_iff_proofAccepted (D : Description) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (read : readFiles Z = .ok pp) (α : ℝ≥0∞) :
    CompleteOn (systemOfRecord D Z (settingsOfRead pp)) (CanServe (settingsOfRead pp)) α ↔
      AtEveryRequest.ProofAcceptedWhere (systemOfRecord D Z (settingsOfRead pp))
        (AtEveryRequest.WellFormedRequest (settingsOfRead pp))
        (AtEveryRequest.modelResult (settingsOfRead pp)) α :=
  (AtEveryRequest.proofAcceptedWhere_iff_completeOn (systemOfRecord D Z (settingsOfRead pp))
    (AtEveryRequest.WellFormedRequest (settingsOfRead pp))
    (AtEveryRequest.modelResult (settingsOfRead pp))
    (CanServe (settingsOfRead pp))
    (fun (weights : ModelWeights (settingsOfRead pp)) prompt output =>
      AtEveryRequest.wellFormed_and_result_iff (valid_of_read read) weights prompt output) α).symm

/-- Where 2^8 ≤ theta, completeness for "can be served and meets the files' policy" gives
completeness for the model's own outputs that can be served. -/
theorem completeOn_of_completeFor (D : Description) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (floor : 2 ^ 8 ≤ pp.pol.theta)
    (h : CompleteFor (systemOfRecord D Z (settingsOfRead pp))
      (fun w prompt output => CanServe (settingsOfRead pp) w prompt output ∧
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output) completenessErrorBound) :
    CompleteOn (systemOfRecord D Z (settingsOfRead pp)) (CanServe (settingsOfRead pp)) completenessErrorBound := by
  intro weights prompt output hc ho
  exact h weights prompt output ⟨hc, Policy.meetsPolicy_of_isModelOutput floor
    (le_trans floor (OnBytes.Flat.settingsAtRef_lawful hr).pol.2.1) hc.2.1 ho⟩

/-! ## 4. The facts about the fixed terms -/

/-- At valid settings the model at the all-zero weights has a value on every list of 1 to 1,024
tokens of the vocabulary. -/
theorem zeroWeights_isSome {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (tokens : List ℕ) (h0 : 0 < tokens.length)
    (hn : tokens.length ≤ ppref.T) (small : ∀ token ∈ tokens, token < ppref.V) :
    (modelNextToken settings (Policy.zeroWeights valid) tokens).isSome = true := by
  unfold Policy.zeroWeights
  rw [modelNextToken_eq_nextToken (lawful_scalesOf valid) valid (settingsOf_scalesOf valid),
    Cm.index_ofIndex, IntegerModel.nextToken_eq_programNextToken _ (lawful_scalesOf valid)]
  obtain ⟨list, hl⟩ := IntegerModel.vocabularyTokens_of_small tokens small
  rw [hl]
  have e : list.map Fin.val = tokens := map_val_of_vocabularyTokens tokens list hl
  have len : list.length = tokens.length := by rw [← e, List.length_map]
  show ((IntegerModel.programNextToken _ list).map Fin.val).isSome = true
  rw [Option.isSome_map]
  refine IntegerModel.model_isSome_of_window _ (fun t => list.getD t.val ⟨0, by decide⟩) list
    (by omega) (by omega) ?_ ?_
  · intro t ht
    show list.get ⟨t, ht⟩ = list.getD t ⟨0, by decide⟩
    rw [List.getD_eq_getElem _ _ ht]
    rfl
  · exact ProgramRGuards.runs_iZero (lawful_scalesOf valid).toPP _

/-- At valid settings and the all-zero weights the output of the one token 1 after the prompt of the
one token 0 can be served. -/
theorem canServe_zero_one {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) :
    CanServe settings (Policy.zeroWeights valid) [0] [1] := by
  have small : ∀ token ∈ IntegerModel.zeroFilledWindow [0] [1], token < ppref.V := by
    intro token hm
    have hm' := List.mem_of_mem_take hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_replicate] at hm'
    rcases hm' with (rfl | rfl) | ⟨-, rfl⟩ <;> decide
  have len : (IntegerModel.zeroFilledWindow [0] [1]).length = 1024 := by
    unfold IntegerModel.zeroFilledWindow
    rw [List.length_take, List.length_append, List.length_append, List.length_replicate]
    rfl
  refine ⟨?_, by simp, zeroWeights_isSome valid _ (by rw [len]; decide) (by rw [len]; decide) small⟩
  intro token hm
  rw [vocabulary_eq valid]
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> decide

/-- At valid settings and the all-zero weights the output [1] after the prompt [0] is not the
model's. -/
theorem not_modelOutput_zero_one {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) :
    ¬ ModelOutput settings (Policy.zeroWeights valid) [0] [1] := by
  intro all
  have m := (Policy.meetsPolicy_exact_iff (Policy.zeroWeights valid) [0] [1]).2 ⟨by simp, all⟩
  exact absurd (((Policy.meetsPolicy_zeroWeights_one_iff valid _).1 m).2 (by decide)) (by decide)

/-- At valid settings, for a token v of the vocabulary, and the library's weights under which the
model answers v after any one token: the output [v] after the prompt [0] can be served and is the
model's. -/
theorem voting_served {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (v : ℕ) (hv : v < 202048) :
    CanServe settings (weightsOfIndex valid (Cm.biteI (fun _ => 0) fun _ => v)) [0] [v] ∧
      ModelOutput settings (weightsOfIndex valid (Cm.biteI (fun _ => 0) fun _ => v)) [0] [v] :=
  ⟨canServe_atVotingWeights _ valid (fun _ => 0) (fun _ => v) (fun _ => (by decide : 0 < 5120))
      (fun _ => hv) 0 (by decide),
    fun position h => by
      obtain rfl : position = 0 := Nat.lt_one_iff.1 h
      exact modelNextToken_atVotingWeights _ valid (fun _ => 0) (fun _ => v)
        (fun _ => (by decide : 0 < 5120)) (fun _ => hv) 0 (by decide)⟩

/-- **The facts about the fixed terms of Ladder.lean.** -/
theorem fixedFacts : FixedFacts where
  claim := fun _ _ _ hr =>
    ⟨_, _, [0], [1], [2], (voting_served (valid_of_read hr) 1 (by decide)).1,
      (voting_served (valid_of_read hr) 1 (by decide)).2,
      (voting_served (valid_of_read hr) 2 (by decide)).1,
      (voting_served (valid_of_read hr) 2 (by decide)).2, rfl, by decide⟩
  otherClaim := fun pp hr hx =>
    ⟨Policy.zeroWeights (valid_of_read hr), [0], [1], canServe_zero_one (valid_of_read hr), by
        rw [hx]
        exact (Policy.meetsPolicy_zeroWeights_one_iff (valid_of_read hr) _).2
          ⟨by decide, fun c => absurd c (by decide)⟩,
      not_modelOutput_zero_one (valid_of_read hr)⟩
  numbers := by
    refine ⟨?_, by decide, by decide⟩
    unfold completenessErrorBound ceiling
    have h : ((2 : ℝ≥0∞)⁻¹) ^ 40 < 2⁻¹ := by
      rw [← ENNReal.inv_pow]
      refine ENNReal.inv_lt_inv.2 ?_
      exact_mod_cast (by norm_num : (2 : ℕ) < 2 ^ 40)
    have q : (4 : ℝ≥0∞)⁻¹ ≤ 2⁻¹ :=
      ENNReal.inv_le_inv.2 (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 4))
    calc ((2 : ℝ≥0∞)⁻¹) ^ 40 + 4⁻¹ < 2⁻¹ + 2⁻¹ :=
          ENNReal.add_lt_add_of_lt_of_le (by simp) h q
      _ = 1 := ENNReal.inv_two_add_inv_two

end VerifierAndGoals

#print axioms VerifierAndGoals.refuses_out_of_scope
#print axioms VerifierAndGoals.not_accepts_out_of_scope
#print axioms VerifierAndGoals.soundAt_of_soundUnderPolicyAt
#print axioms VerifierAndGoals.g7_of_g8
#print axioms VerifierAndGoals.g7_of_g7'
#print axioms VerifierAndGoals.completeOn_of_completeFor
#print axioms VerifierAndGoals.zeroWeights_isSome
#print axioms VerifierAndGoals.canServe_zero_one
#print axioms VerifierAndGoals.not_modelOutput_zero_one
#print axioms VerifierAndGoals.voting_served
#print axioms VerifierAndGoals.valid_of_read
#print axioms VerifierAndGoals.fixedFacts
