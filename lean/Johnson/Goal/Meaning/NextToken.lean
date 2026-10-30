-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/NextToken.lean: the integer model of which the protocol's claim speaks is the
model of the top statements.

Two texts of this library speak of "the model".
* The top statements (Sound and the others, VerifiableInference/Statements.lean) speak of the field
  nextToken of an argument system. In the system of the goals (VerifierAndGoals.system, Ladder.lean) that
  field is modelNextToken at the settings of a table of scales, and the weights are arrays
  (ModelWeights).
* The protocol's claim speaks of a committed matrix of field elements M and of a request x: a window
  of 1,024 tokens, an announced token and two positions. ModelSays pp M x, below, says: M holds a
  well-formed matrix of digits i (Flat.Holds, Johnson/Flat/LedgerClaim.lean), and x is true at i
  under pp's table of scales and acceptance policy (Policy.IsTrueUnder, Policy/Rel/True.lean: the
  library's integer program runs on the window, the request has its form, and the checked tokens
  are within the policy under the program's logits).
This file states and proves that the two are one model, at every pp whose table of scales is lawful.
The statement is MeaningNextToken, a closed proposition; the theorem is meaning_nextToken. What the
goals' reader of the public files returns has a lawful table: meaning_atFiles.

What it says (the fields of MeaningAt), with s for the settings of pp's table:
  package       The field nextToken of the goals' system is modelNextToken s, and its IsModelOutput
                is VerifierAndGoals.ModelOutput s, whatever the description, the public files, the form, the
                prover and the parser are. The other fields therefore name these two terms.
  sameFunction  At the weights that an index holds, modelNextToken s is IntegerModel.nextToken at
                pp's table and the index's tensors, on every list of numbers: where one has no
                value, the other has none. Both are IntegerTransformer.model
                (IntegerModel/Model.lean), at two makings of its arrays.
  decoded       The weights under a matrix that holds an index (weightsOfMatrix) are the weights
                that this index holds. A matrix of any shape holds at most one index.
  everyWeights  All weights are the weights under a matrix: that of their own digits.
  twoSided      THE LAW'S WEIGHT. For a request x built from a prompt, output tokens and any
                padding: ModelSays pp M x holds exactly if M decodes to weights at which the model
                has a value on x's window of 1,024 tokens and the output meets pp's policy
                (Policy.MeetsPolicy). At every policy.
  exactMatch    At the policy of exact match "meets the policy" is: the output is not empty, and the
                output tokens are the model's.
  served        A request that can be served (CanServe) and whose output meets the policy is built
                without padding, and ModelSays holds of it at the matrix of the weights' digits.

What it does not say. Nothing on a protocol or a verifier: that an accepted proof gives ModelSays is
another law. The law names no verifier, so it holds whatever a verifier decides. Nothing on whether
the lookup tables inside the integer program are the tables whose digests the parameter file holds.
That the table and the policy which the goals' reader returns are those that the verifier's own
reading holds: Johnson/Goal/Meaning/Ties.lean. The reference model's sizes alone. The padding is the
prover's: ModelSays asks that the integer program runs on the whole window, the padding too; the
claim MeetsPolicy speaks of the prompt and the output alone.

How it is built. Every step is a theorem of the library; they are put together at the goals' own
terms, two-sided, from the committed matrix: modelNextToken_eq_nextToken
(IntegerModel/Arrays/SameModel.lean), Policy.isTrueUnder_iff_meetsPolicy
(Policy/Front/TrueUnderConverse.lean), Policy.meetsPolicy_exact_iff
(Policy/Front/MeetsPolicyGuards.lean), IntegerModel.model_isSome_of_window and runs_of_full
(IntegerModel/ReplyOnWindow.lean), Flat.matrixOf and Flat.holds_matrixOf
(Johnson/Flat/ThreeFull.lean).
-/
import Ladder.Ties
import Policy.Front.TrueUnderConverse
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Meaning
open VerifiableInference.OnPublicFiles Inst.Model
open Inst.Model.Layout (kRef hRef)

/-! ## 1. The terms -/

/-- **What the protocol's claim says of the model.** The committed matrix M holds a well-formed
matrix of digits i, and the request x is true at i under the table of scales and the acceptance
policy of pp. -/
def ModelSays (pp : ScalesAndPolicy) {rows cols : ℕ} (M : Fin rows → Fin cols → Flat.GE)
    (x : Instance ppref) : Prop :=
  ∃ i : Cm.Idx, Flat.Holds M i ∧ Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x

/-- The weights under a committed matrix: those that its index holds; none if it holds no index. -/
def weightsOfMatrix {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) {rows cols : ℕ}
    (M : Fin rows → Fin cols → Flat.GE) : Option (ModelWeights settings) :=
  (Flat.indexOf M).map (weightsOfIndex valid)

/-- The 1,024 tokens of a request's window, as numbers. -/
def windowOf (x : Instance ppref) : List Token := (IntegerModel.firstToks x 1024).map Fin.val

/-! ## 2. The statement -/

/-- The law at one pp whose table of scales is lawful. `valid`: so its settings are valid. -/
structure MeaningAt (pp : ScalesAndPolicy)
    (valid : settingsAreValid (VerifierAndGoals.settingsOfRead pp) = true) : Prop where
  /-- The top statements' two terms, in the goals' system. They depend on the settings alone. -/
  package : ∀ (D : VerifierAndGoals.Description) (Z : VerifierAndGoals.PublicFiles) (Form : Type)
      (prove : ModelWeights (VerifierAndGoals.settingsOfRead pp) → D.Rand → List Token → List Token →
        RandomizedAlgorithm Form)
      (parse : VerifierAndGoals.Parser D Z Form),
      (VerifierAndGoals.system D Z (VerifierAndGoals.settingsOfRead pp) Form prove parse).nextToken
          = modelNextToken (VerifierAndGoals.settingsOfRead pp) ∧
        ∀ weights prompt output,
          (VerifierAndGoals.system D Z (VerifierAndGoals.settingsOfRead pp) Form prove parse).IsModelOutput weights
              prompt output ↔
            VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output
  /-- One function, on every list of numbers. -/
  sameFunction : ∀ (i : Cm.Idx) (tokens : List Token),
      modelNextToken (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) tokens
        = IntegerModel.nextToken (Cm.Scales.of pp) i.index tokens
  /-- The weights under a matrix that holds an index are the weights that the index holds. -/
  decoded : ∀ (rows cols : ℕ) (M : Fin rows → Fin cols → Flat.GE) (i : Cm.Idx), Flat.Holds M i →
      weightsOfMatrix valid M = some (weightsOfIndex valid i)
  /-- All weights are the weights under the matrix of their own digits. -/
  everyWeights : ∀ weights : ModelWeights (VerifierAndGoals.settingsOfRead pp),
      ∃ i : Cm.Idx, weightsOfMatrix valid (Flat.matrixOf i) = some weights
  /-- The protocol's claim is the goals' claim, with "the model has a value on the window". -/
  twoSided : ∀ (rows cols : ℕ) (M : Fin rows → Fin cols → Flat.GE)
      (prompt output padding : List Token) (x : Instance ppref),
      requestOfTokens (prompt, output) padding = some x →
        (ModelSays pp M x ↔
          ∃ weights, weightsOfMatrix valid M = some weights ∧
            (modelNextToken (VerifierAndGoals.settingsOfRead pp) weights (windowOf x)).isSome = true ∧
            Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol weights prompt output)
  /-- At exact match the goals' claim is `VerifierAndGoals.ModelOutput`, of a non-empty output. -/
  exactMatch : pp.pol = AcceptancePolicy.exact → ∀ weights prompt output,
      (Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol weights prompt output ↔
        output ≠ [] ∧ VerifierAndGoals.ModelOutput (VerifierAndGoals.settingsOfRead pp) weights prompt output)
  /-- What can be served and meets the policy is built, and the protocol's claim holds of it. -/
  served : ∀ (i : Cm.Idx) (prompt output : List Token),
      CanServe (VerifierAndGoals.settingsOfRead pp) (weightsOfIndex valid i) prompt output →
      Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol (weightsOfIndex valid i) prompt output →
        ∃ x, requestOfTokens (prompt, output) [] = some x ∧ ModelSays pp (Flat.matrixOf i) x

/-- **The model of which the protocol's claim speaks is the model of the top statements**, at every
lawful table of scales and every policy. -/
def MeaningNextToken : Prop :=
  ∀ (pp : ScalesAndPolicy) (lawful : (Cm.Scales.of pp).Lawful),
    MeaningAt pp (settingsAreValid_settingsOf lawful)

/-! ## 3. The proof -/

/-- **A matrix of any shape holds at most one index.** Inside the reference shape two digits with
one residue are one; outside it both matrices of digits are 0. -/
theorem holds_unique {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE} {i i' : Cm.Idx}
    (h : Flat.Holds M i) (h' : Flat.Holds M i') : i = i' := by
  have hm : ∀ y c, i.mat y c = i'.mat y c := by
    intro y c
    by_cases hin : y < rows ∧ c < cols
    · by_cases hs : y < hRef ∧ c < 2 ^ kRef
      · have e : ((i.mat y c : ℤ) : Flat.GE) = ((i'.mat y c : ℤ) : Flat.GE) :=
          (h.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩).symm.trans (h'.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩)
        exact Flat.digit_eq (i.wf.1 y hs.1 c hs.2) (i'.wf.1 y hs.1 c hs.2) e
      · rw [show i.mat y c = 0 from Cm.ext_out i.val hs,
          show i'.mat y c = 0 from Cm.ext_out i'.val hs]
    · rw [h.2 y c hin, h'.2 y c hin]
  refine Subtype.ext ?_
  funext y c
  have e := hm y.val c.val
  unfold Cm.Idx.mat Cm.ext at e
  rw [dif_pos ⟨y.2, c.2⟩, dif_pos ⟨y.2, c.2⟩] at e
  exact e

/-- The index that a matrix holds. -/
theorem indexOf_eq {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE} {i : Cm.Idx}
    (h : Flat.Holds M i) : Flat.indexOf M = some i := by
  have hin : Flat.InRange M := ⟨i, h⟩
  unfold Flat.indexOf
  rw [dif_pos hin]
  exact congrArg some (holds_unique hin.choose_spec h)

/-- What `Flat.indexOf` returns is held. -/
theorem holds_of_indexOf {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE} {i : Cm.Idx}
    (h : Flat.indexOf M = some i) : Flat.Holds M i := by
  unfold Flat.indexOf at h
  split at h
  · rename_i hin
    obtain rfl := Option.some.inj h
    exact hin.choose_spec
  · cases h

section
variable {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)

theorem weightsOfMatrix_eq {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE} {i : Cm.Idx}
    (holds : Flat.Holds M i) : weightsOfMatrix valid M = some (weightsOfIndex valid i) := by
  unfold weightsOfMatrix
  rw [indexOf_eq holds]
  rfl

theorem exists_of_weightsOfMatrix {rows cols : ℕ} {M : Fin rows → Fin cols → Flat.GE}
    {weights : ModelWeights settings} (h : weightsOfMatrix valid M = some weights) :
    ∃ i : Cm.Idx, Flat.Holds M i ∧ weightsOfIndex valid i = weights := by
  obtain ⟨i, hi, e⟩ := Option.map_eq_some_iff.1 h
  exact ⟨i, holds_of_indexOf hi, e⟩

variable {scales : Cm.Scales} (lawful : scales.Lawful) (tie : settingsOf scales = settings)
include lawful tie

/-- **The integer program runs on a request's window exactly if the model has a value on it.** -/
theorem runs_iff_isSome (i : Cm.Idx) (x : Instance ppref) :
    RunsK ppref scales.kap scales.nf (fun _ => tbRef) i.index.val x.prompt ↔
      (modelNextToken settings (weightsOfIndex valid i) (windowOf x)).isSome = true := by
  have hT : ppref.T = 1024 := by decide
  have hlen : (IntegerModel.firstToks x 1024).length = 1024 := IntegerModel.firstToks_length x 1024
  unfold windowOf
  rw [Policy.modelNextToken_of_feeds (IntegerModel.committedOf scales lawful i)
    (weightsOfIndex valid i) (Policy.feeds_of_tie lawful valid tie i), Option.isSome_map]
  constructor
  · intro runs
    exact IntegerModel.model_isSome_of_window (IntegerModel.committedOf scales lawful i) x.prompt
      (IntegerModel.firstToks x 1024) (by omega) (by omega)
      (fun t ht => IntegerModel.firstToks_get x 1024 (by omega) t ht) runs
  · intro value
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 value
    exact IntegerModel.runs_of_full (IntegerModel.committedOf scales lawful i) x.prompt
      (IntegerModel.firstToks x 1024) (by omega)
      (fun t _ ht' => (IntegerModel.firstToks_get x 1024 (by omega) t ht').symm)
      (IntegerModel.model_some hy).1.2.2

/-- At an index: true under the policy exactly if the model has a value on the window and the output
meets the policy. -/
theorem isTrueUnder_iff (policy : AcceptancePolicy) (i : Cm.Idx) {x : Instance ppref}
    {prompt output padding : List Token}
    (built : requestOfTokens (prompt, output) padding = some x) :
    Policy.IsTrueUnder scales policy i x ↔
      (modelNextToken settings (weightsOfIndex valid i) (windowOf x)).isSome = true ∧
        Policy.MeetsPolicy settings policy (weightsOfIndex valid i) prompt output := by
  rw [Policy.isTrueUnder_iff_meetsPolicy lawful valid tie policy i built,
    runs_iff_isSome valid lawful tie i x]

/-- What can be served and meets the policy is built without padding, and is true. -/
theorem isTrueUnder_of_served (policy : AcceptancePolicy) (i : Cm.Idx) {prompt output : List Token}
    (canServe : CanServe settings (weightsOfIndex valid i) prompt output)
    (meets : Policy.MeetsPolicy settings policy (weightsOfIndex valid i) prompt output) :
    ∃ x, requestOfTokens (prompt, output) [] = some x ∧ Policy.IsTrueUnder scales policy i x := by
  have small : ∀ token ∈ prompt ++ output, token < ppref.V := fun token member => by
    have h := canServe.1 token member
    rwa [vocabulary_eq valid] at h
  obtain ⟨p, hp⟩ := IntegerModel.vocabularyTokens_of_small prompt fun token member =>
    small token (List.mem_append_left _ member)
  obtain ⟨o, ho⟩ := IntegerModel.vocabularyTokens_of_small output fun token member =>
    small token (List.mem_append_right _ member)
  obtain rfl : p.map Fin.val = prompt := map_val_of_vocabularyTokens prompt p hp
  obtain rfl : o.map Fin.val = output := map_val_of_vocabularyTokens output o ho
  have positions : settings.positions = ppref.T :=
    (Policy.feeds_of_tie lawful valid tie i).same.sizes.positions
  have fits : 0 < p.length ∧ 0 < o.length ∧ p.length + o.length ≤ ppref.T + 1 := by
    refine ⟨List.length_pos_of_ne_nil fun e => meets.promptNonempty (by rw [e]; rfl),
      List.length_pos_of_ne_nil fun e => meets.outputNonempty (by rw [e]; rfl), ?_⟩
    have h := meets.length_le
    rwa [List.length_map, List.length_map, positions] at h
  obtain ⟨x, hx⟩ : ∃ x, IntegerModel.requestOf p o [] = some x := by
    unfold IntegerModel.requestOf
    rw [dif_pos fits]
    exact ⟨_, rfl⟩
  have built : requestOfTokens (p.map Fin.val, o.map Fin.val) [] = some x :=
    (requestOfTokens_eq hp ho rfl).trans hx
  refine ⟨x, built, (isTrueUnder_iff valid lawful tie policy i built).2 ⟨?_, meets⟩⟩
  have value := canServe.2.2
  rw [IntegerModel.zeroFilledWindow_map, ← IntegerModel.firstToks_requestOf hx] at value
  exact value

end

/-- **The law.** -/
theorem meaning_nextToken : MeaningNextToken := fun pp lawful =>
  have valid := settingsAreValid_settingsOf lawful
  { package := fun _ _ _ _ _ => ⟨rfl, fun _ _ _ => Iff.rfl⟩
    sameFunction := fun i tokens => modelNextToken_eq_nextToken lawful valid rfl i tokens
    decoded := fun _ _ _ _ holds => weightsOfMatrix_eq valid holds
    everyWeights := fun weights =>
      ⟨indexOfWeights valid weights,
        (weightsOfMatrix_eq valid (Flat.holds_matrixOf _)).trans
          (congrArg some (weightsOfIndex_indexOfWeights valid weights))⟩
    twoSided := fun _ _ M _ _ _ x built => by
      constructor
      · rintro ⟨i, holds, isTrue⟩
        exact ⟨_, weightsOfMatrix_eq valid holds,
          (isTrueUnder_iff valid lawful rfl pp.pol i built).1 isTrue⟩
      · rintro ⟨weights, decoded, both⟩
        obtain ⟨i, holds, rfl⟩ := exists_of_weightsOfMatrix valid decoded
        exact ⟨i, holds, (isTrueUnder_iff valid lawful rfl pp.pol i built).2 both⟩
    exactMatch := fun exactMatch weights prompt output => by
      rw [exactMatch]
      exact Policy.meetsPolicy_exact_iff weights prompt output
    served := fun i _ _ canServe meets => by
      obtain ⟨x, built, isTrue⟩ := isTrueUnder_of_served valid lawful rfl pp.pol i canServe meets
      exact ⟨x, built, i, Flat.holds_matrixOf i, isTrue⟩ }

/-- **The law at the public files**: what the goals' reader returns has a lawful table of scales.
The proof of validity in a term's type does not matter: any two are equal. -/
theorem meaning_atFiles {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (isRead : VerifierAndGoals.readFiles Z = .ok pp) :
    MeaningAt pp (VerifierAndGoals.valid_of_read isRead) :=
  meaning_nextToken pp (Cm.lawful_of (OnBytes.Flat.settingsAtRef_lawful isRead))

/-! ## 4. The law is not empty, and its joint can fail -/

/-- **The joint is met**, at every lawful table of scales with exact match, the reference table
among them (`Cm.lawful_sRef`): after the prompt [0] the outputs [1] and [2] are each built into a
request of which ModelSays holds at a matrix of its own. Limits of these witnesses: the weights are
made up (under them the model answers one fixed token after any one token); each output has one
token; e < 1,024, so the announced token is not checked. Outputs of several tokens and the case
e = 1,024 have no witness here. -/
theorem modelSays_twice (pp : ScalesAndPolicy) (lawful : (Cm.Scales.of pp).Lawful)
    (exactMatch : pp.pol = AcceptancePolicy.exact) :
    ∃ (M M' : Fin hRef → Fin (2 ^ kRef) → Flat.GE) (x x' : Instance ppref),
      requestOfTokens ([0], [1]) [] = some x ∧ ModelSays pp M x ∧
      requestOfTokens ([0], [2]) [] = some x' ∧ ModelSays pp M' x' := by
  have valid := settingsAreValid_settingsOf lawful
  have law := meaning_nextToken pp lawful
  have go : ∀ v, v < 202048 → ∃ x, requestOfTokens ([0], [v]) [] = some x ∧
      ModelSays pp (Flat.matrixOf (Cm.biteI (fun _ => 0) fun _ => v)) x := fun v hv =>
    law.served _ [0] [v] (VerifierAndGoals.voting_served valid v hv).1
      ((law.exactMatch exactMatch _ _ _).2 ⟨by simp, (VerifierAndGoals.voting_served valid v hv).2⟩)
  obtain ⟨x, built, claim⟩ := go 1 (by decide)
  obtain ⟨x', built', claim'⟩ := go 2 (by decide)
  exact ⟨_, _, x, x', built, claim, built', claim'⟩

/-- The same at the library's reference table of scales: no premise is left. -/
theorem modelSays_twice_atRef :
    ∃ (M M' : Fin hRef → Fin (2 ^ kRef) → Flat.GE) (x x' : Instance ppref),
      requestOfTokens ([0], [1]) [] = some x ∧ ModelSays (Policy.ppOf Cm.sRef AcceptancePolicy.exact) M x ∧
      requestOfTokens ([0], [2]) [] = some x' ∧ ModelSays (Policy.ppOf Cm.sRef AcceptancePolicy.exact) M' x' :=
  modelSays_twice (Policy.ppOf Cm.sRef AcceptancePolicy.exact) Cm.lawful_sRef rfl

/-- **The joint can fail**: at the matrix of the all-zero weights, at exact match, ModelSays is
false of the output [1] after the prompt [0], whatever the padding. -/
theorem not_modelSays_zero_one (pp : ScalesAndPolicy) (lawful : (Cm.Scales.of pp).Lawful)
    (exactMatch : pp.pol = AcceptancePolicy.exact) (padding : List Token) (x : Instance ppref)
    (built : requestOfTokens ([0], [1]) padding = some x) :
    ¬ ModelSays pp (Flat.matrixOf (Cm.Idx.ofIndex ScalesSanity.iZero)) x := by
  intro claim
  have valid := settingsAreValid_settingsOf lawful
  have law := meaning_nextToken pp lawful
  obtain ⟨weights, decoded, -, meets⟩ := (law.twoSided _ _ _ _ _ _ _ built).1 claim
  rw [weightsOfMatrix_eq valid (Flat.holds_matrixOf _)] at decoded
  obtain rfl := Option.some.inj decoded
  exact VerifierAndGoals.not_modelOutput_zero_one valid ((law.exactMatch exactMatch _ _ _).1 meets).2

/-! ## 5. Where the law is spent -/

/-- **The compiler's named hypothesis on the meaning** (`CompilerSoundnessConditionStatements.soundFor`,
Johnson/Top/InnerCompiledVerifier.lean), from the law. For every input of the compiler whose indices are read
as matrices and whose instances are read as requests: if what its builder builds is what
`requestOfTokens` builds, and its relaxed relation gives `ModelSays`, then a built instance that is
true at an index has an output that meets pp's policy at the weights under that index's matrix. The
two premises are not shown here of any input: the second is the law on the protocol's last claims.
At a relation that never holds both the premise and the conclusion are met for nothing. -/
theorem soundFor_of_modelSays (pp : ScalesAndPolicy) (lawful : (Cm.Scales.of pp).Lawful)
    {r : InnerCompilerInput} (b : SoundnessAnalysisData r) {rows cols : ℕ}
    (matrix : r.Index → Fin rows → Fin cols → Flat.GE) (request : r.Instance → Instance ppref)
    (builds : ∀ x' a x, r.buildInstance x' a = some x → requestOfTokens x' a = some (request x))
    (gives : ∀ i x w, b.Rno i x w → ModelSays pp (matrix i) (request x)) :
    CompilerSoundnessConditionStatements.soundFor b fun i prompt output =>
      ∃ weights, weightsOfMatrix (settingsAreValid_settingsOf lawful) (matrix i) = some weights ∧
        Policy.MeetsPolicy (VerifierAndGoals.settingsOfRead pp) pp.pol weights prompt output :=
  fun i x' a x built ⟨w, holds⟩ =>
    have ⟨weights, decoded, _, meets⟩ :=
      ((meaning_nextToken pp lawful).twoSided _ _ _ _ _ _ _ (builds x' a x built)).1
        (gives i x w holds)
    ⟨weights, decoded, meets⟩

end VerifiableInference.Meaning

#print axioms VerifiableInference.Meaning.meaning_nextToken
#print axioms VerifiableInference.Meaning.meaning_atFiles
#print axioms VerifiableInference.Meaning.modelSays_twice_atRef
#print axioms VerifiableInference.Meaning.not_modelSays_zero_one
#print axioms VerifiableInference.Meaning.soundFor_of_modelSays
