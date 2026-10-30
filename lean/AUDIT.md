# FlashProve: the statements, as plain text

This page sets out, in plain text, what an auditor of the statements reads: the statements themselves, in Lean, with the file and line of each. The page to read is the HTML page, [STATEMENTS.html](STATEMENTS.html). Paths are from `lean/`. What FlashProve is: README.md. How to build these files: CHECKING.md. Each statement carries one mark, and the mark is the only status in it:

- **proved in Lean**: Lean's build of this repository has checked the proof.

## 1. What is claimed

At public files that the verifier takes, at the exact-match policy; all but soundness and the reply also ask that the files pass the test `protocolDataWellFormed` on the public files, which the verifier makes too (`FilesInUse`). One such set is known: the stored full-size files (`filesInUse_stored`). That set is a value written in Lean (`VerifierAndGoals.storedPublicFiles`), tied to no file on a disk. `compile flashProveAtFiles` is short for `finalSystem honestProversAndSettings files settings`; in `AtFullSide/Face/TheSixLines.lean` the same term is written `compile (flashProve setup)`.

The six theorems of that file ("the six lines"); the HTML page opens on them. As stated there all six ask `FilesInUse`; soundness and the reply need only `FilesTaken` (in scope, read as the parameters, exact match stated), not the test on the public files (`finalSound`, `finalRefusedHandsOutNoProof_value`).

- `sound`: `Sound (compile flashProveAtFiles) finalSoundnessError`: **proved in Lean**
- `soundAndBinding`: `SoundAndBinding (compile flashProveAtFiles) finalBindingError`: **proved in Lean**
- `completeOnCanServe`: `CompleteOn (compile flashProveAtFiles) CanServe 2^-40`: **proved in Lean**
- `zeroKnowledgeOnCanServe`: for some error that stays at or below 2^-154 up to 2^64 queries and 688127 replies, `ZeroKnowledgeOn (compile flashProveAtFiles) CanServe error`: **proved in Lean**
- `refusedHandsOutNoProof`: the reply: at a refused request every reply that the prover can return is the empty proof: **proved in Lean**
- `repliesFit`: the replies' numbers (`RepliesFit`): **proved in Lean**

Behind the six:

- equivalent to `completeOnCanServe`, and drawn from it (`completeAtWellFormedRequests`): `ProofAcceptedWhere (compile flashProveAtFiles) WellFormedRequest modelResult 2^-40`: **proved in Lean**
- from `zeroKnowledgeOnCanServe` and `refusedHandsOutNoProof` (`zeroKnowledgeAtEveryRequest`): `ZeroKnowledgeBelowWhere (compile flashProveAtFiles) (fun _ => True) requestOutcome (2^64) 688127 2^-154`: **proved in Lean**
- as a corollary, `ZeroKnowledgeShownBelowWhere (compile flashProveAtFiles) WellFormedRequest requestLabel (2^64) 688127 2^-154`: **proved in Lean**
- as a corollary, the reply with its label: its label is `requestLabel`'s, and outside served it holds no proof: **proved in Lean**
- `((compile flashProveAtFiles).verify …).evaluate blake2bHash` is `finalVerifierProgram`: **proved in Lean**
- `leanVerifier`, which is `(compile flashProveAtFiles).accepts blake2bHash`, is `finalVerifierProgram` at a public setup's files (`leanVerifier_eq`): **proved in Lean**
- for every public setup, `executableVerifier`, a definition that Lean compiles, applied to the setup's public files, returns the verdict of `leanVerifier` (`executableVerifier_eq_leanVerifier`): **proved in Lean**
- `verdictOf`, the parts of which the command `lean-verify` calls, parses the claim from the user's files (`claimOf`) and applies `executableVerifier` to it (`verdictOf_eq_executableVerifier`): **proved in Lean**
- `compile flashProveAtFiles`'s verifier is `VerifierAndGoals.verify`, the Lean verifier of lean/THEOREM.md, at the description of the soundness theorem on `verify` (`compile_flashProve_verify_eq`): **proved in Lean**

In the file of the structure `FinalStatementOneBit` (`Johnson/Face/FinalStatementOneBit.lean`) the error of the zero-knowledge line is a parameter; 2^-154 is the least power of two that fits the theorem below; it is not a chosen target.

The six lines' statements, with what they name in their own file, the Lean verifier, and the two that stand behind them. Mark of each theorem: **proved in Lean**.

`AtFullSide/Face/TheSixLines.lean:69`

```lean
structure PublicSetup where
  /-- The three public files. -/
  files : PublicFiles
  /-- What the reader returns at them. -/
  readParameters : Inst.Model.ScalesAndPolicy
  /-- They are in scope, read so, state exact match and pass the test. -/
  inUse : FilesInUse files readParameters
```

`AtFullSide/Face/TheSixLines.lean:82`

```lean
def flashProve (setup : PublicSetup) : Compilable :=
  flashProveAtFiles setup.files (settingsOfRead setup.readParameters)
    (honestProversAndSettings setup.files (settingsOfRead setup.readParameters))
```

`AtFullSide/Face/TheSixLines.lean:93`

```lean
theorem sound (setup : PublicSetup) : Sound (compile (flashProve setup)) finalSoundnessError
```

`AtFullSide/Face/TheSixLines.lean:99`

```lean
theorem soundAndBinding (setup : PublicSetup) :
    SoundAndBinding (compile (flashProve setup)) finalBindingError
```

`AtFullSide/Face/TheSixLines.lean:106`

```lean
theorem completeOnCanServe (setup : PublicSetup) :
    CompleteOn (compile (flashProve setup)) (CanServe (settingsOfRead setup.readParameters))
      finalCompletenessError
```

`AtFullSide/Face/TheSixLines.lean:122`

```lean
theorem zeroKnowledgeOnCanServe (setup : PublicSetup) :
    ∃ error : ℕ → ℕ → ℝ≥0∞,
      (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ finalZeroKnowledgeError) ∧
      ZeroKnowledgeOn (compile (flashProve setup))
        (CanServe (settingsOfRead setup.readParameters)) error
```

`AtFullSide/Face/TheSixLines.lean:134`

```lean
theorem refusedHandsOutNoProof (setup : PublicSetup) :
    HandsOutNoProof (compile (flashProve setup))
      (fun weights request =>
        requestOutcome (settingsOfRead setup.readParameters) weights request = .refused)
      isNoProof
```

`AtFullSide/Face/TheSixLines.lean:144`

```lean
theorem repliesFit (setup : PublicSetup) :
    finalReplyCount ≤ onlineRunsPerCopy setup ∧
      (∀ reading, TableBudgetFits ((flashProve setup).settings reading).furtherCopies
        (onlineRunsPerCopy setup)) ∧
      WithinBudget (compile (flashProve setup)) honestQueryBudget
```

`AtFullSide/Face/TheSixLines.lean:155`

```lean
def leanVerifier (setup : PublicSetup) :
    Commitment → List Token → List Token → (compile (flashProve setup)).Proof → Bool :=
  (compile (flashProve setup)).accepts blake2bHash
```

`AtFullSide/Face/TheSixLines.lean:161`

```lean
theorem leanVerifier_eq (setup : PublicSetup) (commitment : Commitment) (prompt output : List Token)
    (form : flashProveDescription.Form) :
    leanVerifier setup commitment prompt output form =
      finalVerifierProgram setup.files (settingsOfRead setup.readParameters) commitment prompt
        output form
```

`AtFullSide/Face/TheSixLines.lean:173`

```lean
theorem completeAtWellFormedRequests (setup : PublicSetup) :
    ProofAcceptedWhere (compile (flashProve setup))
      (WellFormedRequest (settingsOfRead setup.readParameters))
      (modelResult (settingsOfRead setup.readParameters)) finalCompletenessError
```

`AtFullSide/Face/TheSixLines.lean:213`

```lean
theorem zeroKnowledgeAtEveryRequest_of_lines (setup : PublicSetup)
    (onCanServe : ∃ error : ℕ → ℕ → ℝ≥0∞,
      (∀ asked replies, asked ≤ finalVerifierQueries → replies ≤ finalReplyCount →
        error asked replies ≤ finalZeroKnowledgeError) ∧
      ZeroKnowledgeOn (compile (flashProve setup))
        (CanServe (settingsOfRead setup.readParameters)) error)
    (refused : HandsOutNoProof (compile (flashProve setup))
      (fun weights request =>
        requestOutcome (settingsOfRead setup.readParameters) weights request = .refused)
      isNoProof) :
    ZeroKnowledgeBelowWhere (compile (flashProve setup)) (fun _ => True)
      (requestOutcome (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      finalZeroKnowledgeError
```

`AtFullSide/Face/TheSixLines.lean:235`

```lean
theorem zeroKnowledgeAtEveryRequest (setup : PublicSetup) :
    ZeroKnowledgeBelowWhere (compile (flashProve setup)) (fun _ => True)
      (requestOutcome (settingsOfRead setup.readParameters)) finalVerifierQueries finalReplyCount
      finalZeroKnowledgeError
```

The two properties on the requests that can be served, the simulator and the two experiments of the second, that condition, and two names more of the lines above:

`VerifiableInference/Steps.lean:21`

```lean
def CompleteOn (system : ArgumentSystem) (domain : system.Weights → List Token → List Token → Prop)
    (α : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (prompt output : List Token),
    domain weights prompt output → system.IsModelOutput weights prompt output →
      Prob (do
          let randomness ← system.sampleCommitmentRandomness
          let commitment ← (system.commit weights randomness).toRandomized
          let proof ← system.prove weights randomness prompt output
          (system.verify commitment prompt output proof).toRandomized)
        {accepted | accepted = false}
        ≤ α
```

`VerifiableInference/MoreStatements.lean:151`

```lean
def ZeroKnowledgeOn (system : ArgumentSystem) (domain : system.Weights → List Token → List Token →
    Prop) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ simulator : Simulator system.PublicParameters system.Proof,
    ∀ (weights : system.Weights)
      (chooser : View system.Proof → Option (List Token × List Token)),
      (∀ view prompt output, chooser view = some (prompt, output) → domain weights prompt output ∧
          system.IsModelOutput weights prompt output) →
      ∀ (queries : ℕ) (verifier : Commitment → MaliciousVerifier system.Proof) (proofCount : ℕ),
        (∀ commitment, (verifier commitment).QueryBound queries) →
          statisticalDistance
              (Prob (realExperiment system verifier chooser weights proofCount))
              (eventProbability (simulatedExperiment system simulator verifier chooser weights
                  proofCount))
            ≤ ζ queries proofCount
          ∧ eventProbability (simulatedExperiment system simulator verifier chooser weights
              proofCount)
              {view | ¬ view.queryLog.Consistent} = 0
```

`VerifiableInference/Statements.lean:248`

```lean
structure Simulator (PublicParameters Proof : Type) where
  State : Type
  start : PublicParameters → ℕ → PMF (Commitment × State)
  answerQuery : State → BitString → PMF (Digest × State)
  simulateProof : State → List Token × List Token → PMF (Proof × State)
```

`VerifiableInference/Statements.lean:235`

```lean
def realExperiment (system : ArgumentSystem) (verifier : Commitment → MaliciousVerifier
    system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token))
    (weights : system.Weights) (proofCount : ℕ) : RandomizedAlgorithm (View system.Proof) := do
  let randomness ← system.sampleCommitmentRandomness
  let commitment ← (system.commit weights randomness).toRandomized
  realSteps system chooser weights randomness (verifier commitment) proofCount
      ⟨commitment, [], [], []⟩
```

`VerifiableInference/Statements.lean:281`

```lean
def simulatedExperiment (system : ArgumentSystem)
    (simulator : Simulator system.PublicParameters system.Proof)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option (List Token × List Token))
    (weights : system.Weights) (proofCount : ℕ) : PMF (View system.Proof) :=
  (simulator.start (system.publicParameters weights) proofCount).bind fun started =>
    simulatedSteps simulator chooser (verifier started.1) proofCount ⟨started.1, [], [], []⟩
        started.2
```

`VerifiableInference/CanServe.lean:31`

```lean
def CanServe (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) : Prop :=
  (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] ∧
    (modelNextToken settings weights
      (IntegerModel.zeroFilledWindow prompt output)).isSome = true
```

`AtFullSide/Face/TheSixLines.lean:88`

```lean
abbrev onlineRunsPerCopy (setup : PublicSetup) : ℕ :=
  (honestProversAndSettings setup.files (settingsOfRead setup.readParameters)).onlineRunsPerCopy
```

`VerifiableInference/Statements.lean:62`

```lean
def ArgumentSystem.accepts (system : ArgumentSystem) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token)
    (proof : system.Proof) : Bool :=
  (system.verify commitment prompt output proof).evaluate hash
```

`CanServe`: every token is in the vocabulary, the output is not empty, and the model has a value on the whole window of 1,024 tokens. `CanServe` alone does not say that the output is the model's: both properties ask that beside it. The last condition depends on the weights. What goes with the two lines on it, in the file's own words:

- `completeOnCanServe`: **Completeness** as the general property CompleteOn (VerifiableInference/Steps.lean), at the requests that can be served. Nothing is said of a request outside CanServe, among them those where the model has no result, or of an output that is not the model's.
- `zeroKnowledgeOnCanServe`: **Zero knowledge** on the requests that can be served and whose output tokens are the model's (ZeroKnowledgeOn, VerifiableInference/MoreStatements.lean): its own simulator, which is handed nothing of the weights in the experiment. It may depend on the public files; what these tell of the weights is not counted. Whether a request can be served depends on the weights, and that is not hidden: the chooser of requests may know the weights and is the same in both experiments. It says nothing of a refused request by itself: with refusedHandsOutNoProof it gives zeroKnowledgeAtEveryRequest, within the same bar, in which the simulator is told one bit for each request: served or refused. One request to a proof and one commitment are covered, not batches. The bound is not a named function: the statement says that there is one, and that it stays at or below finalZeroKnowledgeError within the stated limits; ZeroKnowledgeOn takes it as an argument.

The limits under points 2 and 3 below hold of these two as well.

One structure, `FinalStatementOneBit`, at `honestProversAndSettings`, the honest provers and settings, has six fields, points 1 to 6 below: `sound`, `binding`, `handsOutNoProof` and `repliesFit`, of which the theorems `sound`, `soundAndBinding`, `refusedHandsOutNoProof` and `repliesFit` are the cases at a public setup; `complete`, completeness in the equivalent form of point 2; and `zeroKnowledge`, point 3, which follows from the lines above and is not proved to give `zeroKnowledgeOnCanServe` back. `finalSystem honest files settings` is `compile (flashProveAtFiles files settings (honest files settings))`.

`Johnson/Face/FinalStatementOneBit.lean:44`

```lean
structure FinalStatementOneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop where
  sound : FinalSound honest
  complete : FinalComplete honest
  zeroKnowledge : FinalZeroKnowledgeOneBit honest zeroKnowledgeError
  binding : FinalSoundAndBinding honest
  handsOutNoProof : FinalRefusedHandsOutNoProof honest
  repliesFit : RepliesFit honest
```

The corollary's statement, and the theorem that draws it from the one above:

`Johnson/Face/FinalStatement.lean:338`

```lean
structure FinalStatement (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop where
  sound : FinalSound honest
  complete : FinalComplete honest
  zeroKnowledge : FinalZeroKnowledge honest zeroKnowledgeError
  binding : FinalSoundAndBinding honest
  handsOutNoProof : FinalHandsOutNoProof honest
  repliesFit : RepliesFit honest
```

`AtFullSide/Face/TheFinalStatementOneBitHolds.lean:49`

```lean
theorem finalStatement_of_oneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (statement : FinalStatementOneBit honest zeroKnowledgeError) :
    FinalStatement honest zeroKnowledgeError
```

`AtFullSide/Face/HonestProversAndSettingsValue.lean:32`

```lean
noncomputable def honestProversAndSettings : HonestProversAndSettings := honestProversAndSettingsOf thePartsAt
```

**1. `sound`.** Under a random hash function, an output that is not that of the weights that an extractor reads off the commitment and the committer's queries is accepted with probability at most finalSoundnessError (about q/2^124 + 2^-101 after q hash queries). The extractor is a function, not shown computable. Theorem at `honestProversAndSettings`: `finalSound`. Mark: **proved in Lean**.

`Johnson/Face/FinalStatement.lean:255`

```lean
def FinalSound (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    SoundAtFiles honest files parameters
```

`Johnson/Face/FinalStatement.lean:251`

```lean
def SoundAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  Sound (finalSystem honest files (settingsOfRead parameters)) finalSoundnessError
```

**2. `complete`.** For one commitment and one well-formed request, if the model's result is the claimed tokens, the honest proof is accepted, except with probability at most 2^-40, over the hash function and the committer's and the prover's coins. Theorem at `honestProversAndSettings`: `finalAtT1_filled_withRoom`. Mark: **proved in Lean**.

`Johnson/Face/FinalStatement.lean:266`

```lean
def FinalComplete (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    CompleteAtFiles honest files parameters
```

`Johnson/Face/FinalStatement.lean:260`

```lean
def CompleteAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ProofAcceptedWhere (finalSystem honest files (settingsOfRead parameters))
    (WellFormedRequest (settingsOfRead parameters)) (modelResult (settingsOfRead parameters))
    finalCompletenessError
```

**3. `zeroKnowledge`.** A simulator that may depend on the public files and is told, of each request, well-formed or not, only one bit (served or refused: a request is refused if it is ill-formed, if the model has no result on it, or if its result is other tokens) makes the commitment, the replies (each a proof or the empty proof (`noProofForm`: a form all of whose parts are empty)) and the hash answers; for one commitment with one copy of the table, up to 688127 replies and 2^64 queries, its view is within the error of the real one. Theorem at `honestProversAndSettings`: `finalZeroKnowledgeOneBit_value`. As a corollary (`finalZeroKnowledge_of_oneBit`), for a service that chooses to say "failed": the same at every well-formed request, with one label for it (served, failed or other tokens) told to the simulator and shown beside each proof. With the label a verifier learns, for every request of its choice, which of the three holds, and so, over many requests, where the model has no result. No statement bounds what many labels reveal together. Mark, of the line and of its corollary: **proved in Lean**.

`Johnson/Face/Checks.lean:106`

```lean
def FinalZeroKnowledgeOneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ZeroKnowledgeBelowWhere (finalSystem honest files (settingsOfRead parameters)) (fun _ => True)
      (requestOutcome (settingsOfRead parameters)) finalVerifierQueries finalReplyCount
      zeroKnowledgeError
```

The theorem that draws the corollary, and the corollary's definitions:

`Johnson/Face/FinalStatementOneBit.lean:54`

```lean
theorem finalZeroKnowledge_of_oneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (oneBit : FinalZeroKnowledgeOneBit honest zeroKnowledgeError) :
    FinalZeroKnowledge honest zeroKnowledgeError
```

`Johnson/Face/FinalStatement.lean:279`

```lean
def FinalZeroKnowledge (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ZeroKnowledgeAtFiles honest zeroKnowledgeError files parameters
```

`Johnson/Face/FinalStatement.lean:271`

```lean
def ZeroKnowledgeAtFiles (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ZeroKnowledgeShownBelowWhere (finalSystem honest files (settingsOfRead parameters))
    (WellFormedRequest (settingsOfRead parameters)) (requestLabel (settingsOfRead parameters))
    finalVerifierQueries finalReplyCount zeroKnowledgeError
```

*What the compiled zero-knowledge line says, read down to its definitions.* The hash function is drawn at random. Take any public files that the verifier takes, whose policy is exact match and which pass the test on the public files; the stored full-size files are such a set. Then there is one simulator, fixed before the weights, which may depend on the public files. For all weights and for any verifier that queries the hash function classically, with no bound on its running time: the verifier gets one commitment and then, in any order and adaptively, asks up to 2^64 hash queries and up to 688,127 replies, each at a request, well-formed or not, that is picked from all it has seen so far. What it sees with the honest Lean committer and prover (the commitment, the replies, the hash answers, its own coins) is within 2^-157 + 688,127 · 2^-174, which is below 2^-154, in total variation, of what the simulator makes. The simulator gets each request, the largest number of replies and, of the weights, one bit for each request: served or refused (in the corollary, one label for each request: served, failed or other tokens). It makes the commitment and the replies, and it answers the hash queries in the hash function's place, never one query in two ways. The probability is over the hash function, the committer's and the prover's coins and the verifier's own. In the error, 2^-157 is what the hashing costs at these numbers, and 2^-174 bounds the chance, before hashing, for a served request, over the verifier's messages that pass the proof-of-work tests, that the online prover stops for a reason that depends on its secrets (it is counted once for each reply); for the offline and the link prover that chance is 0. A nonce search that runs out is inside what is simulated: it shows as the empty proof at a served request, which looks like the reply to a refused request; in the corollary, as the empty proof beside the label "served".

*Its bounds.* One commitment with one copy of the table, one request per proof, exact match. The committed table of weights is stored encoded, with random masks, and each proof opens some of its columns. One encoding bears only so many openings before its masks are used up: 44,040,191 columns, enough for 688,127 replies. To serve more under one commitment, the protocol makes further encodings of the same table ("copies"), each tied to the commitment's key file by a link proof. The zero-knowledge line is about a prover with exactly one copy, and that number sits inside the value `honestProversAndSettings`, in its settings. The bit depends on the weights, and it is declared, not hidden: for every request of its choice a verifier learns whether the claimed output is the model's result. (It reads the bit off the reply: a refused request gets an empty proof; so, with small probability, does a served one, where a search for a nonce runs out.) So over many requests, chosen adaptively, it learns what the model outputs on inputs of its choice: whoever tries each candidate token for a prompt learns the model's next one from this bit alone, unless all are refused. Against three labels it hides one thing: whether a refusal means that the model has no result or that its result is other tokens. It hides that only from a verifier that asks few requests. A request's window (the 1,024 tokens that the model's run reads: the prompt, the claimed output, then zeros) can itself be sent as a prompt, with one more token as the claimed output, which the run does not read: a verifier that tries every candidate for that token and is refused each time learns that the model has no result on that window, and one that is served once learns that it has one (argued from the definitions; no theorem states it). Each such search costs up to 202,048 of the 688,127 replies. A true output is refused if the model has no value further on in the window. No statement bounds what many bits reveal together. Nothing in the prover counts replies, and beyond these numbers the line says nothing. It says nothing of what the public files themselves tell of the weights, or of timing: it's about the Lean prover as a definition, default values included. The simulator's running time isn't modelled. The verifier has no hash query before the commitment, and the weights and the public files are fixed before the hash function is drawn. A second, fixed hash function inside the format isn't treated as random. In the same Lean value stand soundness, binding and completeness of the same committer, prover and verifier, so the line isn't met by a prover that hands out nothing.

**4. `binding`.** Soundness, and binding of the same committer: an opening of the commitment to other weights than the extractor gives is rarely found. Theorem at `honestProversAndSettings`: `finalSoundAndBinding_value`. Mark: **proved in Lean**.

`Johnson/Face/FinalStatement.lean:288`

```lean
def FinalSoundAndBinding (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    BindingAtFiles honest files parameters
```

`Johnson/Face/FinalStatement.lean:284`

```lean
def BindingAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  SoundAndBinding (finalSystem honest files (settingsOfRead parameters)) finalBindingError
```

`Johnson/Face/FinalBindingLines.lean:43`

```lean
def FinalSoundOpened (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    SoundOpened (finalSystem honest files (settingsOfRead parameters))
      fun queries => 2 * finalBindingError queries
```

`finalSoundOpened_value`, AtFullSide/Face/FinalBindingAtTheValue.lean: **proved in Lean**. To open is to name weights and one number for the committer's randomness. That names fewer openings than any choice of coins would: nothing is said of an opening in which the salts of the first table's leaves have another public start or another length. At a small `coinBound` binding would say next to nothing: at 0 there is one setting of coins. At the honest provers and settings of the six theorems the bound leaves none of these out: `coinBound` + 1 is the committer's whole range, and at public files in use every encoding randomness of the first table and every member of the list of its salts are named together by a number up to `coinBound` (a theorem: `AtFullSide/Face/FinalBindingOpeningsAtHonestProversAndSettingsOf.lean:39`). No number is given for `coinBound`. Nothing is said of two openings to the same weights, or of several commitments. The commitment covers the first table's root, its out-of-domain sample and a part of what is read off the public files, and not the key file's proofs, copies or links. Soundness holds whatever the honest provers and settings, binding for all whose tables' salts have one length, the same whatever the public readings return: they read no prover. The extractor is a function, not shown computable.

**5. `handsOutNoProof`.** At a refused request every reply that the prover can return is the empty proof. Theorem at `honestProversAndSettings`: `finalRefusedHandsOutNoProof_value`. As a corollary (`finalHandsOutNoProof_of_refused`): at every request the label of the reply is requestLabel's, and outside served the form beside it holds no proof. Mark, of the line and of its corollary: **proved in Lean**.

`Johnson/Face/FinalStatementOneBit.lean:38`

```lean
def FinalRefusedHandsOutNoProof (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    RefusedHandsOutNoProofAtFiles honest files parameters
```

`Johnson/Face/FinalStatementOneBit.lean:30`

```lean
def RefusedHandsOutNoProofAtFiles (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  HandsOutNoProof (finalSystem honest files (settingsOfRead parameters))
    (fun weights request => requestOutcome (settingsOfRead parameters) weights request = .refused)
    isNoProof
```

The theorem that draws the corollary, and the corollary's definitions:

`AtFullSide/Face/TheFinalStatementOneBitHolds.lean:36`

```lean
theorem finalHandsOutNoProof_of_refused (honest : HonestProversAndSettings)
    (refused : FinalRefusedHandsOutNoProof honest) : FinalHandsOutNoProof honest
```

`Johnson/Face/FinalStatement.lean:305`

```lean
def FinalHandsOutNoProof (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    ReplyAtFiles honest files parameters
```

`Johnson/Face/FinalStatement.lean:294`

```lean
def ReplyAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ∀ (weights : ModelWeights (settingsOfRead parameters))
    (randomness : (finalSystem honest files (settingsOfRead parameters)).CommitmentRandomness)
    (request : Request) (hash : Hash) (answer : Label × flashProveDescription.Form),
    (reply (finalSystem honest files (settingsOfRead parameters))
        (requestLabel (settingsOfRead parameters)) weights randomness request.1 request.2).run
        hash answer ≠ 0 →
      answer.1 = requestLabel (settingsOfRead parameters) weights request ∧
        (answer.1 ≠ .served → isNoProof answer.2)
```

**6. `repliesFit`.** The numbers that the proof of zero knowledge reads: the replies are at most a stated number of runs of the online IOP a copy, at which the opened columns fit each table; and one run of the sampler, one of the committer and one of the prover together stay within 2^48 hash queries. Theorem at `honestProversAndSettings`: `finalAtT1_filled_withRoom`. Mark: **proved in Lean**.

`Johnson/Face/FinalStatement.lean:331`

```lean
def RepliesFit (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    RepliesFitAtFiles honest files parameters
```

`Johnson/Face/FinalStatement.lean:323`

```lean
def RepliesFitAtFiles (honest : HonestProversAndSettings) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  finalReplyCount ≤ (honest files (settingsOfRead parameters)).onlineRunsPerCopy ∧
    (∀ reading, TableBudgetFits
      ((honest files (settingsOfRead parameters)).compiledSettings reading).furtherCopies
      (honest files (settingsOfRead parameters)).onlineRunsPerCopy) ∧
    WithinBudget (finalSystem honest files (settingsOfRead parameters)) honestQueryBudget
```

`finalSound` rests on `VerifierAndGoals.AtTheName.sound_of_verify_at`, the soundness theorem on `verify`, whatever the honest provers and settings. Mark of that theorem: **proved in Lean**.

**The theorem that has all six fields of the final statement.** Mark: **proved in Lean**. Its statement, as the file has it:

`AtFullSide/Face/TheFinalStatementOneBitHolds.lean:65`

```lean
theorem theFinalStatementOneBitHolds_at {zeroKnowledgeError : ℝ≥0∞}
    (room : stepErrorAtTheStops ≤ zeroKnowledgeError) :
    FinalStatementOneBit honestProversAndSettings zeroKnowledgeError
```

`AtFullSide/Face/TheFinalStatementOneBitHolds.lean:77`

```lean
theorem theFinalStatementOneBitHolds : FinalStatementOneBit honestProversAndSettings finalZeroKnowledgeError
```

`AtFullSide/Face/TheFinalStatementOneBitHolds.lean:81`

```lean
theorem theFinalStatementBothHold :
    FinalStatementOneBit honestProversAndSettings finalZeroKnowledgeError ∧
      FinalStatement honestProversAndSettings finalZeroKnowledgeError
```


The sum in the first form, `stepErrorAtTheStops`, is 2^-157, for the compiled step, plus the interactive errors 0 and 0 and 688127 times 2^-174. `finalZeroKnowledgeError` is 2^-154: the least power of two that fits. It is not a chosen target.

`FinalStatement`, the six fields with the label shown, has a theorem of its own too, `theFinalStatementHolds` (`AtFullSide/Face/TheFinalStatementHolds.lean`). The six fields at the stored files, `statementAtStoredFiles_holds` (the same file), are drawn from that theorem: they show the label, and have no form with the bit.

**The executable Lean verifier.** Mark: **proved in Lean**.

`Johnson/Face/ExecutableVerifier.lean:52`

```lean
theorem finalSystem_verifier_at_blake2b (honest : HonestProversAndSettings) (files : PublicFiles) (settings : Settings)
    (commitment : Commitment) (prompt output : List Token) (form : flashProveDescription.Form) :
    ((finalSystem honest files settings).verify commitment prompt output form).evaluate
        blake2bHash =
      finalVerifierProgram files settings commitment prompt output form
```

`Johnson/Face/FinalStatement.lean:351`

```lean
def finalVerifierProgram (files : PublicFiles) (settings : Settings) (commitment : Commitment)
    (prompt output : List Token) (form : flashProveDescription.Form) : Bool :=
  (finalVerifier files settings commitment prompt output form).evaluate blake2bHash
```

`Johnson/Face/ExecutableVerifier.lean:40`

```lean
theorem verdictOf_eq_finalVerifierProgram (g : PV.Program.Given) (c : PV.Program.Claim)
    (reads : PV.Program.claimOf g = some c) (settings : Settings) :
    PV.Program.verdictOf g =
      some (finalVerifierProgram (PV.Program.pubOf g) settings c.commitment c.prompt c.output
        (PV.Program.formOf g c))
```

`AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean:40`

```lean
def executableVerifier (files : PublicFiles) (commitment : Commitment) (prompt output : List Token)
    (proof : FlashProve.FormBytes) : Option Bool :=
  PV.Ride.verdictThe files _root_.Fmt.oracle proof
    (PV.Ride.rideThe files _root_.Fmt.oracle proof commitment prompt output)
```

`AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean:47`

```lean
theorem executableVerifier_eq_leanVerifier (setup : PublicSetup) (commitment : Commitment)
    (prompt output : List Token) (proof : FlashProve.FormBytes) :
    executableVerifier setup.files commitment prompt output proof =
      some (leanVerifier setup commitment prompt output proof)
```

`AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean:60`

```lean
theorem verdictOf_eq_executableVerifier (given : PV.Program.Given) :
    PV.Program.verdictOf given =
      (PV.Program.claimOf given).bind fun claim =>
        executableVerifier (PV.Program.pubOf given) claim.commitment claim.prompt claim.output
          (PV.Program.formOf given claim)
```

`AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean:69`

```lean
theorem verdictOf_eq_leanVerifier (setup : PublicSetup) (given : PV.Program.Given)
    (claim : PV.Program.Claim) (sameFiles : PV.Program.pubOf given = setup.files)
    (reads : PV.Program.claimOf given = some claim) :
    PV.Program.verdictOf given =
      some (leanVerifier setup claim.commitment claim.prompt claim.output
        (PV.Program.formOf given claim))
```

`executableVerifier_eq_leanVerifier` applies only when the public files are those of a public setup. The command `lean-verify` does not enforce this: it does not reject public files that specify a policy other than exact match. `verdictOf_eq_leanVerifier` is the same fact, stated for `verdictOf`; it therefore has two further hypotheses: the claim can be parsed, and the public files are those of the setup. No theorem shows that `claimOf` implements the file format, and no theorem covers the parser outside Lean or the run itself. "Executable" means that Lean compiles the definition of `executableVerifier`, which is not marked noncomputable; Lean's list of axioms for it also names the axiom of choice (GAPS.md, 56).

**How these theorems stand.** The theorems named in this section and in Appendix D are part of this repository's Lean build, and for each Lean prints no axiom beyond its three standard ones (`propext`, `Classical.choice`, `Quot.sound`). Those whose files lie under `lean/AtFullSide/` stand in the side library, the others in the main library. The side library rests on a third, `lean/ShapeLines/`: these two need larger thread stacks and a large machine to build ([CHECKING.md](CHECKING.md)). The independent checker has been run, on the export of the soundness theorem on `verify` and, by name, on those of `sound`, `repliesFit` and `refusedHandsOutNoProof`, as the exporter writes them over a build of this repository's files; what it accepted: [CHECK-RESULTS.md](CHECK-RESULTS.md). The Lean verifier's reference run has been made over this repository's Lean files (what was run, and what came of it: [CHECK-RESULTS.md](CHECK-RESULTS.md)). A whole run of the library's full check over this repository's Lean files passed at every step; its last line says that no theorem got a verdict on binders or on `Classical.choice` (the whole line, and what the check doesn't cover: [CHECK-RESULTS.md](CHECK-RESULTS.md)). Some constants beneath the side library's theorems fail in Lean's kernel at the default thread stack and pass at a larger one, at which that library is compiled; `leanchecker`, which has no option for the stack, fails on them, so the script does not hand them to it: all twenty-three modules of that library that are shown to need the larger stack, with every other module of `AtFullSide/` and `ShapeLines/`, are sent past `leanchecker` by the script, to Lean's own replay at the wider stack (CHECKING.md; LIMITS.md, L69). (Seen for twenty-two in runs over Lean files that differ from this repository's, GAPS.md, 73, and for `AtFullSide/Layout/TieRfl.lean` on two machines, `scripts/RULES.txt`.) By import lines modules that hold such constants lie beneath the modules of `complete_in_scope`, `zkOnServedRequests_inScope`, `completeOnServedRequests_at_every_files_in_use`, `finalAtT1_filled_withRoom`, `threeAtFiles_in_use`, `theFinalStatementHolds`, `finalZeroKnowledgeOneBit_value`, `finalRefusedHandsOutNoProof_value`, `theFinalStatementOneBitHolds`, `theHonestPart_complete_where_the_worst_case_check_passes` and `theHonestPart_complete_where_some_worst_case_check_passes` (these two are the completeness theorem at weights that pass a worst-case check, in two forms: LIMITS.md, L93), and of `finalSoundAndBinding_value` and `rejectsNoProof_value`; `lean/ShapeLines/` lies beneath those of the first eleven and not of these two. By a walk over the constants of the build of this repository's files that [CHECK-RESULTS.md](CHECK-RESULTS.md) tells as made in seven calls, proofs included (a program's finding, no theorem; it takes as given the twenty-three modules that GAPS.md, 73, names, and measures no stack), `finalSoundAndBinding_value`, `rejectsNoProof_value` and `finalRefusedHandsOutNoProof_value` (and `finalHandsOutNoProof_value`, which this page does not otherwise name) reach no constant of these modules, and each of the others reaches at least one. One Lean file, with one definition and four theorems, which nothing else imports, was added after the runs reported here and checked on its own. Three of the check script's pinned values were changed and three of its stored lists were extended for it; nothing else in the script or the lists changed. That file's theorems were not in that walk.

- `theFinalStatementHolds, theFinalStatementHolds_at, statementAtStoredFiles_holds`: `AtFullSide/Face/TheFinalStatementHolds.lean`
- `theFinalStatementOneBitHolds`, `theFinalStatementBothHold`, `finalRefusedHandsOutNoProof_value`: `AtFullSide/Face/TheFinalStatementOneBitHolds.lean`
- `finalZeroKnowledgeOneBit_value`: `AtFullSide/CompletenessAndZeroKnowledge/OneBitAtHonestProversAndSettings.lean`
- `rejectsNoProof_value`: `AtFullSide/CompletenessAndZeroKnowledge/RejectsTheEmptyForm.lean`
- `finalAtT1_filled_withRoom`: `AtFullSide/E2E/TheCompiledStepFilled.lean`
- `finalSoundAndBinding_value`: `AtFullSide/Face/FinalBindingAtTheValue.lean`
- `threeAtFiles_in_use`: `AtFullSide/Face/TheThreeAtTheFiles.lean`
- `executableVerifier_eq_leanVerifier`, `executableVerifier_eq_leanVerifier_stored`, `verdictOf_eq_executableVerifier`, `verdictOf_eq_leanVerifier`: `AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean`

At BLAKE2b no theorem shows that `verify` accepts anything: there it is tested by runs.

**What these lines do not say.**

- They are about `honestProversAndSettings` exactly as written. It is one closed term: default values stand in it at named places, the online prover's own among them. It is a definition and not a program: it takes the model's trace by a non-constructive choice.
- One request per proof; one commitment; exact match; the prover keeps no state, nothing counts the replies, and all its coins are fresh and uniform.
- A request counts as served only if the model gives a value at every position of the zero-filled window, the padding after the output included; so a true output can be refused (in the corollary with the label: told "failed") on account of the padding (for weights that pass a worst-case check a theorem rules it out; for others none does, and no example is proved).
- In point 3 nothing stands beside a proof: it is about the system that `compile` yields, with no wrapper round it. In that corollary the label beside a proof is a function in the statement, and nothing in `compile` emits it.
- Where the model has no result on a request, or another result than the claimed output, the completeness line says nothing.
- That a request is refused is unchecked, as the label is: an empty proof proves nothing, and a prover can return it at a request that it could serve. The compiled verifier rejects it, under every hash function and at all public files (`rejectsNoProof_value`). In that corollary the label is unchecked too: a service that chooses to say "failed" does not prove it and can say it falsely, and the same holds of "other tokens": no proof goes with either, and the verifier checks nothing there.
- The library also has statements on completeness written for any description of the protocol, which they take as a parameter, among them `G3'pol`. It is proved of no description, and the final statement does not depend on it (by the compiled library's record of the constants that each statement and proof uses).
- Of soundness and binding this list says nothing. Their limits: lean/THEOREM.md, "Look first at four things" and "What it does not say"; point 4 above; [STATEMENTS.html](STATEMENTS.html).

## 2. What an auditor must read

These are the definitions that the final statement's six fields unfold to directly, in reading order; those beneath them follow, by file. Appendix D need not be read to audit the final statement.

**Soundness.** 
`VerifiableInference/Statements.lean:84`

```lean
def Sound (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      ∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries)
```

**Soundness with binding.** 
`VerifiableInference/Statements.lean:109`

```lean
def SoundAndBinding (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → Option system.Weights,
    ∀ (committerQueries proverQueries : ℕ) (State : Type)
      (committer : RandomizedAlgorithm (Commitment × State)),
      committer.QueryBound committerQueries →
      (∀ prover : State → RandomizedAlgorithm (List Token × List Token × system.Proof),
        (∀ state, (prover state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (prompt, output, proof) ← prover state
            let accepted ← (system.verify commitment prompt output proof).toRandomized
            pure (extractor commitment queryLog, prompt, output, accepted))
          {(extracted, prompt, output, accepted) |
            accepted = true ∧
            ¬ ∃ weights, extracted = some weights ∧ system.IsModelOutput weights prompt output}
          ≤ ε (committerQueries + proverQueries)) ∧
      (∀ opener : State → RandomizedAlgorithm (system.Weights × system.CommitmentRandomness),
        (∀ state, (opener state).QueryBound proverQueries) →
        Prob (do
            let ((commitment, state), queryLog) ← committer.withQueryLog
            let (weights, randomness) ← opener state
            let recomputed ← (system.commit weights randomness).toRandomized
            pure (extractor commitment queryLog, commitment, weights, recomputed))
          {(extracted, commitment, weights, recomputed) |
            recomputed = commitment ∧ extracted ≠ some weights}
          ≤ ε (committerQueries + proverQueries))
```

**Completeness at a hypothesis.** 
`VerifiableInference/AtEveryRequest.lean:47`

```lean
def ProofAcceptedWhere (system : ArgumentSystem) (hypothesis : Request → Prop)
    (result : system.Weights → Request → Option (List Token)) (error : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (request : Request), hypothesis request →
    result weights request = some request.2 →
    Prob (do
        let randomness ← system.sampleCommitmentRandomness
        let commitment ← (system.commit weights randomness).toRandomized
        let proof ← system.prove weights randomness request.1 request.2
        (system.verify commitment request.1 request.2 proof).toRandomized)
      {accepted | accepted = false}
      ≤ error
```

**Zero knowledge, the simulator told one value for each request, with one bound on the error.** 
`VerifiableInference/AtEveryRequest.lean:146`

```lean
def ZeroKnowledgeBelowWhere {Told : Type} (system : ArgumentSystem) (hypothesis : Request → Prop)
    (told : system.Weights → Request → Told) (queries proofs : ℕ) (bar : ℝ≥0∞) : Prop :=
  ∃ error : ℕ → ℕ → ℝ≥0∞,
    (∀ asked replies, asked ≤ queries → replies ≤ proofs → error asked replies ≤ bar) ∧
      ZeroKnowledgeWhere system hypothesis told error
```

**Zero knowledge with the label shown.** 
`VerifiableInference/Labelled.lean:74`

```lean
def ZeroKnowledgeShownBelowWhere {Told : Type} (system : ArgumentSystem)
    (hypothesis : Request → Prop) (told : system.Weights → Request → Told) (queries proofs : ℕ)
    (bar : ℝ≥0∞) : Prop :=
  ZeroKnowledgeBelowWhere (labelled system told) hypothesis told queries proofs bar
```

**Zero knowledge told, the experiment.** 
`VerifiableInference/AtEveryRequest.lean:128`

```lean
def ZeroKnowledgeWhere {Told : Type} (system : ArgumentSystem) (hypothesis : Request → Prop)
    (told : system.Weights → Request → Told) (error : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∃ simulator : Simulator system.PublicParameters Told system.Proof,
    ∀ (weights : system.Weights) (chooser : View system.Proof → Option Request),
      (∀ view request, chooser view = some request → hypothesis request) →
      ∀ (queries : ℕ) (verifier : Commitment → MaliciousVerifier system.Proof) (proofCount : ℕ),
      (∀ commitment, (verifier commitment).QueryBound queries) →
        statisticalDistance
            (Prob (realExperiment system verifier chooser weights proofCount))
            (eventProbability (simulatedExperiment system simulator told verifier chooser weights
                proofCount))
          ≤ error queries proofCount
        ∧ eventProbability (simulatedExperiment system simulator told verifier chooser weights
            proofCount)
            {view | ¬ view.queryLog.Consistent} = 0
```

**The malicious verifier.** 
`VerifiableInference/Statements.lean:192`

```lean
inductive MaliciousVerifier (Proof : Type) : Type
  | stop : MaliciousVerifier Proof
  | query (input : BitString) (next : Digest → MaliciousVerifier Proof) : MaliciousVerifier Proof
  | sample (bound : ℕ) (next : Fin (bound + 1) → MaliciousVerifier Proof) : MaliciousVerifier Proof
  | requestProof (next : List Token × List Token → Proof → MaliciousVerifier Proof) :
      MaliciousVerifier Proof
```

**The simulator.** 
`VerifiableInference/AtEveryRequest.lean:76`

```lean
structure Simulator (PublicParameters Told Proof : Type) where
  State : Type
  start : PublicParameters → ℕ → PMF (Commitment × State)
  answerQuery : State → BitString → PMF (Digest × State)
  simulateProof : State → Request → Told → PMF (Proof × State)
```

**The simulated experiment with that simulator.** 
`VerifiableInference/AtEveryRequest.lean:109`

```lean
def simulatedExperiment {Told : Type} (system : ArgumentSystem)
    (simulator : Simulator system.PublicParameters Told system.Proof)
    (told : system.Weights → Request → Told)
    (verifier : Commitment → MaliciousVerifier system.Proof)
    (chooser : View system.Proof → Option Request)
    (weights : system.Weights) (proofCount : ℕ) : PMF (View system.Proof) :=
  (simulator.start (system.publicParameters weights) proofCount).bind fun started =>
    simulatedSteps simulator (told weights) chooser (verifier started.1) proofCount
      ⟨started.1, [], [], []⟩ started.2
```

**A well-formed request.** 
`VerifiableInference/WellFormedRequests.lean:28`

```lean
def WellFormedRequest (settings : IntegerTransformer.Settings) (request : Request) : Prop :=
  RequestForm settings request.1 request.2
```

**The bit.** 
`VerifiableInference/AtEveryRequest.lean:36`

```lean
inductive Outcome : Type where
  | served : Outcome
  | refused : Outcome
  deriving DecidableEq
```

`VerifiableInference/RequestOutcome.lean:40`

```lean
def requestOutcome (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Outcome :=
  if RequestForm settings request.1 request.2 ∧
      requestResult settings weights request.1 request.2 = some request.2 then .served
  else .refused
```

**No proof at a refused request.** 
`VerifiableInference/AtEveryRequestGuards.lean:62`

```lean
def HandsOutNoProof (system : ArgumentSystem) (unserved : system.Weights → Request → Prop)
    (isNoProof : system.Proof → Prop) : Prop :=
  ∀ (weights : system.Weights) (randomness : system.CommitmentRandomness) (request : Request)
    (hash : Hash) (form : system.Proof),
    unserved weights request →
      (system.prove weights randomness request.1 request.2).run hash form ≠ 0 → isNoProof form
```

**The label.** 
`VerifiableInference/RequestLabel.lean:39`

```lean
def requestLabel (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Label :=
  if RequestForm settings request.1 request.2 then
    match requestResult settings weights request.1 request.2 with
    | none => .failed
    | some tokens => if tokens = request.2 then .served else .otherTokens
  else .otherTokens
```

**The model's result.** 
`VerifiableInference/WellFormedRequests.lean:32`

```lean
def modelResult (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Option (List Token) :=
  requestResult settings weights request.1 request.2
```

**The files in use.** 
`Johnson/Face/FinalStatement.lean:246`

```lean
structure FilesInUse (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) : Prop extends
    FilesTaken files parameters where
  pass : protocolDataWellFormed (asDescriptionFiles files) = true
```

**The compiler.** 
`Johnson/Face/Compiler.lean:382`

```lean
def compile : ArgumentSystem :=
  systemOf input.publicSide.model.nextToken (compiledSide input)
    (compiledVerifier input.publicSide input.format.parse)
```

**What the compiler takes.** 
`Johnson/Face/Compiler.lean:289`

```lean
structure Compilable where
  /-- The protocol, its layouts, the readings, the model. -/
  publicSide : PublicSide
  /-- The layouts as the committer and the prover read them. -/
  wiring : CompilerWiring publicSide
  /-- The honest provers. -/
  provers : HonestProvers publicSide.protocol
  /-- What the honest side chooses beside its provers, at each value of the public reading. -/
  settings : (reading : wiring.family.D) → CompiledSettings (wiring.layoutAtReading reading) provers
  /-- The test on an answer's first hash block by which a search for a nonce decides whether to ask
  the other blocks: a failed try costs one call. -/
  firstBlockTest : (reading : wiring.family.D) → Rom.More (typedOracleFamily 256
    (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.queryLayout.K
    (typedOracleCarrier (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.protocol
      (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.LeafBody
      (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.offlineRoundSplits
      (publicSide.layoutAt wiring.baseDigest wiring.baseFurther).input.linkRoundSplits)) 256
  /-- The honest committer samples one number from 0 to this. -/
  coinBound : ℕ
  /-- The proof format. -/
  format : ProofFormat publicSide.protocol publicSide.offlineRoundSplits publicSide.linkRoundSplits
```

**flashProveAtFiles.** 
`Johnson/Face/FinalStatement.lean:151`

```lean
def flashProveAtFiles (files : PublicFiles) (settings : Settings) (honest : HonestProversAndSettingsAtFiles files settings) :
    Compilable where
  publicSide := flashProvePublic files settings
  wiring := flashProveWiring files settings honest.fallbackInstance
  provers := honest.provers
  settings := honest.compiledSettings
  firstBlockTest := flashFirstBlockTest files
  coinBound := honest.coinBound
  format := formatOf flashProveDescription files flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files)
```

**The one protocol structure.** 
`Hiop/RecInterface.lean:111`

```lean
structure HolographicProtocol (I X : Type) where
  wordLength    : ℕ
  Symbol   : Type
  EncodingRandomness   : Type
  [encodingRandomnessIsFinite : Fintype EncodingRandomness]
  [encodingRandomnessIsNonempty  : Nonempty EncodingRandomness]
  encodeIndex  : I → EncodingRandomness → (Fin wordLength → Symbol)
  /-- the record phase (an out-of-domain sample): the verifier's seed -/
  OutOfDomainSeed : Type
  [outOfDomainSeedIsFinite : Fintype OutOfDomainSeed]
  [outOfDomainSeedIsNonempty  : Nonempty OutOfDomainSeed]
  /-- the prover's answer -/
  OutOfDomainAnswer  : Type
  /-- the honest answer -/
  honestOutOfDomainAnswer  : I → EncodingRandomness → OutOfDomainSeed → OutOfDomainAnswer
  /-- the word has a collision at the seed -/
  hasCollisionAt : (Fin wordLength → Symbol) → OutOfDomainSeed → Prop
  /-- the index decoder reads the word and its record -/
  decodeIndex  : (Fin wordLength → Symbol) → OutOfDomainSeed × OutOfDomainAnswer → Option I
  offline : InteractiveOracleProof (OutOfDomainSeed × OutOfDomainAnswer) (oneExternalString wordLength Symbol)
  link : InteractiveOracleProof ((OutOfDomainSeed × OutOfDomainAnswer) × (OutOfDomainSeed × OutOfDomainAnswer)) (twoExternalStrings wordLength Symbol)
  /-- the number of slots -/
  maxBatchSize    : ℕ
  onlineBatch  : BatchInteractiveOracleProof (X × (OutOfDomainSeed × OutOfDomainAnswer)) (oneExternalString wordLength Symbol)
  honestOfflineProver   : Honest offline (I × EncodingRandomness × OutOfDomainSeed)
  honestLinkProver   : Honest link (I × (EncodingRandomness × OutOfDomainSeed) × (EncodingRandomness × OutOfDomainSeed))
  honestOnlineBatchProver   : BatchHonestProver onlineBatch (I × EncodingRandomness × OutOfDomainSeed)
  early : X → X
  late  : Option ℕ
```

**Beneath them, by file.**

- The honest provers and settings: `AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean` (honestProversAndSettingsOf, compiledPartAtHonestProvers)
- `Johnson/Face/HonestProversWithCompiledPart.lean` (honestProversAndSettingsAtFiles, theProvers)
- The honest provers: `E2E/TheHonestProver.lean` (honestProvers)
- `E2E/KeyArgumentsAt.lean` (thePartsAt)
- `E2E/KeyFifteen.lean`
- `E2E/KeyPartsIdle.lean`
- `E2E/KeyLookups.lean`
- `E2E/KeyFirstSends.lean`
- `E2E/KeyBookAtWritten.lean`
- `E2E/KeyProver.lean`
- The files: `Johnson/Face/FinalStatement.lean` (FilesTaken, TableBudgetFits, isNoProof)
- `Ladder.lean` (InScope, readFiles, queryBudget, verify, the description)
- Argument systems and the model of hashes: `VerifiableInference/Statements.lean` (ArgumentSystem)
- `VerifiableInference/RandomOracleModel.lean` (RandomizedAlgorithm, Prob)
- The compiled side: `Johnson/Face/Compiler.lean` (systemOf, compiledSide)
- The reply and the label: `VerifiableInference/Labelled.lean` (labelled, reply)
- `VerifiableInference/RequestLabel.lean` (Label)
- `VerifiableInference/RequestResult.lean` (RequestForm)
- `VerifiableInference/AtEveryRequest.lean` (WithinBudget)
- The numbers: `Ladder/Bits.lean` (soundnessErrorInQueries, bindingErrorInQueries)
- `Ladder/PackageBits.lean` (levelError)

## 3. The numbers

- `finalSoundnessError q` = 16 (q + 1 + 2^23) / 2^128 + (q + 2^23 + 3)^2 / 2^256, about q / 2^124 + 2^-101. q counts the hash queries of the committer and the prover together.
- `finalBindingError q` = max (soundnessErrorInQueries q 2^23) (bindingErrorInQueries q), about q / 2^124 + 2^-100.
- `finalCompletenessError` = 2^-40.
- At the interactive level the completeness error is at most 2^-41.
- `finalZeroKnowledgeError` = 2^-154, the least power of two that fits.
- 2^-174 bounds the chance, before hashing, for a served request, over the verifier's messages that pass the proof-of-work tests, that the online prover stops for a reason that depends on its secrets (it is counted once for each reply); for the offline and the link prover that chance is 0.
- The numbers on zero knowledge are statistical distances, not a security level.
- The zero-knowledge error, with one request to a run, is below 2^-154 over these 688,127 replies, and, by a lemma on the stated term (`life_number_at_most`, `AtFullSide/CompletenessAndZeroKnowledge/LifeNumberAt135.lean`), below 2^-135 over the interactive statement's whole budget of up to 710,324 copies with up to 688,127 runs of the online IOP each.
- In point 3, 2^64 bounds the verifier's hash queries, and 688127 the replies under one commitment: a reply at a refused request, which is the empty proof, counts too.
- The hash function is not an argument of `compile`: the lines on soundness, binding, completeness and zero knowledge draw it at random, so they are statements in the random-oracle model. A second, fixed hash function, made of BLAKE2b's compression function with another counter, stands inside the protocol's description in all of them: that one is not a random oracle.

## 4. The axioms

For each of these theorems Lean prints no axiom beyond these three: propext, Classical.choice, Quot.sound. Lean's kernel is trusted, not proved; the pinned version, 4.29.1, is older than fixes of publicly known soundness bugs in it: `lean/LIMITS.md`, L45.

An independent proof checker has replayed the proof of the soundness theorem on `verify` (`sound_of_verify_at`), on which `finalSound` rests, over a build of this repository's files (that the compiled files that it and the passes told below read were that build's is known from a report alone; Lean's own files were not compared with a list of checksums), with every declaration beneath it, and accepted it; that was a pass on that theorem's export alone: it accepted nothing that does not lie beneath that theorem, and `finalSound` does not. Of the six, the independent checker has accepted `sound`, `repliesFit` and `refusedHandsOutNoProof` by name, over a build of this repository's files; over such a build the three on binding, completeness and zero knowledge have been checked by Lean's kernel alone. The library's full check sends the modules of the side library `AtFullSide/` and of `ShapeLines/` through the kernel's second pass by another call than the rest, each at the stack at which Lake compiles it (`lean/CHECKING.md`). A whole run of it over this repository's Lean files passed at every step; its last line says that no theorem got a verdict on binders or on `Classical.choice` (the whole line, and what the check doesn't cover: `lean/CHECK-RESULTS.md`).

## Appendix A. The protocol

The protocol's description is `VerifierAndGoals.theDescription` and what it is assembled from: `Ladder.lean` and `Johnson/` in the library. The protocol's type is in `Hiop/RecInterface.lean`. Not shown here: only where it lies.

## Appendix B. BLAKE2b

`Run/Blake2b/Compress.lean`, `Run/Blake2b/Hash.lean`, `Run/Blake2b/SaltedPlain.lean`, `Fmt/Blake2b.lean` and `Fmt/Rules23.lean` in the library. Not shown here: only where it lies.

## Appendix C. The integer model

`IntegerModel/` and `VerifiableInference/ModelWeights.lean` in the library. Not shown here: only where it lies.

## Appendix D. The statements at the level of the interactive oracle proof

Before any hashing: about one protocol; completeness and zero knowledge about one triple of provers in it.

The structure below is a definition. What is proved at this level is `ThreeAtFiles`, further down, which is not this structure.

`Johnson/Face/OneProtocol.lean:35`

```lean
structure TheThreeIOPStatements (files : PublicFiles) {parameters : Inst.Model.ScalesAndPolicy}
    (read : readFiles files = .ok parameters) (parts : Parts files)
    (offlineStops linkStops onlineStops : ℝ≥0∞) : Prop where
  sound : SoundAsIOPAtFiles files (filesAt files).fixedMessageProvers
  complete : CompleteOnServedRequests files read (proversAtFiles files read (plainProvers files parts))
  zeroKnowledge : ZeroKnowledgeOnServedRequests files read (plainProvers files parts)
    offlineStops linkStops onlineStops
  servedIsTrue : ∀ index instance_, ServedRequest committerCoinCountLessOne files read index instance_ →
    relationAtFiles files index instance_
```

Soundness at this level, round by round, with a named extractor of the weights. The theorem is `soundAsIOPAtTheProtocol`, in `E2E/SoundAsIOPAtFilesProofs.lean`. Mark: **proved in Lean**.

`E2E/SoundAsIOPAtFiles.lean:148`

```lean
def soundAsIOPAtTheProtocol : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    protocolDataWellFormed (asDescriptionFiles Z) = true →
    (protocolAtFiles Z).IndexKnowledgeSoundIOP (relationAtFiles Z) (filesAt Z).annT (offlinePlaces Z) (filesAt Z).annL 1
      ((2 : ℝ≥0∞)⁻¹ ^ 128)
```

As a probability: at most 67,391 × 2^-96, below 2^-79. This is before hashing, and not the compiled figure: it is what round-by-round counting yields when proof of work is treated as challenge bits instead of being charged to the adversary's hash queries; after compiling, the figure is finalSoundnessError's. Mark: **proved in Lean**.

`E2E/SoundAsIOPNumbers.lean:220`

```lean
theorem probabilityInScope (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (P : (filesAt Z).Provers)
    (fill : ((filesAt Z).withProvers P).Fill) (β : Type)
    (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β) :
    pr (unif (Rho (((filesAt Z).withProvers P).wholeRunShape fill))) (ConclusionFails Z P fill prover) ≤
      (67391 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96
```

*Beside the compiled soundness line.* The compiled soundness line (`finalSound`), and the soundness theorem on `verify` on which it rests (`sound_of_verify_at`), do not rest on soundness at this level: by import lines the file of its proofs lies beneath neither. The proof of the soundness theorem on `verify` takes the round-by-round soundness of the key, copy and proof protocols one by one (`keySound`, `entrySound`, `proofSound`, three of the compiler's named hypotheses; where each is proved at `theDescription`: LIMITS.md, L57) and hands them to the compiler's theorem on `innerCompiledVerifier`, in the form `verifierAcceptingNoMoreThanBehindReadingAndParser_soundFor` (`Johnson/Top/InnerCompiledVerifierByPublicReading.lean:640`). A second theorem (`sound_of_verify_at_through_the_IOP`, `E2E/SoundAsIOPAtFilesProofs.lean:144`) has the statement of the soundness theorem on `verify` to the letter, with no further hypothesis, and is proved through soundness at this level, not through that theorem: it draws the three from soundness at this level and hands them to the same theorem of the compiler. It adds little assurance: the three parts of soundness at this level are themselves proved from one lemma of the first proof and from sisters of the other two, which rest on the same theorems: it is the same proof by another road, no second derivation. Mark of the second theorem: **proved in Lean**. The fields of `FinalStatementOneBit` on completeness and zero knowledge are both proved through one theorem (`beneath_at_T1`, `AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean:164`), and the lines `completeOnCanServe` and `zeroKnowledgeOnCanServe` through another (`served_at_T1`, the same file, :200); both take one premise: the two statements below, at the protocol's honest provers, and an inequality on numbers, which at `honestProversAndSettings` and 2^-154 is proved, at all public files in use (`termLeft_value`, `AtFullSide/CompletenessAndZeroKnowledge/OneBitAtHonestProversAndSettings.lean:91`).

Completeness at this level, at the protocol's honest provers on served requests, with error at most 2^-41, over the prover's coins and the challenges that pass the proof of work; and honest-verifier zero knowledge. These definitions are this library's own, and no published definition word for word: an auditor should read them first. In ordinary words, with their limits: LIMITS.md, L90, L91, L92. Two of these limits: at this level one bit for each request is not hidden (whether it is served, which depends on the weights); and a statement of this form is met by a prover that shows nothing, so it counts only beside completeness of the same provers.

`E2E/CompleteAsIOPAtFiles.lean:86`

```lean
def CompleteOnServedRequests (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (Hs : HonestProvers (protocolAtFiles Z)) : Prop :=
  CompleteIOP (protocolAtFiles Z) Hs (workAtFiles Z) (copyNumberAtFiles Z) (ServedRequest committerCoinCountLessOne Z hr)
    completenessTarget
```

`VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean:82`

```lean
structure ZeroKnowledgeOnServedRequests (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (Hs : HonestProvers (protocolAtFiles Z))
    (offlineStops linkStops onlineStops : ℝ≥0∞) : Prop where
  /-- the online part is not idle -/
  someRequestIsServed : ∃ i x, rangeAtFiles i ∧ ServedRequest committerCoinCountLessOne Z hr i x
  /-- and the index is not told by that alone -/
  twoIndicesServeOneRequest : TwoIndicesServeOneRequest Z hr
  simulated : ∃ simulators : RunSimulators (protocolAtFiles Z),
    HonestVerifierZeroKnowledge (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles
        (ServedRequest committerCoinCountLessOne Z hr) (budgetAtFiles offlineStops linkStops onlineStops) ∧
      ∀ (copyNumber : ℕ → ℕ) (copies sessionsPerCopy : ℕ), copies ≤ 710324 → sessionsPerCopy ≤ 688127 →
        WholeLife (workAtFiles Z) (proversAtFiles Z hr Hs) simulators rangeAtFiles (ServedRequest committerCoinCountLessOne Z hr)
          (budgetAtFiles offlineStops linkStops onlineStops) copyNumber copies sessionsPerCopy
```

`VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean:174`

```lean
structure HonestVerifierZeroKnowledge (work : PartsWork L) (provers : HonestProvers L)
    (simulators : RunSimulators L) (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) : Prop where
  /-- the range is no single index -/
  twoIndices : ∃ i i', i ≠ i' ∧ inRange i ∧ inRange i'
  /-- the work bits are the protocols' own: the verifiers ask the work, and the maps clear no more than is tested -/
  faithful : work.Faithful
  runByRun : RunByRun work provers simulators inRange Served N
  wholeView : WholeView work provers simulators inRange Served N
```

Their two theorems at the files. Marks: **proved in Lean**, **proved in Lean**. The two name the provers by two terms, and the two terms are the same by unfolding one definition (`termLetters`).

`AtFullSide/E2E/CompleteAtEveryFilesInUse.lean:89`

```lean
theorem completeOnServedRequests_at_every_files_in_use :
    ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers files)
```

`AtFullSide/E2E/ZeroKnowledgeFromTheRows.lean:176`

```lean
theorem zkOnServedRequests_inScope (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) :
    ZeroKnowledgeOnServedRequests files hr
      (HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files))) 0 0
      (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)))
```

The theorem that binds them, about one protocol, with completeness and zero knowledge about one triple of provers in it, at every set of files in use. Mark: **proved in Lean**.

`AtFullSide/Face/TheThreeAtTheFiles.lean:25`

```lean
theorem threeAtFiles_in_use (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ThreeAtFiles files inUse.read (HonestProvers.ofThreeProvers (honestProvers files (thePartsAt files)))
      0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)))
```

`E2E/ThreeAtOneProtocol.lean:132`

```lean
abbrev ThreeAtFiles (Hs : HonestProvers (protocolAtFiles Z)) (offlineStops linkStops onlineStops : ℝ≥0∞) : Prop :=
  ThreeAtOneProtocol (protocolAtFiles Z) (proversAtFiles Z hr Hs) (workAtFiles Z) (copyNumberAtFiles Z)
    (ServedRequest committerCoinCountLessOne Z hr) (relationAtFiles Z) rangeAtFiles (filesAt Z).annT (offlinePlaces Z)
    (filesAt Z).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128) completenessTarget
    (budgetAtFiles offlineStops linkStops onlineStops)
```

`E2E/ThreeAtOneProtocol.lean:113`

```lean
structure ThreeAtOneProtocol {Index Request : Type} (L : HolographicProtocol Index Request) (provers : HonestProvers L)
    (work : PartsWork L) (copyNumberIn : ℕ → Plains L.onlineBatch.loc.shape → Bool)
    (served wide : Index → Request → Prop) (inRange : Index → Prop)
    (offlineMarks : RoundSplits L.offline.shape) (offlinePlaces : ℕ) (linkMarks : RoundSplits L.link.shape)
    (linkPlaces : ℕ) (roundBound completenessError : ℝ≥0∞) (budget : Budget) : Prop where
  /-- round-by-round knowledge soundness for the index, of L's three verifiers -/
  sound : L.IndexKnowledgeSoundIOP wide offlineMarks offlinePlaces linkMarks linkPlaces roundBound
  /-- completeness of these provers, against L's three verifiers -/
  complete : CompleteIOP L provers work copyNumberIn served completenessError
  /-- honest-verifier zero knowledge of these provers, in runs with L's three verifiers -/
  zeroKnowledge : ∃ simulators : RunSimulators L,
    HonestVerifierZeroKnowledge work provers simulators inRange served budget
  /-- what is served lies in the relation of soundness -/
  servedIsTrue : ∀ index request, served index request → wide index request
```

The field's comment says «knowledge soundness»: no equivalence with a printed definition of round-by-round knowledge soundness is claimed.

`ThreeAtFiles` is not the structure `TheThreeIOPStatements` printed above. No theorem names both. `threeAtOne_of_statements` and `statements_of_threeAtOne`, in the same file, lead between `ThreeAtFiles` and the three statements that are the first three fields of `TheThreeIOPStatements`, for files in scope; the way back asks one more fact.

What the structure does not give:

- Soundness reads neither `provers` nor `work`.
- The numbers stand over different distributions and are not to be compared: `roundBound` (at the files 2^-128) is a share of all of one round's challenges, the bits of proof of work among them; `completenessError` is over the provers' coins and the challenges that pass the proof-of-work tests.
- Soundness is here in its form in parts: online it speaks of a batch, where the other two speak of one request.
