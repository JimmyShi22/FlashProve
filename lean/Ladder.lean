-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder.lean: the goals at the top of this library, each written as the definition of a proposition.
Definitions only: no proof is in this file. The numbers in the goals' names are labels and have
gaps; the prime in `G3'pol` is part of the label.

Why this file exists. The goals must not change with the description of the protocol.
So everything that may change is gathered in one parameter `D`, and the goals are stated in terms
that `D` cannot reach: the verifier and the argument system are built here from `D`, and the
weights, the model, what is asked of an output, the test on the public files and all numbers are
terms of this file or of the library. In the goals `D` takes a function in the place of the format's
second hash function and returns a `Description`; in section 3 and in `SoundAt`,
`SoundUnderPolicyAt` and `BindsAt` `D` is a `Description`. The goals have no hypothesis apart from
their scope, so a theorem that needs one must show it in its own statement. One kind of hypothesis
is foreseen, for `G3'pol` alone: that a closed term of type Bool is true which names only
the two named sets of files, constants of the library, and the fields `C`, `F` and `P` of `D`, which
do not depend on the hash function. That is the kind that Ladder/Guards.lean evaluates by `#guard`;
the fields of `FilesRead` are of it. No decision by compiled code is admitted as a proof, and no
axiom beyond Lean's three. A goal shown under such a hypothesis is shown up to an evaluation, and
that has to be said with it. (A case split inside `D` can do a hypothesis's work: see 9.)

Words.
  hash function   The format's hash function. The goals draw it at random (`Sound`,
                  VerifiableInference/Statements.lean). "The real hash function" is the one that the
                  programs compute.
  second hash     The format's second hash function:
                  OnBytes/Hash/SecondHashFunction.lean.
  format          docs/format/FORMAT.md.
  public files    Three files that the user holds with the commitment: the parameter file (`Z.pol`;
                  policy.txt), the layout file (`Z.lay`; layout.txt) and the scale file (`Z.KL`;
                  KL.bin).
  reader          `readFiles`: it reads a table of scales and the policy off the public files.
  policy          The acceptance policy: three numbers C, theta, cap in the parameter file
                  (`pp.pol`; see `MeetsPolicy`, Policy/Front/MeetsPolicy.lean). Exact match is (256,
                  256, 0): every output token is the model's next token.
  in scope        `InScope`: the stored full-size example's public files, with any scale file, and
                  in the parameter file any values of eight free numbers, that the reader accepts,
                  if 2^8 ≤ theta.
  request         A prompt with output tokens. It can be served if `CanServe` holds
                  (VerifiableInference/CanServe.lean).
  compiler        It makes the verifier `innerCompiledVerifier` from a protocol: Johnson/Top/InnerCompiledVerifier.lean.
  typed proof     What `innerCompiledVerifier` takes from the prover's side. A parser makes one from a form; a
                  form is whatever the prover hands over.
  honest side     `D`'s own committer and prover: `sample`, `commit`, `prove`.
  extractor       From the commitment and the committer's queries it gives the weights of which a
                  goal on soundness or binding speaks.
  gate            A branch of `D` that accepts every request.
Further terms: lean/GLOSSARY.md.

The goals about `D`.
  G3'pol     The honest side is accepted for every output that can be served and meets the policy,
             within its budget of queries, at the stored example's two sets of public files alone.
  G7         Soundness at exact match, with an error of at most `ceiling` (one quarter).
  G7'        `G7`, with the same ceiling, whatever function stands in the second hash function's
             place. There is no such form of `G8` or `G9`.
  G8         Soundness under the policy, with the same ceiling.
  G9         The commitment binds to the weights that the extractor gives, with the same ceiling,
             and the honest committer stays within the honest side's budget at all files in scope.
The ceiling is a bar on the error, no security level. In all goals but `G7'` and `G7'bits` the
second hash function is the format's own, a fixed function.
The same four with a security level, `G7bits`, `G7'bits`, `G8bits` and `G9bits`, are stated in
Ladder/Bits.lean. No goal of this file has a security level: a `D` whose verifier ignores the user's
request at an eighth of all hash functions can meet every goal here (5).
Not about `D`.
  FilesRead  The two named sets of public files are in scope and are read as expected.
  FixedFacts Weights and outputs exist without which the goals would say less.

What each goal is worth alone. Read this before citing one of them.
1. `G3'pol` alone is met by a verifier that accepts every request.
2. All goals on soundness and binding together, those of Ladder/Bits.lean too, are met by a verifier
   that always refuses with a commitment that binds. `G7` alone is also met by a verifier that
   accepts only the empty output, or has a single set of weights written into it. `G3'pol` rules
   these out, given `FilesRead` and `FixedFacts`: it speaks of all weights, a request that can be
   served has a non-empty output, and the honest side is accepted except with probability `completenessErrorBound`
   (2^-40).
3. `G3'pol` speaks at two named sets of public files only, and both have the stored example's scale
   file and normalisations. So a `D` may refuse all files in scope but these two sets, and with them
   every other model, and still meet every goal of this file: no goal here asks that the honest side
   is accepted at other files. At all files in scope but the two named sets `G7` and `G8` are met by
   a `D` that always refuses, and `G9` asks only that `commit` binds and stays within its budget. In
   scope apart from the two named sets are other scale files and other values of the eight free
   numbers of the parameter file (`FreeLines`, Ladder/Stored.lean), nothing else. A parameter file
   that differs in any other line, or a layout file that differs at all, is out of scope of every
   goal, and `verify` refuses it. Among the fixed lines are theta0, cs, S and rx, which the model of
   these goals has built into its tables (`lookupTables`), and the four tables' digests, wb_emb and
   s, which the model does not read. `InScope` refuses other values of all of them. That the model's
   tables are the tables with these four digests is not shown. The weights of these goals may have
   embedding entries of four signed bytes, whatever wb_emb states (`weightsInRange`,
   VerifiableInference/ModelWeights.lean). So a model whose fit changes one of the fixed lines
   cannot be verified by this verifier at all. Since the fixed bytes are fixed, a `D` need not read
   them: a `D` that reads nothing of the layout file, and of the parameter file the free numbers
   alone, can meet every goal.
4. `G3'pol` bounds the honest side's queries by 2^48, against 2^64 for the adversary. Without that
   bound a protocol that checks nothing but one very hard proof of work would meet every goal here.
5. `G7` with `G3'pol` is still met by a `D` with a gate that is open when three fixed bits of the
   public files' digest are zero (error 1/8), and that is a true system otherwise, complete under
   the policy. No constant ceiling rules that out; `G7bits` (Ladder/Bits.lean) does. Likewise `G8`
   and `G9`. They are also met by a `D` with a gate that can be opened by search: it accepts every
   request whose form holds a string at which 68 fixed bits of the hash function's answer are zero.
   Within the budgets (2^64 queries of the adversary and as many of a parser) that adds about 1/8 to
   the error; but this gate is open at every hash function, the real one too, to whoever spends
   about 2^68 queries.
6. The part of `G8` that speaks of policies with 257 ≤ theta and 257 ≤ C is met by an extractor that
   always returns the all-zero weights and a verifier that only tests the form of a request
   (`meetsPolicy_zeroWeights`, Policy/Front/TrueUnder.lean). `G9` at the same extractor rules out
   that extractor: since `commit` stays within the honest side's budget, "commit honestly to other
   weights and open them" is an adversary within the budget. (With a `commit` of more queries than
   the adversary's budget no adversary could compute a commitment, and binding would hold whatever
   the extractor gave.) `G9` says nothing of a commitment that the honest committer did not make:
   the extractor may give any weights there, the all-zero weights too, and a yes under such a
   commitment says no more than one under a commitment to them. In general a yes says that the
   output meets the policy at the weights under the commitment that the verifier was given. It does
   not say that `commit` made that commitment, nor whose it is. A `D` that enforces exact match,
   whatever policy the files state, meets `G8` and `G9`; `G3'pol` rules that out. So `G8`
   means something only together with `G9` and `G3'pol`. Even then it is as weak as the docstring of
   `MeetsPolicy` says: a committer may itself commit to such weights, and against that committer
   `G8` says nothing at these policies. Public files can do the like without the weights: some valid
   settings make every layer add nothing (by hand, no theorem: see the docstring of
   `weightsAreValid`, VerifiableInference/ModelWeights.lean); where files in scope state such
   settings, `G7` and `G8` say little.
7. "Send the weights" (the commitment is their hash, the proof is the weights) would meet every goal
   of this file and of Ladder/Bits.lean, if it is written for the compiler. It is a true argument
   system. These goals do not say that `D` is the protocol that the programs run, that what the
   parser reads is the prover's files, that the verifier can be run, or that a proof hides anything.
8. These goals fix their own text and no more. Every definition beneath them could change without a
   character of this file changing. A comparison of this file with a stored copy must also compare
   every constant that the goals reach; only a value of `D` is free.
9. No proposition can say how `D` is made. A `D` that ignores its argument and calls a hash function
   by name can meet `G7'` and `G7'bits`. So can a family made by a case split: `D` at the functions
   where `D` is sound, a verifier that always refuses at the others. A `D` taken by choice from a
   proof that some `D` meets the goals meets them and has no field that can be read. So a check of a
   `D` has to read its definitions. `D` may apply its argument and compare what it returns with
   bytes of the public files; it may not decide which function it was given, nor reach a hash
   function by name. The fields that run (`C`, `F`, `P`, `readMore`, `T`, `parse`, `sample`,
   `commit`, `prove`) may not use choice; the extractor may.
10. The goals speak of a hash function drawn at random, so a `D` that behaves otherwise at one
    particular value loses nothing: that value has probability 2^-256. At the real hash function it
    can be chosen to occur. Example: a gate that is open where the public files' digest equals the
    real hash function's digest of them, as a constant or by a call by name. Such a `D` meets every
    goal here and in Ladder/Bits.lean. Runs at the real hash function on a stored proof with the
    output, the prompt or the commitment altered see this gate, but not one that is keyed to one
    commitment or one prompt. A list of the hash functions and constants that `D`'s definitions
    reach shows what is written out, not what is computed. The rest is a matter of reading `D`.
11. Whether the protocol checks enough is tested only coarsely by the goals of this file: up to the
    budgets a challenge that can be ground has to have an error of about 2^-67 or less for each try,
    and no more is asked. The goals of Ladder/Bits.lean test it at their level, at a drawn hash
    function and fixed files. Running the verifier on good proofs cannot show it.
12. The public files are fixed before the hash function is drawn. A provider that picks or grinds
    its files with the hash function in hand, as every provider can, is covered by no goal here or
    in Ladder/Bits.lean: a goal in which the provider names the files would be another goal. The
    ordinary case: a `D` whose queries, instance or code of a key leave out the files' digest can be
    sound at every fixed set of files and meet every goal, and a provider that writes the scale
    file, or the free numbers of the parameter file, after it has seen challenges then forges. The
    contrived case: a gate that is open where bytes of the scale file spell an answer of the hash
    function; at fixed files that has probability 2^-256, and whoever writes the scale file after
    one query brings it about. The free numbers of the parameter file have room for more than a
    hundred bits of such an answer too. Neither check of 10 sees this. Only a reading of `D` guards
    it; it asks whether the files' digest, or the files' bytes, enter every query from which the
    verifier draws a challenge.
13. No goal ties a commitment to one set of public files. Every goal speaks of one set of files at a
    time, and `commit` may ignore them: one commitment may then be accepted under all public files
    in scope. The user has to hold the right public files as it holds the right commitment.
14. What is asked, or known, at the two named sets of files alone, in one place. (a) That the honest
    side is accepted (`G3'pol`): elsewhere a verifier may always refuse, or refuse all
    weights but one set that is written into it. A goal that asks acceptance at other files is not
    in this file. `G7` and `G3'pol` meet at one set of files alone, the stored full-size example's.
    (b) That the commitments which `commit` makes are accepted, with honest proofs.
    `G9` speaks of `commit`; the verifier tests the commitment against the code in `T`; only
    `G3'pol` ties the two. Elsewhere a verifier may refuse all that `commit` makes. At all files,
    the named sets too, a verifier may also accept commitments of another make, and the extractor
    may give any weights at these (6). What `G8` with `G9` rule out at all files in scope is a false
    yes under a commitment that `commit` made: say, to the outputs of one set of weights written
    into the verifier, where there are weights w and an output that the written weights admit and w
    does not. (c) What 6 says that `G3'pol` rules out: it is ruled out at the second named set
    alone. (d) The bounds of `HonestWithin` on `prove` and `readMore`. The bound on `commit` is
    asked at all files in scope (`BindsAt`: `G9`); that on `D`'s own parser by `G8` at all files in
    scope, and by `G7` and `G7'` where the policy is exact match; `sample` does not depend on the
    files. Why these two: `readMore` and `innerCompiledVerifier` run inside every system of which the goals
    speak, at any cost; `D.parse` is reached only through "every parser with at most n queries", and
    `commit` only through the run in `BindsWith` that is in nobody's count; `sample` and `prove` are
    run in no experiment on soundness or binding. No goal of this file bounds the queries of
    `innerCompiledVerifier`, at any files, nor those of `readMore` elsewhere: a true system whose verifier
    searches, and cannot be run, may meet them all (7). (e) What 4 says: elsewhere a protocol that
    checks nothing but one very hard proof of work meets every goal here. (f) The requests and
    outputs of `FixedFacts`. (g) `FilesRead`: that files are in scope, and what is read off them, is
    stated of these two sets alone. (Ladder/Guards.lean evaluates `InScope` at a few further files
    that it makes.) At all files in scope, by `G8` alone: a verifier that accepts an empty output is
    ruled out, since no empty output meets a policy (`Policy.not_meetsPolicy_nil`,
    Policy/Front/MeetsPolicyGuards.lean); `G7` does not rule it out: every empty output is the
    model's.

Of what the verifier reads, only the bytes of the three public files are fixed before the hash
function is drawn. (The parameter file holds digests of four public tables under the second hash
function; these are bytes of a file.) The verifier asks the hash function for the files' digest
(`readConfig`), `readMore` may ask for more, and the field `T` is a function of the answers.

What the compiler takes also holds honest parties and a model (`P`; in `T`: `commit`, `prove`,
`nextToken`, `ISK`, `bound`, `π₀`); neither `innerCompiledVerifier` nor any goal reads them. A goal on the
honest side or on hiding has to speak of `systemOfRecord`, the system with `D`'s own form, parser
and prover.

Not covered: the package's small example. `settingsOfRead` always has the reference model's sizes
and 1,024 positions, no term of this library is the small example's model (see the docstrings of
`claimsSmall` and `nextSmall`, Johnson/Flat/ClaimsSizes.lean), and `verify` refuses its files. A run
at the small size runs `verifyAt` at another scope. No goal binds `D` there: a yes at another scope
shows nothing of soundness.

The numbers (section 1) are choices of this project. No theorem yields them.
-/
import VerifiableInference.MoreStatements
import VerifiableInference.Steps
import VerifiableInference.CanServe
import VerifiableInference.WellFormedRequests
import IntegerModel.Arrays.OfIndex
import Policy.Front.MeetsPolicy
import Johnson.Flat.InnerInputOfThreeProtocols
import Johnson.Flat.SettingsAtRef
import Ladder.Stored
import OnBytes.Hash.SecondHashFunction
import Run.CodingBits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open scoped ENNReal

/-! ## 1. The numbers -/

/-- The honest side may fail with at most this probability. It leaves room for an honest search for
proof of work that gives up after a bounded number of tries. -/
def completenessErrorBound : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 40

/-- The most queries to the hash function that the honest side may make. `RepliesFit` asks it, by
`WithinBudget`, of one run of the sampler, one of the committer and one of the prover together: one
commitment and one request, no batch. `bindingErrorInQueries` has it for one run of the committer. Statements
of this file that are no lines of the final statement ask it of `commit` and of `D`'s own parser, at
files in scope. One query counts as one, whatever its length; a typed query of the compiler costs
one query for each digest of its answer. The number is a choice. -/
def honestBudget : ℕ := 2 ^ 48

/-- 2^64 queries: past it the zero-knowledge line bounds no verifier and `ceiling` no adversary. -/
def queryBudget : ℕ := 2 ^ 64

/-- The goals with a ceiling say nothing where the parser has more queries than this. -/
def parserBudget : ℕ := 2 ^ 64

/-- The ceiling on the error in `G7`, `G7'`, `G8` and `G9`, up to the budgets. -/
def ceiling : ℝ≥0∞ := 4⁻¹

/-! ## 2. The other fixed terms -/

/-- Run one algorithm, then another on its result. -/
def andThen {α β : Type} :
    DeterministicAlgorithm α → (α → DeterministicAlgorithm β) → DeterministicAlgorithm β
  | .done a, f => f a
  | .query s k, f => .query s fun d => andThen (k d) f

/-- The reader of the public files: the table of scales, with the policy, that the parameter file
and the scale file state. It refuses files that it cannot read, scales that are not lawful, a policy
without C < 2^32, theta ≤ C and cap ≤ 1,024, and a parameter file in which a line on the model,
other than its sizes and scales, is not the reference model's. It does not read the layout file. -/
abbrev readFiles (Z : PublicFiles) : Except String Inst.Model.ScalesAndPolicy := settingsAtRef Z.pol Z.KL

/-- The integer model's settings at what the reader returned. -/
abbrev settingsOfRead (pp : Inst.Model.ScalesAndPolicy) : IntegerTransformer.Settings :=
  settingsOf (Cm.Scales.of pp)

/-- The output tokens are the model's: each is the model's next token after the prompt and the
output tokens before it. This is `IsModelOutput` (VerifiableInference/Statements.lean) of `system`
(section 3). -/
def ModelOutput (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (prompt output : List Token) : Prop :=
  ∀ position (h : position < output.length),
    modelNextToken s w (prompt ++ output.take position) = some output[position]

/-- The eight free numbers of the parameter file, as they stand in what the reader returned. The
reader lays eps1 and eps2 into the two normalisations of every layer; they are read here off the
first layer. -/
def freeLinesOf (pp : Inst.Model.ScalesAndPolicy) : FreeLines where
  eps1 := (pp.w 0).n1.eps.toNat
  eps2 := (pp.w 0).n2.eps.toNat
  epsF := pp.nf.eps.toNat
  MF := pp.nf.M
  KF := pp.nf.K
  C := pp.pol.C
  theta := pp.pol.theta
  cap := pp.pol.cap

/-- The public files that `verify` takes; the final statement's lines ask more (`FilesTaken`): the
reader accepts them; the layout file is the stored full-size example's (Ladder/Stored.lean); the
parameter file is that example's, byte for byte, but for the eight free numbers (`FreeLines`), which
are written as the reader read them; and 2^8 ≤ theta. So only the scale file and these eight numbers
are free, within what the reader accepts. All security settings, the version line and the layout are
fixed: files of a changed format are out of scope.
Why 2^8 ≤ theta: every token costs at least 2^8, so below it a policy is met by no output with a
counted token (theta < C) or bounds little but their number (theta = C). Policies that leave every
counted token free stay in scope: (256, 256, 1) at one counted token; theta = C with cap = 1,024 at
every request. ("Cost" and "counted token": see `MeetsPolicy`.) -/
def InScope (Z : PublicFiles) : Bool :=
  decide (Z.lay = storedPublicFiles.lay) &&
    match readFiles Z with
    | .ok pp =>
      decide (Z.pol = policyFile (freeLinesOf pp)) && decide (2 ^ 8 ≤ pp.pol.theta)
    | .error _ => false

/-- The public files at which `G3'pol` asks that the honest side is accepted: the stored
full-size example's, and the same three files with the policy (C, theta, cap) = (25856, 512, 1).
Whether proofs for either set are stored is for the package's folder examples/ to say. -/
def NamedFiles (Z : PublicFiles) : Prop := Z = storedPublicFiles ∨ Z = zGap

/-- The string that the format hashes for the digest of the three public files: `Fmt.oStr`
(Fmt/Rules23.lean) at half 0, number 169, tree 0, index 2, on their bytes. `Fmt.zero32` is the
"start" argument of that call; it is not a digest. -/
def configString (Z : PublicFiles) : BitString :=
  _root_.Run.bytesToBits (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes [Z.pol, Z.lay, Z.KL]))

/-- The digest of the three public files, asked of the hash function. -/
def readConfig (Z : PublicFiles) : DeterministicAlgorithm Digest := .query (configString Z) .done

/-- The type of a function that can take the place of the second hash function: from a
number and a list of bytes to bytes. The format also has a tree hash under that function; a `D` that
needs it has to build it from its argument. -/
abbrev SecondHashFunctionType : Type := ℕ → ByteArray → ByteArray

/-! ## 3. Everything that may change -/

/-- A typed proof: what `innerCompiledVerifier` takes from the prover's side at the protocols `F`: further
tokens, a key and a proof. It is the type `(innerSystem (innerInputOfThreeProtocols F P T)).Proof`, whatever `T` is.
The further tokens are the prover's: `T`'s field `build` makes an instance from them and from the
user's prompt and output. The claims of the goals speak of the prompt and the output alone. -/
abbrev TypedProof {C : Hiop.ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) : Type :=
  List Token × (TypedOracleCompiler.Compile.Batch.Cms.KeyRoot 256 (F.withProvers P) ×
    TypedOracleCompiler.Compile.Batch.Cms.OfflineLinkOnlineProof 256 (F.withProvers P) F.annT F.annL)

/-- The description of the protocol. `C`, `F`, `P` and `T` are what the compiler takes. The first
three, and with them the types of keys and proofs, are functions of the public files alone; of these
four only `T` may depend on values of the hash function. No field is a hypothesis: a law that a part
carries in its type has to be proved in order to build `D`. -/
structure Description where
  /-- The types of indices and instances, the relation and the encoding. -/
  C : PublicFiles → Hiop.ConfigurationWithOutOfDomainSample
  /-- The protocols of the prover's three files: key file, entry file, proof file. -/
  F : (Z : PublicFiles) → Files (C Z)
  /-- Their honest provers. They stand in the types of keys and proofs (`F.withProvers P`); their values are
  read neither by `innerCompiledVerifier` nor by any goal. -/
  P : (Z : PublicFiles) → (F Z).Provers
  /-- What the further public reading returns. -/
  More : Type
  /-- The further public reading: an algorithm with access to the hash function, from the public
  files and their digest. -/
  readMore : PublicFiles → Digest → DeterministicAlgorithm More
  /-- The rest of what the compiler takes (see `InnerCompilerInputFieldsOverThreeProtocols`, Johnson/Flat/InnerInputOfThreeProtocols.lean), as a function
  of the public files and of what the two public readings returned: among it how rounds and openings
  are laid into queries, the coding of queries into the one hash function, the code of a key, and
  how an instance is built from tokens. The goals let every field depend on the answers. -/
  T : (Z : PublicFiles) → Digest → More → InnerCompilerInputFieldsOverThreeProtocols (F Z) (P Z)
  /-- The extractor of `G8` and `G9` (and of `G8bits` and `G9bits`, Ladder/Bits.lean): one for all.
  It sees the public files, the settings, the commitment and the committer's logged queries, and
  nothing else: not the hash function, nor what the public readings returned. -/
  extractor : PublicFiles → (s : IntegerTransformer.Settings) → Commitment → QueryLog →
    Option (ModelWeights s)
  /-- What a proof may reveal of the weights: its type. No goal here reads it. -/
  Shown : Type
  /-- What a proof may reveal of the weights. No goal here reads it. -/
  shown : (s : IntegerTransformer.Settings) → ModelWeights s → Shown
  /-- The honest committer's randomness: its type. -/
  Rand : Type
  /-- The honest committer samples its randomness. `G3'pol` reads it. -/
  sample : RandomizedAlgorithm Rand
  /-- The honest committer. `G3'pol` and `G9` read it. -/
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  /-- The form that the honest prover fills in. -/
  Form : Type
  /-- `D`'s own parser. `G3'pol` reads it. -/
  parse : (Z : PublicFiles) → List Token → List Token → Form →
    DeterministicAlgorithm (TypedProof (F Z) (P Z))
  /-- The honest prover. `G3'pol` reads it. -/
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm Form

/-- The compiler's input at the public files and at what the two public readings returned. -/
abbrev Description.input (D : Description) (Z : PublicFiles) (c : Digest) (m : D.More) : InnerCompilerInput :=
  innerInputOfThreeProtocols (D.F Z) (D.P Z) (D.T Z c m)

/-- A parser: from the prompt, the output and a form, an algorithm with access to the hash function
that returns a typed proof. It does not see the commitment. It cannot refuse: from a form that it
cannot read it returns some typed proof. -/
abbrev Parser (D : Description) (Z : PublicFiles) (Form : Type) : Type :=
  List Token → List Token → Form → DeterministicAlgorithm (TypedProof (D.F Z) (D.P Z))

/-- The verifier: a test on the public files, a parser, the two public readings, then `innerCompiledVerifier`.
From the user: the public files Z, the commitment, the prompt and the output. From the prover: the
whole form. At files that fail `scope` it refuses, whatever `D` is. The final statement's lines
speak of this term at `scope := InScope` (`verify`), not of `innerCompiledVerifier (D.input Z c m)` alone. -/
def verifyAt (scope : PublicFiles → Bool) (D : Description) (Z : PublicFiles) {Form : Type}
    (parse : Parser D Z Form) (commitment : Commitment) (prompt output : List Token)
    (form : Form) : DeterministicAlgorithm Bool :=
  if scope Z then
    andThen (parse prompt output form) fun proof =>
      andThen (readConfig Z) fun c =>
        andThen (D.readMore Z c) fun m =>
          innerCompiledVerifier (D.input Z c m) commitment prompt output proof
  else .done false

/-- The verifier: `verifyAt` at the scope `InScope`. `finalVerifier` is this term at `flashProveDescription` and its
parser (`finalVerifier_eq`): a run counts for the final statement only if it runs the term there. -/
def verify (D : Description) (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form) :
    Commitment → List Token → List Token → Form → DeterministicAlgorithm Bool :=
  verifyAt InScope D Z parse

/-- The argument system of the goals: its verifier is `verify`. So every yes is at files
of which `G8` and `G9` speak. Z is a parameter of the system, so it is fixed before the hash
function is drawn (the head of this file, 12). s is the settings of the weights and the model; the
goals pass what the reader returns at Z. Soundness does not read `prove`. -/
def system (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings) (Form : Type)
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser D Z Form) : ArgumentSystem where
  Weights := ModelWeights s
  PublicParameters := D.Shown
  publicParameters := D.shown s
  CommitmentRandomness := D.Rand
  Proof := Form
  nextToken := modelNextToken s
  sampleCommitmentRandomness := D.sample
  commit := D.commit Z s
  prove := prove
  verify := verify D Z parse

/-- The system with `D`'s own form, parser and honest prover. -/
abbrev systemOfRecord (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    ArgumentSystem :=
  system D Z s D.Form (D.prove Z s) (D.parse Z)

/-- The parser asks the hash function at most n times. -/
def Parser.Within {D : Description} {Z : PublicFiles} {Form : Type} (parse : Parser D Z Form) (n : ℕ) :
    Prop :=
  ∀ prompt output form, (parse prompt output form).toRandomized.QueryBound n

/-- For one commitment and one request: in one run of `sample`, one of `commit`, one call of
`prove`, one of `readMore` and one of `D`'s own parser, the queries to the hash function are
together at most `honestBudget`. The bounds are asked at requests and forms of every length. Not
counted: the one query of `readConfig` and the queries of `innerCompiledVerifier`. -/
def HonestWithin (D : Description) (Z : PublicFiles) (s : IntegerTransformer.Settings) : Prop :=
  ∃ qSample qCommit qProve qMore qParse : ℕ,
    qSample + qCommit + qProve + qMore + qParse ≤ honestBudget ∧
    D.sample.QueryBound qSample ∧
    (∀ w ρ, (D.commit Z s w ρ).toRandomized.QueryBound qCommit) ∧
    (∀ w ρ prompt output, (D.prove Z s w ρ prompt output).QueryBound qProve) ∧
    (∀ c, (D.readMore Z c).toRandomized.QueryBound qMore) ∧
    Parser.Within (D.parse Z) qParse

/-- `D` at the second hash function. All goals but `G7'` (and `G7'bits`, Ladder/Bits.lean)
read `D` here. -/
abbrev atSecondHashFunction (D : SecondHashFunctionType → Description) : Description := D OnBytes.secondHashFunction

/-! ## 4. The goals -/

/-- Completeness for a claim: the text of `CompleteOn` (VerifiableInference/Steps.lean) with a claim
where that has "in the domain, and the output tokens are the model's". -/
def CompleteFor (system : ArgumentSystem)
    (claim : system.Weights → List Token → List Token → Prop) (α : ℝ≥0∞) : Prop :=
  ∀ (weights : system.Weights) (prompt output : List Token), claim weights prompt output →
    Prob (do
        let randomness ← system.sampleCommitmentRandomness
        let commitment ← (system.commit weights randomness).toRandomized
        let proof ← system.prove weights randomness prompt output
        (system.verify commitment prompt output proof).toRandomized)
      {accepted | accepted = false}
      ≤ α

/-- **G3'pol. The honest side is accepted for every output that can be served and meets the
acceptance policy, at the stored example's two sets of files alone.** At both sets, where they are
in scope and the reader accepts them, with `D`'s own parser: the honest side stays within
`honestBudget`; and for all weights and every output that can be served and meets the policy that
the files state, whether it is the model's own output or not, the honest commitment and proof are
accepted, except with probability `completenessErrorBound`. Of acceptance nothing is asked where a request cannot be
served; the budget is asked at every request. No goal asks the like at other files (the head of
this file, 3). If the named files were not in scope, or not read, this goal would ask nothing: see
`FilesRead`. -/
def G3'pol (D : SecondHashFunctionType → Description) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), NamedFiles Z → InScope Z = true → readFiles Z = .ok pp →
    HonestWithin (atSecondHashFunction D) Z (settingsOfRead pp) ∧
      CompleteFor (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp))
        (fun w prompt output => CanServe (settingsOfRead pp) w prompt output ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output) completenessErrorBound

/-- Soundness at all public files in scope that state exact match, for every type of form and every
parser from it to a typed proof: what a parser computes counts as sent by the prover. `D`'s own
parser is asked to stay within `honestBudget`: so it is one of these parsers, and the goals speak of
`D`'s own verifier, `verify` at `D.parse`. The bound counts queries to the hash function, at forms
of every length: a parser that asks none meets it, and so does one that asks once for each round of
the plan and, at forms of another length, returns some typed proof without a query. The error is eps
t n, where t bounds the adversary's queries and n the parser's. The queries of `readConfig`,
`readMore` and `innerCompiledVerifier` are in neither count: the error has to cover them. `Sound`'s extractor
may depend on the files, the form and the parser, and need not be `D`'s: only `G8` ties an accepted
output to the weights to which `G9` binds. -/
def SoundAt (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    pp.pol = Inst.Model.AcceptancePolicy.exact →
    Parser.Within (D.parse Z) honestBudget ∧ ∀ (Form : Type)
      (prove : ModelWeights (settingsOfRead pp) → D.Rand → List Token → List Token →
        RandomizedAlgorithm Form)
      (parse : Parser D Z Form) (n : ℕ), parse.Within n →
      Sound (system D Z (settingsOfRead pp) Form prove parse) fun t => eps t n

/-- **G7. Soundness at exact match with an error of at most one quarter, for up to 2^64 queries of
the adversary and of a parser: a bar on the error, no security level.** There is one error eps, the
same for all public files in scope that state exact match, at most the ceiling up to the two
budgets, at which `system` is `Sound`. Beyond the budgets nothing is claimed. The public files are
fixed before the hash function is drawn: a provider that picks or grinds them with the hash function
in hand is not covered; nor is a `D` ruled out that branches on a value of the real hash function
(the head of this file, 12 and 10). For a security level see `G7bits` (Ladder/Bits.lean). -/
def G7 (D : SecondHashFunctionType → Description) : Prop :=
  ∃ eps : ℕ → ℕ → ℝ≥0∞,
    (∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling) ∧ SoundAt (atSecondHashFunction D) eps

/-- **G7'. G7 whatever function stands in the second hash function's place, with the same ceiling
of one quarter and the same budgets: no security level.** One error, at most the ceiling up to the
budgets, serves every function o that is fixed before, and apart from, the drawn hash function. So
soundness does not rest on the second hash function being free of collisions. `G3'pol`
stays at the format's own function. The public files are fixed before the hash function is drawn: a
provider that picks or grinds them with the hash function in hand is not covered; nor is a `D` ruled
out that branches on a value of the real hash function (the head of this file, 12 and 10). Four
limits: 1. It says nothing of a function that depends on the drawn one. That the format's second
hash function, which shares its compression function with the format's hash function, may be treated
as apart from it stays an assumption. 2. At a function that gives the four public tables other
digests than the parameter file holds, a `D` that compares them refuses everything. The goal has
content only at functions that agree with the format's there. A `D` that is made from the library's
text of the programs' reading of the public files (`publicOf`, OnBytes/Model/VerifyPublic.lean) has
to take o in that text's calls of the second hash function: the text calls it by name. 3. As a
proposition it follows from `G7` at another `D`, made by a case split on o. No goal rules that out;
only a look at the definitions of `D` does (the head of this file, 9). 4. A `D` that binds the
request through the second hash function alone cannot meet it: the request has to stand whole in a
query to the hash function. Such a `D` fails `G7`, `G7bits` and `G8` too wherever the second hash
function has a collision between a true request and a false one: `Sound` ranges over all
adversaries. -/
def G7' (D : SecondHashFunctionType → Description) : Prop :=
  ∃ eps : ℕ → ℕ → ℝ≥0∞,
    (∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling) ∧ ∀ o : SecondHashFunctionType, SoundAt (D o) eps

/-- Soundness for the policy that the files state, at all public files in scope, for every type of
form and every parser, at `D`'s extractor and the error eps t n. `D`'s own parser is asked to stay
within `honestBudget`, as in `SoundAt`. -/
def SoundUnderPolicyAt (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    Parser.Within (D.parse Z) honestBudget ∧ ∀ (Form : Type)
      (prove : ModelWeights (settingsOfRead pp) → D.Rand → List Token → List Token →
        RandomizedAlgorithm Form)
      (parse : Parser D Z Form) (n : ℕ), parse.Within n →
      SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
        (D.extractor Z (settingsOfRead pp)) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
        fun t => eps t n

/-- **G8. Soundness under the files' acceptance policy with an error of at most one quarter, for up
to 2^64 queries of the adversary and of a parser: a bar on the error, no security level.** The
extractor is `D`'s, the same as in `G9`. The error is at most the ceiling up to the two budgets. The
public files are fixed before the hash function is drawn: a provider that picks or grinds them with
the hash function in hand is not covered; nor is a `D` ruled out that branches on a value of the
real hash function (the head of this file, 12 and 10). What a policy rules out depends on the
weights' scores as well as on its three numbers (see `MeetsPolicy`). At a policy with theta = C and
cap at least the number of counted tokens every counted token is free, and `G8` says nothing of
them; `policyEmpty` (OnBytes/Model/Config.lean) names that case, and the programs refuse there,
where the call names the policy and at least one token is counted (in the library's text of their
verifier: `cpPolicySays` and `policyEnd`, OnBytes/Model/VerifyHeads.lean). A `D` should refuse there
likewise; no goal asks it. `G8` means something only together with `G9` and `G3'pol` (the head of
this file, 6). -/
def G8 (D : SecondHashFunctionType → Description) : Prop :=
  ∃ eps : ℕ → ℕ → ℝ≥0∞,
    (∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling) ∧
      SoundUnderPolicyAt (atSecondHashFunction D) eps

/-- Binding at all public files in scope, at `D`'s extractor: for every committer and every opener,
the opener opens the committer's commitment to weights that the extractor does not give with
probability at most eps t, where t bounds their queries together. Of the system, binding reads
`commit` alone; its run in the experiment is in nobody's count. So `commit` is also asked to stay
within `honestBudget`, at all files in scope: a commitment that nobody within the budget can compute
would bind for nothing. -/
def BindsAt (D : Description) (eps : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    (∀ w ρ, (D.commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord D Z (settingsOfRead pp)) (D.extractor Z (settingsOfRead pp)) eps

/-- **G9. The commitment binds to what D's extractor gives, with an error of at most one quarter for
up to 2^64 queries: no security level.** The extractor is `G8`'s. The error is at most the ceiling
up to the budget. The honest committer stays within the honest side's budget at all files in scope
(`BindsAt`). The public files are fixed before the hash function is drawn: a provider that picks or
grinds them with the hash function in hand is not covered; nor is a `D` ruled out that branches on a
value of the real hash function (the head of this file, 12 and 10). -/
def G9 (D : SecondHashFunctionType → Description) : Prop :=
  ∃ eps : ℕ → ℝ≥0∞, (∀ t, t ≤ queryBudget → eps t ≤ ceiling) ∧ BindsAt (atSecondHashFunction D) eps

/-- **FilesRead. The two named sets of public files are in scope and are read as expected.**
`G3'pol` asks nothing without it. Ladder/Guards.lean checks both fields by evaluation whenever it
is compiled. Proved, of the written copies, not of the files on disk: `VerifierAndGoals.filesRead`. -/
structure FilesRead : Prop where
  /-- The stored full-size files are in scope, can be read, and state exact match. -/
  full : InScope storedPublicFiles = true ∧ ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact
  /-- The same files with the other policy are in scope, can be read, and state that policy. -/
  other : InScope zGap = true ∧ ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩

/-- **FixedFacts. Weights and outputs exist without which the goals would say less**, whatever `D`
is. The first two fields hold at whatever the reader returns, and ask nothing where it refuses; they
say nothing of the stored bytes, and all their witnesses are weights whose layers are all zero. None
of them says that the second named policy rules out a token. Proved: `fixedFacts`
(Ladder/Ties.lean). -/
structure FixedFacts : Prop where
  /-- Whatever the reader returns at a named set of files: there are two sets of weights and one
  prompt with two different outputs of one length, each of which can be served and is the model's
  output at its own set of weights. Otherwise `G3'pol` would not rule out a `D` with one set of
  weights written into it. -/
  claim : ∀ Z pp, NamedFiles Z → readFiles Z = .ok pp →
    ∃ (w w' : ModelWeights (settingsOfRead pp)) (prompt output output' : List Token),
      CanServe (settingsOfRead pp) w prompt output ∧
        ModelOutput (settingsOfRead pp) w prompt output ∧
        CanServe (settingsOfRead pp) w' prompt output' ∧
        ModelOutput (settingsOfRead pp) w' prompt output' ∧
        output.length = output'.length ∧ output ≠ output'
  /-- Where the reader returns the other policy at the other files: some output can be served, meets
  the policy and is not the model's. Otherwise `G3'pol` would ask no more than acceptance of the
  model's own output. -/
  otherClaim : ∀ pp, readFiles zGap = .ok pp → pp.pol = ⟨25856, 512, 1⟩ →
    ∃ (w : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      CanServe (settingsOfRead pp) w prompt output ∧
        Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output ∧
        ¬ ModelOutput (settingsOfRead pp) w prompt output
  /-- The honest side's failure and the ceiling together stay below 1, and the honest side's budget
  is within both budgets of `G7`, so `G7` speaks of the system that `G3'pol` speaks of. -/
  numbers : completenessErrorBound + ceiling < 1 ∧ honestBudget ≤ queryBudget ∧ honestBudget ≤ parserBudget

end VerifierAndGoals
