-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontParts.lean: a record of named hypotheses under which a Lean verifier that is a
function of (files, hash function) is sound over a drawn hash function, in a game whose extractor
may query the hash function (`SoundForWithO`; not this library's own `Sound`): five hypotheses link
its yes to the yes of the checks' verifier, and further ones: bounds on the three checks, that
the public reading (a computation that queries the hash function) tosses no coin and keeps a budget
of queries, that no check tosses a coin, that index binding passes behind the hash of the key's code
(`commitment`), the meaning of the extracted index, a bound on the error, the parser's budget and a
bound on the exception's probability. Every hypothesis is left open here.

What this file states. The front verifier is `p.port` of a `PortArmsC r`
(Johnson/Top/OnFilesPortC.lean): any term that takes a commitment ID, a prompt, output tokens and
the files that a prover hands over, and asks the hash function as an oracle. The checks' verifier
is the system of the three checks that r holds, behind the hash of a key's code (`systemArmsC r`,
Johnson/Top/OnFilesArmsC.lean). A parser (`p.reader`) makes typed strings of the files.
`front_sound`: under `FrontFields`: `SoundForWithO` of the system whose verifier is the front
verifier, with the error ε (t + n) + δ t. `SoundO`, `front_soundO`: the same at the system's own
claim ("the output tokens are the model's"), the extractor bound by "there is". `front_sound_text`:
the parts in the library's own game: from `FrontParts` and soundness of the three checks' system for
an extractor that reads the log alone: `Sound`, in the text of VerifiableInference/Statements.lean.
Its second premise is proved at no input in this library. `Rec.soundForWith_systemE`
(Johnson/Top/FrontEnc.lean) leads to it from index binding of the three checks' scheme with an
extractor that reads the log alone, and a key's code that is one to one. How `front_sound` is
proved: `verify_sound_arms_CD` (bounds, commitment and meaning give soundness of the three checks'
system) and `verify_sound_portC_O` (a linking statement at every g carries soundness to the front
verifier; Johnson/Top/SoundVia.lean).
Two applications.

The experiment (it is `Sound`'s): one hash function is drawn. A committer puts out 32 bytes, the
commitment ID, and a state. A prover, given the state, puts out prompt, output tokens and all files,
the key file among them: the claim comes from the adversary, with the proof. Both together ask at
most t queries. Prompt and output are arguments of both verifiers, and the instance is made of them
inside the checks' verifier (`r.build`): a parser brings further tokens, a key and typed strings.
The theorems hold for every parser that is fixed before the function is drawn: it can be read as the
prover's last step. Public files are no part of the experiment: where r and p are made of them, they
are fixed before the function is drawn.

Under which hypotheses. The front verifier is linked to the checks' verifier by five hypotheses:
the fields `request`, `idPart`, `keyPart`, `entryPart` and `proofPart`. Each is one hypothesis on
the front verifier's whole yes, at every hash function: where it says yes, that step of the
checks' verifier says yes on what the parser returns, or the named exception says yes. The type
cuts the front verifier into no parts: `p.port` is one term. With them go the parser's `budget` and
`price`, the bound on the named exception's probability. `FrontFields p b claim extO q εO ε`: all
named hypotheses: `parts`; `arms` (the three checks' bounds over a drawn function: `CoreArmsCD`,
Johnson/Top/OnFilesArmsCD.lean); `commitment`; `meaning`; `error`.

What it does not show.
- Every field is a hypothesis; a conditional theorem holds vacuously where a field is false: it
  claims nothing there.
- The game of `front_sound` is not `Sound`'s. `Sound` has an extractor that reads the
  commitment and the committer's log alone. `SoundForWithO` (Johnson/Top/SoundO.lean) has an
  extractor that may also query the hash function, at most q times. `SoundO` is `Sound`'s text with
  that one change. No theorem of this library passes from the second to the first at q > 0.
- One reason for the queries: the checks' promises are read at public digests that a committer
  need not have asked for; whether that alone forces the oracle game is not said. The commitment
  ID's string is no reason for them: it holds the record's seed (`publishedBytes`, Fmt/Rules4.lean).
  Where the public digest is in the typed key, the checks test it, and the key's code is one to one,
  they fall away: Johnson/TypedOracleCompiler/Top/FrontSoundTold.lean ends in `Sound` itself, under named
  hypotheses.
- A field can be had with no linking hypothesis and no exception, of a changed verifier.
  `withCheck` adds a check next to the given text, which stays and runs too; where the added check
  is "parse, then r's check", the changed verifier's yes holds that check's
  yes by definition. The one lemma of that kind here is the entry file's (`entryPart_of_parseThen`),
  at one g and one call.
- The check that `withCheck` adds does not see the commitment, so `idPart` cannot be had by it.
- The text of `front_sound` does not turn when a field is had so, because p is a parameter; the
  term in its place turns, and it is another verifier than before.
- Where an added check and the given text test one thing by two texts, the changed verifier says
  yes only where both do: if the two cannot say yes together, it never says yes, and all five hold
  of it vacuously: they claim nothing.
- The link goes one way: the front verifier accepts only what the checks' verifier accepts,
  outside a named exception with a bound on its probability; it is not said that the two accept the
  same. r, p (the files' type, an honest prover, the front verifier, the parser, its budget, the
  named exception, the bound on its probability), b (the public reading, the word under a root, the
  relation, the three errors), the extractor, q and the errors are parameters, and vacuous
  instances, which meet the hypotheses and say nothing, come in through each: a front verifier that
  never says yes; an exception that always says yes (then no bound below 1 on its probability
  exists); checks that are not the compiler's output; checks that toss coins (`.det` takes every
  draw as 0; `CoreArmsCD.noCoin` forbids it); a public reading that is not what the checks ask; a
  relation that every instance meets; a claim that some index meets at all prompts and outputs; a
  model (`r.nextToken`, `r.I`) that is not the model; a word under a root that is constant, a
  decoder that is none everywhere or a collision predicate that always holds (each can free the
  proof file's promise); a code or a builder that is none everywhere (then every yes must go through
  the named exception); a front verifier that behaves as the program only at one function's answers;
  errors of 1 or more, also through a budget n so large that ε (t + n) is 1.
- The idle member (the files are the typed proof, the front verifier is the checks' own verifier,
  the parser hands its input on) meets `FrontParts` by definition: it is harmless; it has the shape
  of the design "a parser outside, then the verifier", where what the parser returns counts as the
  prover's message.
- It says something only at written terms, and none is given here; so nothing here has run.
- The exception is a parameter, so "at every g" has no force of its own: at the named exception
  "the front verifier says yes and a part fails" all five linking hypotheses hold by logic, and all
  weight lies in `price`.
- The front verifier, the parser, the named exception and the checks reach g by queries, but their
  next steps are arbitrary functions: one that holds a fixed hash function, or values of it, is a
  legal member.
- A part linked by a hypothesis at every g polices its parser; for a part that is "parse, then
  r's check" by definition nothing does.
- That these terms hold no hash function but the one that they ask is no theorem: at written terms
  it wants a scan of constants over all of them.
- A part that holds by definition moves the burden: that any program runs that check is not said.
- `meaning` is a hypothesis that can be false, not a definition.
- No field bounds q.
- `budget` requires one number for all files: a written parser meets it only if it caps itself
  (tests the files' sizes before it asks).
- A parser is total by its type and does not see the commitment: one that fails must return what
  the checks refuse.
- No number is given for the error.
- Soundness alone. For proofs only; the program does not import this file.


-/
import Johnson.Top.OnFilesPortC
import Johnson.Top.OnFilesArmsCD
import Johnson.Top.FrontGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC} (p : PortArmsC r)

/-- The front verifier says yes at g. -/
def PortArmsC.Yes (g : Hash) (c : Commitment) (prompt output : List Token) (F : p.Files) : Prop :=
  (p.port c prompt output F).evaluate g = true

/-- The exception says yes at g. -/
def PortArmsC.Out (g : Hash) (c : Commitment) (prompt output : List Token) (F : p.Files) : Prop :=
  (p.exc c prompt output F).evaluate g = true

/-- What the parser makes of the files at g. -/
def PortArmsC.parsed (g : Hash) (prompt output : List Token) (F : p.Files) :
    List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL) :=
  (p.reader prompt output F).evaluate g

/-- The front verifier's parts, each at every hash function g: where the front verifier says yes,
that part of the checks' verifier says yes on what the parser returns, or the named exception
says yes. -/
structure FrontParts : Prop where
  /-- the request: the builder makes an instance of prompt, output and what the parser brings -/
  request : ∀ g c prompt output F, p.Yes g c prompt output F →
    (∃ x, r.build (prompt, output) (p.parsed g prompt output F).1 = some x) ∨
      p.Out g c prompt output F
  /-- the commitment ID: the key that was parsed has a code, and g sends it to c -/
  idPart : ∀ g c prompt output F, p.Yes g c prompt output F →
    (∃ code, r.enc (p.parsed g prompt output F).2.1 = some code ∧ g code = c) ∨
      p.Out g c prompt output F
  /-- the key file -/
  keyPart : ∀ g c prompt output F x, p.Yes g c prompt output F →
    r.build (prompt, output) (p.parsed g prompt output F).1 = some x →
    (liftKC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
      (fun _ => g) = true ∨ p.Out g c prompt output F
  /-- the entry file -/
  entryPart : ∀ g c prompt output F x, p.Yes g c prompt output F →
    r.build (prompt, output) (p.parsed g prompt output F).1 = some x →
    (liftEC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
      (fun _ => g) = true ∨ p.Out g c prompt output F
  /-- the proof file -/
  proofPart : ∀ g c prompt output F x, p.Yes g c prompt output F →
    r.build (prompt, output) (p.parsed g prompt output F).1 = some x →
    (liftPC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
      (fun _ => g) = true ∨ p.Out g c prompt output F
  /-- the parser's budget of queries -/
  budget : ∀ prompt output F, (p.reader prompt output F).toRandomized.QueryBound p.n
  /-- the bound on the exception's probability over a hash function drawn at random -/
  price : ExceptionBound p.exc p.δ

variable {p}

/-- The parts give the three hypotheses of `PortTiesC`. -/
theorem FrontParts.ties (h : FrontParts p) : PortTiesC p where
  budget := h.budget
  price := h.price
  tie := by
    intro g c prompt output F hy
    have y : p.Yes g c prompt output F := hy
    by_cases e : p.Out g c prompt output F
    · exact Or.inr e
    · obtain ⟨x, hx⟩ := (h.request g c prompt output F y).resolve_right e
      obtain ⟨code, hc, hg⟩ := (h.idPart g c prompt output F y).resolve_right e
      exact Or.inl ⟨(p.parsed g prompt output F).1, (p.parsed g prompt output F).2.1,
        (p.parsed g prompt output F).2.2, x, code, rfl, hx, hc, hg,
        (h.keyPart g c prompt output F x y hx).resolve_right e,
        (h.entryPart g c prompt output F x y hx).resolve_right e,
        (h.proofPart g c prompt output F x y hx).resolve_right e⟩

variable (p)

/-- One check (`arm`, a parameter) behind the parser: parse; make the instance; run the check
on what was parsed. No where the builder makes no instance. -/
def parseThen (arm : r.C × KeyRoot 256 r.L → r.X → OfflineLinkOnlineProof 256 r.L r.aT r.aL →
      Rom.OComp (rom 256) Bool) (prompt output : List Token) (F : p.Files) :
    DeterministicAlgorithm Bool :=
  (p.reader prompt output F).andThen fun a =>
    match r.build (prompt, output) a.1 with
    | some x => deterministicOf (Rom.ofRom (arm a.2.1 x a.2.2))
    | none => .done false

/-- Its value at g. -/
theorem evaluate_parseThen (arm : r.C × KeyRoot 256 r.L → r.X → OfflineLinkOnlineProof 256 r.L r.aT r.aL →
      Rom.OComp (rom 256) Bool) (g : Hash) (prompt output : List Token) (F : p.Files) (x : r.X)
    (hx : r.build (prompt, output) (p.parsed g prompt output F).1 = some x) :
    (parseThen p arm prompt output F).evaluate g =
      (arm (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det fun _ => g := by
  unfold parseThen
  rw [DeterministicAlgorithm.evaluate_andThen]
  show (match r.build (prompt, output) (p.parsed g prompt output F).1 with
    | some x => deterministicOf (Rom.ofRom (arm (p.parsed g prompt output F).2.1 x
        (p.parsed g prompt output F).2.2))
    | none => .done false).evaluate g = _
  rw [hx]
  exact OnBytes.K.evaluate_ofRom g _

/-- The front verifier with one check more: p's own text runs, then the check; yes where both say
yes. The check sees prompt, output and files, not the commitment. Parser, budget, exception and the
exception's bound stay. -/
def PortArmsC.withCheck (extra : List Token → List Token → p.Files → DeterministicAlgorithm Bool) :
    PortArmsC r :=
  { p with
    port := fun c prompt output F => (p.port c prompt output F).andThen fun a =>
      (extra prompt output F).andThen fun b => .done (a && b) }

/-- Where the front verifier with one check more says yes, both say yes. -/
theorem PortArmsC.yes_withCheck
    (extra : List Token → List Token → p.Files → DeterministicAlgorithm Bool) {g : Hash}
    {c : Commitment} {prompt output : List Token} {F : p.Files}
    (h : (p.withCheck extra).Yes g c prompt output F) :
    p.Yes g c prompt output F ∧ (extra prompt output F).evaluate g = true := by
  have h' : ((p.port c prompt output F).andThen fun a =>
      (extra prompt output F).andThen fun b => .done (a && b)).evaluate g = true := h
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen] at h'
  exact Bool.and_eq_true_iff.1 h'

/-- Of the front verifier with "parse, then the entry file's check" laid in, what the field
`entryPart` asks holds by definition, at g and these arguments: without the field `tie` and without
the exception. It is a changed verifier: p's own text runs too. Stated of the entry file's check
alone: no lemma here says the like of the key file's or the proof file's. -/
theorem entryPart_of_parseThen {g : Hash} {c : Commitment} {prompt output : List Token}
    {F : p.Files} {x : r.X}
    (h : (p.withCheck (parseThen p (liftEC r))).Yes g c prompt output F)
    (hx : r.build (prompt, output) (p.parsed g prompt output F).1 = some x) :
    (liftEC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
      (fun _ => g) = true :=
  (evaluate_parseThen p (liftEC r) g prompt output F x hx).symm.trans (p.yes_withCheck _ h).2

variable (b : BesideArmsCD r)

/-- All named hypotheses of `front_sound`. -/
structure FrontFields (claim : r.I → List Token → List Token → Prop)
    (extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) (q : ℕ) (εO : ℕ → ℕ → ℝ≥0∞)
    (ε : ℕ → ℝ≥0∞) : Prop where
  /-- the four parts, the request, the parser's budget, the bound on the exception's probability -/
  parts : FrontParts p
  /-- the three checks' bounds over a hash function drawn at random, the public reading and
  "no coin" -/
  arms : CoreArmsCD b
  /-- the commitment: binding behind the hash of the key's code -/
  commitment : HoleArmsCD.commitmentOO b extO q εO
  /-- the meaning: what is true of the extracted index is the claim -/
  meaning : HoleArmsCD.soundFor b claim
  /-- the error's name -/
  error : ∀ tC tP, εO tC tP ≤ ε (tC + tP)

variable {p b}

/-- Under the named fields: soundness of the system whose verifier is the front verifier, over a
drawn hash function, in the game whose extractor may query it. -/
theorem front_sound {claim : r.I → List Token → List Token → Prop}
    {extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)} {q : ℕ} {εO : ℕ → ℕ → ℝ≥0∞}
    {ε : ℕ → ℝ≥0∞} (h : FrontFields p b claim extO q εO ε) :
    SoundForWithO (systemPortC p) (fun c l => deterministicOf (extO.Ei c l)) q claim
      fun t => ε (t + p.n) + p.δ t :=
  verify_sound_portC_O h.parts.ties
    (verify_sound_arms_CD claim extO q εO ε h.arms h.commitment h.meaning h.error)

/-- `Sound` (VerifiableInference/Statements.lean) with one change: the extractor is an algorithm
that may query the hash function, at most q times. -/
def SoundO (system : ArgumentSystem) (q : ℕ) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∃ extractor : Commitment → QueryLog → DeterministicAlgorithm (Option system.Weights),
    SoundForWithO system extractor q system.IsModelOutput ε

/-- `front_sound` at the system's own claim. -/
theorem front_soundO
    {extO : ZKCP.ExtractorO 256 r.I r.X Unit (ZKCP.Digest 256)
      ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)} {q : ℕ} {εO : ℕ → ℕ → ℝ≥0∞}
    {ε : ℕ → ℝ≥0∞} (h : FrontFields p b (systemPortC p).IsModelOutput extO q εO ε) :
    SoundO (systemPortC p) q fun t => ε (t + p.n) + p.δ t :=
  ⟨_, front_sound h⟩

/-- The parts in this library's own game: from them and soundness of the three checks' system, for
an extractor that reads the commitment and the log alone, follows `Sound` of the system whose
verifier is the front verifier. -/
theorem front_sound_text (h : FrontParts p) {extractor : Commitment → QueryLog → Option r.I}
    {ε : ℕ → ℝ≥0∞}
    (hs : SoundForWith (systemArmsC r) extractor (systemArmsC r).IsModelOutput ε) :
    Sound (systemPortC p) fun t => ε (t + p.n) + p.δ t :=
  ⟨extractor, verify_sound_portC h.ties hs⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.FrontParts.ties
#print axioms VerifiableInference.OnPublicFiles.entryPart_of_parseThen
#print axioms VerifiableInference.OnPublicFiles.front_sound
#print axioms VerifiableInference.OnPublicFiles.front_soundO
#print axioms VerifiableInference.OnPublicFiles.front_sound_text
