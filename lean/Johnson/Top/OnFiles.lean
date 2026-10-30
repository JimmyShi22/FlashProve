-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFiles.lean: soundness of the argument system that the compiler with a record makes
from a protocol description, for every description, under named hypotheses.

Definitions, two structures of hypotheses, and theorems with their proofs. The proofs go through
Johnson/Top/OnFilesAt.lean, the same theorem for any object with records: `d.toAt` is the
description there whose object is the passed object `d.L`.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `ProtocolDescription`: a configuration, its five sub-protocols and their lists of errors; what the
    compiler reads beside them (samplers, bits of work, wires, the coding of the typed oracles in
    one hash function); what the front reads (the code of a key, how an instance is built from a
    prompt with output tokens, the model); the extractor behind the commitment; the honest
    committer and prover; the stated numbers.
  `scheme d`: the scheme whose verifier is `Compile.Batch.Cms.VR d.W d.Sd d.p`
    (Johnson/RecCompile/FrontRoot.lean): the compiled verifier with a record, `VC`
    (Johnson/RecCompile/Cms.lean), with the key cut to the root and the record; the test's proof
    and one link travel in each proof and are checked at every call.
  `systemOf d`, `verify d`, `extractorOf d`, `soundnessErrorOf d`: the argument system made from
    `scheme d` by the steps of Johnson/Top/FrontEnc.lean, its verifier, the named extractor, the
    bound.
  `Hole.‹name› d`: the named hypotheses, one definition each, with one sentence each.
  `Core d`: the 21 hypotheses that name no claim. `Holes d`: these and `Hole.sound d`.
  `verify_sound_for`: `Core d` and `Hole.soundFor d claim` give `SoundForWith` for `claim`.
  `verify_sound`: `Holes d` gives `SoundForWith` for "the output tokens are the model's".
  `Core.binds`: index binding of `scheme d`. `Hole.commitment_of_code`: see `Hole.commitment`.
  `ProtocolDescription.toAt`, `systemOf_eq_at`, `extractorOf_eq_at`, `soundnessErrorOf_eq_at`,
  `Core.toAt`, `Holes.toAt`: the description, the system, the extractor, the bound and the
    hypotheses one floor lower.
Limits:
  No description is given here, and none is shown to meet `Holes d`. That `verify d`, at some d, is
  what a program outside this library runs is not said here.
  Three things stand outside `Holes d`. (1) `d.m : Rom.OracleCoding` holds laws in its type
  (Rom/Family.lean): the answers of every typed oracle are blocks of 256 bits, and the coding of
  (oracle, query, block) is a bijection onto all bit strings. `d.W` holds point structures with
  their laws; `ConfigurationWithOutOfDomainSample`, every round and every sampler hold instances of finiteness and
  non-emptiness. (2) The hash function is one random function with 256-bit answers: that model
  is in the definition of `SoundForWith`. (3) The model `d.nextToken` and the indices `d.C.I` are
  fields of d; they meet the protocol through `Hole.sound` alone.
  No hypothesis says that κs · κ is small: the theorems hold at every κ, and say something only
  where the bound is below 1.
  A description can make the theorems true and empty: if `build` or `enc` always answer `none` the
  verifier rejects everything; at κ = ⊤, κs = ⊤ or εId = ⊤ the bound is ⊤; if no witness meets
  `C.Rno`, `Hole.sound` holds of itself; if `build` itself refuses every output that is not the
  model's, `Hole.sound` holds whatever the relation is, and the theorems say nothing on the
  protocol. No hypothesis says that `verify d` accepts anything.
  The commitment is the hash function's answer at `d.enc` of the key (root, record). That `d.enc`
  is the string that a program hashes is not said here. A record is a seed with answers; the seed
  is a function of the hash function's answer at the root. A code that leaves the seed out is not
  one to one, so `Hole.commitment_of_code` does not apply to it: there `Hole.commitment` is a
  hypothesis on `d.ext` and `d.εId` that this library does not prove. It is of another kind than
  the other hypotheses: its premise follows from them (`Core.binds`), so under them it asserts its
  conclusion, index binding of the whole scheme behind the commitment, outright. The format's
  commitment ID holds the record's seed (`Fmt.publishedBytes`, Fmt/Rules4.lean); a code that spells
  that string is one to one at the type of key of Johnson/Top/InnerCompiledVerifier.lean
  (`idCodeSeed_oneToOne`, Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean, if the two spellings are one to one).
  Nothing is laid in `d.enc` here.
  The compiler's theorem asks that no part of an instance is named late
  (`cmsR_binding_work`, Johnson/RecCompile/FrontRoot.lean).
  Does not say: completeness; zero knowledge; that the extractor returns an honest committer's
  index.

-/
import Cb.Thin.Cond.TargetSoundOnly
import Johnson.RecCompile.Join
import Johnson.Top.OnFilesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Iop Hiop Compile Compile.Batch Compile.Batch.Cms

/-- What `verify` reads, what the hypotheses speak of, the honest side's algorithms, and the stated
numbers. -/
structure ProtocolDescription where
  /-- The configuration: indices, instances, the relations, the record. -/
  C : ConfigurationWithOutOfDomainSample
  /-- The five sub-protocols: key file (wf, linOff), entry file (link), proof file (req, linOn). -/
  S : SubsR C
  /-- Their lists of errors. `verify` does not read them; the hypotheses do. -/
  P : S.Nums
  /-- The nonces of the proof of work. -/
  Nn : Type
  [inh : Inhabited Nn]
  /-- The maps from hash answers to verifier messages, round by round, for the three files. -/
  σT : Samplers S.lhr.offline.shape
  σL : Samplers S.lhr.link.shape
  σB : Samplers S.lhr.onlineBatch.loc.shape
  /-- The bits of work, round by round. -/
  g : S.Bits
  /-- The wire of the passed object: how rounds and openings are laid into hash queries. -/
  W : QueryLayout 256 (S.lhrW Nn σT σL σB g).carrierC
  /-- The wire of the record. -/
  Sd : OutOfDomainSampleQueryLayout 256 W.K (S.lhrW Nn σT σL σB g)
  p : Params
  /-- The typed oracles in one hash function. -/
  m : OracleCoding (spec 256 W.K (S.lhrW Nn σT σL σB g).carrierC) 256
  /-- The code of a key: the hash function's answer at it is the commitment. -/
  enc : KeyRoot 256 (S.lhrW Nn σT σL σB g) → Option ZKCP.Str
  /-- The extractor behind the commitment. For the index it reads the commitment and the
  committer's query log. `verify` does not read it; the theorems name it. -/
  ext : ZKCP.Extractor 256 C.I C.X Unit (ZKCP.Digest 256)
    (KeyRoot 256 (S.lhrW Nn σT σL σB g) × PrfRoot 256 (S.lhrW Nn σT σL σB g))
  /-- The stated cost of the commitment, in the sum of the two bounds on queries. -/
  εId : ℕ → ℝ≥0∞
  /-- From a prompt with output tokens, and further tokens that the proof brings, an instance. -/
  build : List Token × List Token → List Token → Option C.X
  /-- The model. `verify` does not read it; the claim does. -/
  nextToken : C.I → List Token → Option Token
  /-- The honest side. Nothing is asked of these six, nor of the five honest provers in `S`. -/
  ISK : Type
  commit : C.I → Rom.OComp (spec 256 W.K (S.lhrW Nn σT σL σB g).carrierC)
    (KeyRoot 256 (S.lhrW Nn σT σL σB g) × ISK)
  prove : ISK → (b : List (C.X × Unit)) →
    Rom.OComp (spec 256 W.K (S.lhrW Nn σT σL σB g).carrierC)
      (ZKCP.Gen.Slots (PrfRoot 256 (S.lhrW Nn σT σL σB g)) b)
  bound : ℕ
  π₀ : KeyRoot 256 (S.lhrW Nn σT σL σB g) × PrfRoot 256 (S.lhrW Nn σT σL σB g)
  x₀ : C.X
  /-- The stated bias of the samplers. -/
  κs : ℝ≥0∞
  /-- The stated bound on a round's error, its work counted. -/
  κ : ℝ≥0∞

attribute [instance] ProtocolDescription.inh

variable (d : ProtocolDescription)

/-- The object with records, passed (its verifier messages made by the samplers, its rounds with
their proof of work): what the compiler takes. -/
abbrev ProtocolDescription.L : HolographicProtocol d.C.I d.C.X := d.S.lhrW d.Nn d.σT d.σL d.σB d.g

/-- The scheme. Its verifier is the compiled verifier with a record, the key being the root and the
record. -/
def scheme : ZKCP.Gen.Arg (spec 256 d.W.K d.L.carrierC) d.C.I d.C.X Unit (KeyRoot 256 d.L) d.ISK
    (PrfRoot 256 d.L) :=
  ⟨d.commit, d.prove, VR d.W d.Sd d.p⟩

/-- The argument system made from the description. -/
def systemOf : ArgumentSystem :=
  Rec.tokenArgumentSystem (schemeOverOneHashFunction d.m (scheme d)) d.enc d.bound d.build d.π₀ d.nextToken

/-- The verifier. -/
def verify := (systemOf d).verify

/-- The named extractor. It reads the commitment and the committer's query log alone. -/
def extractorOf : Commitment → QueryLog → Option d.C.I :=
  (d.ext.buildInstance : ZKCP.Extractor 256 d.C.I (List Token × List Token) Unit (ZKCP.Digest 256)
    (List Token × (KeyRoot 256 d.L × PrfRoot 256 d.L))).Ei

/-- The bound, in t, the sum of the bounds on the committer's and the prover's queries to the hash
function: (t + tVC + 1) · κs · κ + 2 (t + tVC + 2)² / 2^256 + εId t, where tVC bounds the typed
queries of the compiled verifier. -/
def soundnessErrorOf : ℕ → ℝ≥0∞ :=
  fun t => epsC d.W (d.κs * d.κ) t 0 + d.εId t

/-- An instance is true at an index: some witness meets the relaxed relation. -/
def IsTrue (i : d.C.I) (x : d.C.X) : Prop := ∃ w, d.C.Rno i x w

/-! ## The named hypotheses -/

namespace Hole

/-- Key file: the sub-protocol "the committed weights are well formed" has round-by-round knowledge
soundness, with the listed errors, on the statements without a collision; an output with a
collision counts as a win of the prover and is counted in the errors. -/
def wfKnow : Prop := PreKnowR d.S.off d.S.wf d.C.free d.C.RwfR (fun _ _ _ => ()) d.P.wf.err
/-- Key file: the offline linear test has round-by-round knowledge soundness, with the listed
errors, on all statements without a collision, whether the encoded index decodes or not. -/
def linOffKnow : Prop := LinKnowR d.S.off d.S.linOff d.S.dOff d.P.linOff.err
/-- Entry file: the link between the first encoded index and a further one has round-by-round
soundness, with the listed errors, on the statements whose first encoded index decodes to an index
and whose further one has no collision; nothing is extracted. -/
def linkKnow : Prop := LinkKnowR d.S.link d.P.link.err
/-- Proof file: the sub-protocol for one request has round-by-round knowledge soundness, with the
listed errors, on the statements at which the index decoder answers; an output with a collision
counts as a win of the prover and is counted in the errors. -/
def reqKnow : Prop :=
  PreKnowR d.S.on d.S.req (fun a => (d.C.D a.2 a.1.2).isSome) d.C.RreqR d.S.cellsOf d.P.req.err
/-- Proof file: the online linear test over a batch of requests has round-by-round knowledge
soundness, in the form for batches, with the listed errors: for each record, with that record in
all slots, on the statements without a collision whose encoded index decodes with the record. -/
def linOnKnow : Prop := LinBKnowR d.S.on d.S.linOn d.S.N d.S.dOn d.P.linOn.err
/-- The request's sub-protocol hands the record on unchanged. -/
def passes : Prop := ∀ x y τ b, d.S.req.out x y τ = some b → b.2 = x.2
/-- The request's sub-protocol copies the encoded index unchanged. -/
def copy : Prop := ∀ y τ, (d.S.req.imp y τ).1 = y
/-- The verifier of "well formed" reads its oracles at the positions that it declares alone. -/
def wfLocal : Prop := d.S.wf.IsLocal
/-- The verifier of the offline linear test reads its oracles at the declared positions alone. -/
def linOffLocal : Prop := d.S.linOff.IsLocal
/-- The verifier of the link reads its oracles at the declared positions alone. -/
def linkLocal : Prop := d.S.link.IsLocal
/-- The verifier of the request's sub-protocol reads its oracles at the declared positions alone. -/
def reqLocal : Prop := d.S.req.IsLocal
/-- The verifier of the online linear test reads its oracles at the declared positions alone. -/
def linOnLocal : Prop := d.S.linOn.ior.IsLocal
/-- The online test's marks (which rounds a batch shares, which are a request's own) fit together
round by round. -/
def coherent : Prop := d.S.linOn.ann.Coherent
/-- Numbers: in every round of the key file's protocol, the map from hash answers to verifier
messages makes no message more than κs times as likely as a uniform draw would. -/
def samplersT : Prop := ∃ K, d.σT.Good d.κs K
/-- Numbers: the same for every round of the entry file's protocol. -/
def samplersL : Prop := ∃ K, d.σL.Good d.κs K
/-- Numbers: the same for every round of the proof file's protocol. -/
def samplersB : Prop := ∃ K, d.σB.Good d.κs K
/-- Numbers: in each of the five lists every round's error, with that round's proof of work
counted, is at most κ. -/
def below : Prop := d.P.BelowG d.g d.κ
/-- The record: for every word, the seed made from uniform digests is a seed at which that word has
a collision with probability at most κs · κ. -/
def seedLaw : Prop := d.Sd.Law (d.κs * d.κ)
/-- The layout, at the passed object (`QueryLayout.OKG`, `ProtocolQueryLayout.OKG`, `WireRB.OKG`, Iop/BatchWire.lean):
every oracle position has its own leaf in its tree and every used leaf a position; depths and the
number of openings are large enough; the number of slots is a power of two; and in every round the
message (there: the sampler's source) is made from hash answers so that uniform answers give an
exactly uniform message. -/
def wires : Prop := d.W.OKG ∧ (wTC d.W).OKG ∧ (wLC d.W).OKG ∧ (wBC d.W).OKG
/-- The record: no two records are written as the same list of digests. -/
def recordCode : Prop := Function.Injective d.Sd.code
/-- The commitment: index binding of the compiled scheme, whose verifier holds the key itself, gives
index binding of the scheme whose verifier holds the hash function's answer at the key's code, with
the extractor `d.ext`, at the cost of `d.εId (tC + tP)`. If no two keys have the same code it holds
with the library's extractor at (tC + tP + 2)² / 2^256 (`commitment_of_code`). A code that leaves
the record's seed out is not of that kind. For such a code this library has no proof, which does not
say that there is none: the index-binding game's extractor sees the commitment and the committer's
query log and has no access to the hash function, so it cannot compute a seed that the committer
never asked for. What would give a proof there: an extractor that needs no seed, or a game whose
extractor may query the hash function. Johnson/Top/GameO.lean defines such a game
(`ZKCP.HasIndexBindingWithO`); a bound in it is no proof of this hypothesis. The format's commitment
ID holds the record's seed (`Fmt.publishedBytes`, Fmt/Rules4.lean). At this file's type of key this
library has no code with the seed; at that of Johnson/Top/InnerCompiledVerifier.lean it has one, which is of
that kind if the two spellings are one to one (`idCodeSeed_oneToOne`,
Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean). -/
def commitment : Prop :=
  ZKCP.HasIndexBindingWith (ZKCP.languageRelation (IsTrue d))
      (SpecialAny.oneOf (schemeOverOneHashFunction d.m (scheme d)))
      (Special.extOf (extractorOverOneHashFunction d.m (indexExtractorAtRootAndOutOfDomainSample d.W))) (epsC d.W (d.κs * d.κ)) →
    ZKCP.HasIndexBindingWith (ZKCP.languageRelation (IsTrue d))
      ((SpecialAny.oneOf (schemeOverOneHashFunction d.m (scheme d))).digestKey d.enc) d.ext
      fun tC tP => epsC d.W (d.κs * d.κ) tC tP + d.εId (tC + tP)
/-- The meaning, for a claim: if an instance is built from a prompt with output tokens and is true
at an index (some witness meets the RELAXED relation), then the claim holds at that index of the
prompt and the output tokens. -/
def soundFor (claim : d.C.I → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) a x, d.build x' a = some x → IsTrue d i x → claim i x'.1 x'.2
/-- The meaning: `soundFor` at the claim "the output tokens are the model's". -/
def sound : Prop := soundFor d (systemOf d).IsModelOutput

/-- A code under which no two keys agree gives `commitment`, at the library's extractor and cost. -/
theorem commitment_of_code (h : ZKCP.CodeIsOneToOne d.enc)
    (he : d.ext = (Special.extOf (extractorOverOneHashFunction d.m (indexExtractorAtRootAndOutOfDomainSample d.W))).digestKey d.enc)
    (hε : ∀ t, d.εId t = (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) : commitment d := by
  intro hb tC tP St Ct Pt hC hP
  rw [he]
  show _ ≤ epsC d.W (d.κs * d.κ) tC tP + d.εId (tC + tP)
  rw [hε]
  exact hb.digestKey h tC tP St Ct Pt hC hP

end Hole

/-- The 21 named hypotheses that name no claim. Each field's type is the definition of that name. -/
structure Core : Prop where
  wfKnow      : Hole.wfKnow d
  linOffKnow  : Hole.linOffKnow d
  linkKnow    : Hole.linkKnow d
  reqKnow     : Hole.reqKnow d
  linOnKnow   : Hole.linOnKnow d
  passes      : Hole.passes d
  copy        : Hole.copy d
  wfLocal     : Hole.wfLocal d
  linOffLocal : Hole.linOffLocal d
  linkLocal   : Hole.linkLocal d
  reqLocal    : Hole.reqLocal d
  linOnLocal  : Hole.linOnLocal d
  coherent    : Hole.coherent d
  samplersT   : Hole.samplersT d
  samplersL   : Hole.samplersL d
  samplersB   : Hole.samplersB d
  below       : Hole.below d
  seedLaw     : Hole.seedLaw d
  wires       : Hole.wires d
  recordCode  : Hole.recordCode d
  commitment  : Hole.commitment d

/-- The 22 named hypotheses: `Core d` and the meaning at "the output tokens are the model's". -/
structure Holes : Prop extends Core d where
  sound : Hole.sound d

/-- The description one floor lower. -/
def ProtocolDescription.toAt (d : ProtocolDescription) : DescriptionAt where
  I := d.C.I
  X := d.C.X
  L := d.L
  Wn := d.C.Cells
  Rno := d.C.Rno
  W := d.W
  Sd := d.Sd
  p := d.p
  m := d.m
  enc := d.enc
  ext := d.ext
  εId := d.εId
  build := d.build
  nextToken := d.nextToken
  ISK := d.ISK
  commit := d.commit
  prove := d.prove
  bound := d.bound
  π₀ := d.π₀
  x₀ := d.x₀
  εs := d.κs * d.κ

theorem systemOf_eq_at : systemOf d = systemAt d.toAt := rfl

theorem extractorOf_eq_at : extractorOf d = extractorAt d.toAt := rfl

theorem soundnessErrorOf_eq_at : soundnessErrorOf d = soundnessErrorAt d.toAt := rfl

/-- The hypotheses here give those of Johnson/Top/OnFilesAt.lean: the five hypotheses on knowledge
soundness, with the samplers and the numbers, give the soundness of the three files' protocols at
the passed object. -/
theorem Core.toAt {d : ProtocolDescription} (h : Core d) : CoreAt d.toAt :=
  let ⟨_, gdT⟩ := h.samplersT
  let ⟨_, gdL⟩ := h.samplersL
  let ⟨_, gdB⟩ := h.samplersB
  let hS := ((rec_soundAt_ofK d.C d.S d.P _ (fun _ => Prob.cnt_le_card _)
    ⟨h.wfKnow, h.linOffKnow, h.linkKnow, h.reqKnow, h.linOnKnow⟩ h.passes h.copy).pull
      gdT.fib gdL.fib gdB.fib).grind d.Nn (d.g.TR.pull _) (d.g.LR.pull _) (d.g.BR.pull _)
  { noneColl := hS.noneColl
    keySound := ⟨_, (Err.below_grind_iff _ _ _).2 (Err.BelowG.pull gdT
      ((belowG_app _ _ d.g.wf d.g.linOff d.P.wf.err d.P.linOff.err d.κ).2
        ⟨h.below.wf, h.below.linOff⟩)), hS.sndT⟩
    entrySound := ⟨_, (Err.below_grind_iff _ _ _).2 (Err.BelowG.pull gdL h.below.link), hS.sndL⟩
    proofSound := ⟨fun b y τ => d.S.wit b y (Tr.push d.σB (Tr.strip (d.g.BR.pull d.σB) τ)), _,
      (Err.below_grind_iff _ _ _).2 (Err.BelowG.pull gdB
      ((belowG_app _ _ d.g.req d.g.linOn d.P.req.err d.P.linOn.err d.κ).2
        ⟨h.below.req, h.below.linOn⟩)), hS.sndB⟩
    late := rfl
    keyLocal := ((Iop.isLocal_toProto _ _ _
      (Iop.isLocal_seq _ _ _ _ _ _ _ _ h.wfLocal h.linOffLocal)).pull d.σT).grind _
    entryLocal := ((Iop.isLocal_toProto _ _ _ h.linkLocal).pull d.σL).grind _
    proofLocal := ((Iop.isLocal_toProto _ _ _
      (Iop.isLocal_seq _ _ _ _ _ _ _ _ h.reqLocal h.linOnLocal)).pull d.σB).grind _
    coherent := BatchGrind.coherent_grind _ (BatchPull.coherent_pull d.σB (RoundSplits.app_coherent
      (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _)
      h.coherent))
    seedLaw := h.seedLaw
    wires := h.wires
    recordCode := h.recordCode
    commitment := h.commitment }

/-- Index binding of `scheme d`, for the language of the relaxed relation, from the hypotheses on
the sub-protocols, numbers, wires and record. -/
theorem Core.binds {d : ProtocolDescription} (h : Core d) :
    ZKCP.Gen.HasIndexBindingWith (relPair (IsTrue d) (IsTrue d) fun _ _ hw => hw)
      (scheme d) (indexExtractorAtRootAndOutOfDomainSample d.W) (epsC d.W (d.κs * d.κ)) :=
  h.toAt.binds

/-- Under 22 hypotheses, the 21 of `Core d` and `Hole.soundFor d claim` (hypotheses of the theorem:
Lean's list of axioms does not show them): soundness of `verify d` for the claim, with the extractor
named, for every description d. It is `verify_sound_at_for` (Johnson/Top/OnFilesAt.lean) at
`d.toAt`. -/
theorem verify_sound_for (claim : d.C.I → List Token → List Token → Prop) (h : Core d)
    (hs : Hole.soundFor d claim) :
    SoundForWith (systemOf d) (extractorOf d) claim (soundnessErrorOf d) :=
  verify_sound_at_for d.toAt claim h.toAt hs

/-- Under the 22 named hypotheses `Holes d` (hypotheses of the theorem: Lean's list of axioms does
not show them), for every description d: for every committer and every prover with at most t
queries to the hash function together, the probability that `verify d` accepts while the extractor
gives no index, or an index at which the output tokens are not the model's, is at most
`soundnessErrorOf d t`. -/
theorem verify_sound (h : Holes d) :
    SoundForWith (systemOf d) (extractorOf d) (systemOf d).IsModelOutput (soundnessErrorOf d) :=
  verify_sound_for d _ h.toCore h.sound

theorem Holes.toAt {d : ProtocolDescription} (h : Holes d) : HolesAt d.toAt :=
  { h.toCore.toAt with sound := h.sound }

/-- What `verify d` is. -/
example : verify d = fun commitment prompt output proof =>
    deterministicOf
      ((Rec.tokenScheme (schemeOverOneHashFunction d.m (scheme d)) d.enc d.bound d.build d.π₀).V commitment
        (prompt, output) proof) :=
  rfl

/-- The scheme's verifier is the compiled verifier with a record, at the key made whole from the
root, the record and what the proof brings. -/
example (k : KeyRoot 256 d.L) (x : d.C.X) (π : PrfRoot 256 d.L) :
    (scheme d).V k x π = VC d.W d.Sd d.p ⟨k.cm, k.rcd, π.piT, [π.link]⟩ x ⟨0, π.piB⟩ := rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.verify_sound_for
#print axioms VerifiableInference.OnPublicFiles.verify_sound
