-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/OnFilesAt.lean: soundness of the argument system that the compiler with a record makes
from an object with records, for every such object, under named hypotheses on its three protocols.

Definitions, two structures of hypotheses, and four theorems with their proofs. This is the form
of Johnson/Top/OnFiles.lean one floor lower: the description holds the object `L : HolographicProtocol I X` that the
compiler reads as a field, not the configuration, sub-protocols, samplers and bits of work from
which Johnson/Top/OnFiles.lean makes it. The hypotheses on soundness are three, one for each file.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `DescriptionAt`: the object; the relaxed relation; the wires; the coding of the typed oracles in
    one hash function; the code of a key; the extractor behind the commitment and its stated cost;
    how an instance is built; the model; the honest committer and prover; one stated number.
  `schemeAt a`, `systemAt a`, `verifyAt a`, `extractorAt a`, `soundnessErrorAt a`: as `scheme`,
    `systemOf`, `verify`, `extractorOf`, `soundnessErrorOf` in Johnson/Top/OnFiles.lean.
  `HoleAt.‹name› a`: the named hypotheses, one definition each, with one sentence each.
  `CoreAt a`: the 13 hypotheses that name no claim. `HolesAt a`: these and `HoleAt.sound a`.
  `CoreAt.binds`: index binding of `schemeAt a`.
  `verify_sound_at_for`, `verify_sound_at`: `SoundForWith` for a claim; for "the output tokens are
    the model's".
Limits: those of Johnson/Top/OnFiles.lean, read at `a`. No object is given here, and none is shown
  to meet `HolesAt a`. No hypothesis says that εs is small. No hypothesis says that `verifyAt a`
  accepts anything. `a.m`, `a.W` and `a.L` hold laws and instances in their types. The hash function
  is one random function with 256-bit answers.
  `HoleAt.wires` asks that in every round uniform hash answers give an EXACTLY uniform verifier
  message. By a count (no theorem here), no map does that where the number of a round's messages
  does not divide the number of hash answers, a power of two; so at an object with a round that
  draws, say, an element of a field of odd size, `HolesAt a` cannot be met and the theorems are
  empty. An object whose rounds have blocks of digests for messages can meet it: such is the
  passed object of Johnson/Top/OnFiles.lean, where the samplers' bias is paid in κs.
  No field names bits of proof of work: the three hypotheses on soundness bound every round's error
  of the object as it stands, so where an error is small only with its work counted, the object's
  rounds must hold that work (nonce and test).
  If `build` itself refuses every output that is not the model's, `HoleAt.sound` holds whatever the
  relation is, and the theorems say nothing on the protocol.
  Does not say: completeness; zero knowledge; that the extractor returns an honest committer's
  index.

-/
import Johnson.RecCompile.FrontRoot
import Johnson.Top.FrontCommit
import Johnson.Top.BlocksOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Iop Compile Compile.Batch Compile.Batch.Cms

/-- What `verifyAt` reads, what the hypotheses speak of, the honest side's algorithms, and the
stated numbers. -/
structure DescriptionAt where
  /-- Indices. -/
  I : Type
  /-- Instances. -/
  X : Type
  /-- The object with records: three protocols (key file, entry file, proof file), the encoder and
  decoder of an index, the record. -/
  L : HolographicProtocol I X
  /-- Witnesses. `verifyAt` does not read them; the hypotheses do. -/
  Wn : Type
  /-- The relaxed relation. `verifyAt` does not read it; the hypotheses do. -/
  Rno : I → X → Wn → Prop
  /-- The wire of the object: how rounds and openings are laid into hash queries. -/
  W : QueryLayout 256 L.carrierC
  /-- The wire of the record. -/
  Sd : OutOfDomainSampleQueryLayout 256 W.K L
  p : Params
  /-- The typed oracles in one hash function. -/
  m : OracleCoding (spec 256 W.K L.carrierC) 256
  /-- The code of a key: the hash function's answer at it is the commitment. -/
  enc : KeyRoot 256 L → Option ZKCP.Str
  /-- The extractor behind the commitment. For the index it reads the commitment and the
  committer's query log. `verifyAt` does not read it; the theorems name it. -/
  ext : ZKCP.Extractor 256 I X Unit (ZKCP.Digest 256) (KeyRoot 256 L × PrfRoot 256 L)
  /-- The stated cost of the commitment, in the sum of the two bounds on queries. -/
  εId : ℕ → ℝ≥0∞
  /-- From a prompt with output tokens, and further tokens that the proof brings, an instance. -/
  build : List Token × List Token → List Token → Option X
  /-- The model. `verifyAt` does not read it; the claim does. -/
  nextToken : I → List Token → Option Token
  /-- The honest side. Nothing is asked of these six, nor of the honest provers that `L` holds. -/
  ISK : Type
  commit : I → Rom.OComp (spec 256 W.K L.carrierC) (KeyRoot 256 L × ISK)
  prove : ISK → (b : List (X × Unit)) →
    Rom.OComp (spec 256 W.K L.carrierC) (ZKCP.Gen.Slots (PrfRoot 256 L) b)
  bound : ℕ
  π₀ : KeyRoot 256 L × PrfRoot 256 L
  x₀ : X
  /-- The stated bound on a round's error. -/
  εs : ℝ≥0∞

variable (a : DescriptionAt)

/-- The scheme. Its verifier is the compiled verifier with a record, the key being the root and the
record. -/
def schemeAt : ZKCP.Gen.Arg (spec 256 a.W.K a.L.carrierC) a.I a.X Unit (KeyRoot 256 a.L) a.ISK
    (PrfRoot 256 a.L) :=
  ⟨a.commit, a.prove, VR a.W a.Sd a.p⟩

/-- The argument system made from the description. -/
def systemAt : ArgumentSystem :=
  Rec.tokenArgumentSystem (schemeOverOneHashFunction a.m (schemeAt a)) a.enc a.bound a.build a.π₀ a.nextToken

/-- The verifier. -/
def verifyAt := (systemAt a).verify

/-- The named extractor. It reads the commitment and the committer's query log alone. -/
def extractorAt : Commitment → QueryLog → Option a.I :=
  (a.ext.buildInstance : ZKCP.Extractor 256 a.I (List Token × List Token) Unit (ZKCP.Digest 256)
    (List Token × (KeyRoot 256 a.L × PrfRoot 256 a.L))).Ei

/-- The bound, in t, the sum of the bounds on the committer's and the prover's queries to the hash
function: (t + tVC + 1) · εs + 2 (t + tVC + 2)² / 2^256 + εId t, where tVC bounds the typed queries
of the compiled verifier. -/
def soundnessErrorAt : ℕ → ℝ≥0∞ :=
  fun t => epsC a.W a.εs t 0 + a.εId t

/-- An instance is true at an index: some witness meets the relaxed relation. -/
def IsTrueAt (i : a.I) (x : a.X) : Prop := ∃ w, a.Rno i x w

/-! ## The named hypotheses -/

namespace HoleAt

/-- The decoder gives no index at a word and a record at whose seed the word has a collision. -/
def noneColl : Prop := ∀ y (rec : a.L.Rec), a.L.hasCollisionAt y rec.1 → a.L.decodeIndex y rec = none
/-- Key file: its protocol is round-by-round sound, every round's error at most εs, for "the word
has a collision at the record's seed, or decodes with the record". -/
def keySound : Prop :=
  ∃ ε, Err.Below ε a.εs ∧ a.L.offline.Sound (fun rec y => a.L.hasCollisionAt y rec.1 ∨ a.L.decodeIndex y rec ≠ none) ε
/-- Entry file: its protocol is round-by-round sound, every round's error at most εs, for "the first
word does not decode, or the further word has a collision, or both decode to the same index". -/
def entrySound : Prop :=
  ∃ ε, Err.Below ε a.εs ∧ a.L.link.Sound
    (fun rr y =>
      a.L.decodeIndex y.1 rr.1 = none ∨ a.L.hasCollisionAt y.2 rr.2.1 ∨ a.L.decodeIndex y.2 rr.2 = a.L.decodeIndex y.1 rr.1) ε
/-- Proof file: for each record its protocol has round-by-round knowledge soundness in the form for
batches, every round's error at most εs, for the relaxed relation at the decoded index. -/
def proofSound : Prop :=
  ∃ (wit : a.X × a.L.Rec → (oneExternalString a.L.wordLength a.L.Symbol).Str → Tr a.L.onlineBatch.loc.shape → a.Wn) (ε : _),
    Err.Below ε a.εs ∧ ∀ rec, (a.L.batAt rec).SndBKT a.L.maxBatchSize a.L.early a.L.late
      (a.L.relB a.Rno rec) (fun x y τ => wit (x, rec) y τ) ε
/-- No part of an instance is named late. -/
def late : Prop := a.L.late = none
/-- The key file's verifier reads its oracles at the positions that it declares alone. -/
def keyLocal : Prop := a.L.offline.IsLocal
/-- The entry file's verifier reads its oracles at the declared positions alone. -/
def entryLocal : Prop := a.L.link.IsLocal
/-- The proof file's verifier reads its oracles at the declared positions alone. -/
def proofLocal : Prop := a.L.onlineBatch.loc.IsLocal
/-- The proof file's marks (which rounds a batch shares, which are a request's own) fit together
round by round. -/
def coherent : Prop := a.L.onlineBatch.ann.Coherent
/-- The record: for every word, the seed made from uniform digests is a seed at which that word has
a collision with probability at most εs. -/
def seedLaw : Prop := a.Sd.Law a.εs
/-- The layout (`QueryLayout.OKG`, `ProtocolQueryLayout.OKG`, `WireRB.OKG`, Iop/BatchWire.lean): every oracle position
has its own leaf in its tree and every used leaf a position; depths and the number of openings are
large enough; the number of slots is a power of two; and in every round the verifier's message is
made from hash answers so that uniform answers give an exactly uniform message (see the limits at
the head of this file: to meet this an object must have blocks of digests for messages). -/
def wires : Prop := a.W.OKG ∧ (wTC a.W).OKG ∧ (wLC a.W).OKG ∧ (wBC a.W).OKG
/-- The record: no two records are written as the same list of digests. -/
def recordCode : Prop := Function.Injective a.Sd.code
/-- The commitment: index binding of the compiled scheme, whose verifier holds the key itself, gives
index binding of the scheme whose verifier holds the hash function's answer at the key's code, with
the extractor `a.ext`, at the cost of `a.εId (tC + tP)`. Its premise follows from the other
hypotheses (`CoreAt.binds`), so under them it asserts its conclusion outright. If no two keys have
the same code it holds with the library's extractor at (tC + tP + 2)² / 2^256
(`commitment_of_code`). A code that leaves the record's seed out is not of that kind. For such a
code this library has no proof, which does not say that there is none: the index-binding game's
extractor sees the commitment and the committer's query log and has no access to the hash function,
so it cannot compute a seed that the committer never asked for. What would give a proof there: an
extractor that needs no seed, or a game whose extractor may query the hash function.
Johnson/Top/GameO.lean defines such a game (`ZKCP.HasIndexBindingWithO`); a bound in it is no proof
of this hypothesis. The format's commitment ID holds the record's seed (`Fmt.publishedBytes`,
Fmt/Rules4.lean). At this file's type of key this library has no code with the seed; at that of
Johnson/Top/InnerCompiledVerifier.lean it has one, which is of that kind if the two spellings are one to one
(`idCodeSeed_oneToOne`, Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean). -/
def commitment : Prop :=
  ZKCP.HasIndexBindingWith (ZKCP.languageRelation (IsTrueAt a))
      (SpecialAny.oneOf (schemeOverOneHashFunction a.m (schemeAt a)))
      (Special.extOf (extractorOverOneHashFunction a.m (indexExtractorAtRootAndOutOfDomainSample a.W))) (epsC a.W a.εs) →
    ZKCP.HasIndexBindingWith (ZKCP.languageRelation (IsTrueAt a))
      ((SpecialAny.oneOf (schemeOverOneHashFunction a.m (schemeAt a))).digestKey a.enc) a.ext
      fun tC tP => epsC a.W a.εs tC tP + a.εId (tC + tP)
/-- The meaning, for a claim: if an instance is built from a prompt with output tokens and is true
at an index (some witness meets the RELAXED relation), then the claim holds at that index of the
prompt and the output tokens. -/
def soundFor (claim : a.I → List Token → List Token → Prop) : Prop :=
  ∀ i (x' : List Token × List Token) b x, a.build x' b = some x → IsTrueAt a i x → claim i x'.1 x'.2
/-- The meaning: `soundFor` at the claim "the output tokens are the model's". -/
def sound : Prop := soundFor a (systemAt a).IsModelOutput

/-- A code under which no two keys agree gives `commitment`, at the library's extractor and cost. -/
theorem commitment_of_code (h : ZKCP.CodeIsOneToOne a.enc)
    (he : a.ext = (Special.extOf (extractorOverOneHashFunction a.m (indexExtractorAtRootAndOutOfDomainSample a.W))).digestKey a.enc)
    (hε : ∀ t, a.εId t = (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) : commitment a := by
  intro hb tC tP St Ct Pt hC hP
  rw [he]
  show _ ≤ epsC a.W a.εs tC tP + a.εId (tC + tP)
  rw [hε]
  exact hb.digestKey h tC tP St Ct Pt hC hP

end HoleAt

/-- The 13 named hypotheses that name no claim. Each field's type is the definition of that name. -/
structure CoreAt : Prop where
  noneColl   : HoleAt.noneColl a
  keySound   : HoleAt.keySound a
  entrySound : HoleAt.entrySound a
  proofSound : HoleAt.proofSound a
  late       : HoleAt.late a
  keyLocal   : HoleAt.keyLocal a
  entryLocal : HoleAt.entryLocal a
  proofLocal : HoleAt.proofLocal a
  coherent   : HoleAt.coherent a
  seedLaw    : HoleAt.seedLaw a
  wires      : HoleAt.wires a
  recordCode : HoleAt.recordCode a
  commitment : HoleAt.commitment a

/-- The 14 named hypotheses: `CoreAt a` and the meaning at "the output tokens are the model's". -/
structure HolesAt : Prop extends CoreAt a where
  sound : HoleAt.sound a

/-- Index binding of `schemeAt a`, for the language of the relaxed relation. Two premises of
`cmsR_binding_at` are met on the spot, since its conclusion does not read them: the count of seeds
at which a word has a collision, at the number of all seeds; the exact relation, taken to be the
relaxed one. -/
theorem CoreAt.binds {a : DescriptionAt} (h : CoreAt a) :
    ZKCP.Gen.HasIndexBindingWith (relPair (IsTrueAt a) (IsTrueAt a) fun _ _ hw => hw)
      (schemeAt a) (indexExtractorAtRootAndOutOfDomainSample a.W) (epsC a.W a.εs) :=
  let ⟨_, bT, sT⟩ := h.keySound
  let ⟨_, bL, sL⟩ := h.entrySound
  let ⟨_, _, bB, sB⟩ := h.proofSound
  cmsR_binding_at a.W a.Sd a.p a.Rno a.Rno _ (Fintype.card a.L.OutOfDomainSeed) _ _ _ a.εs _
    ⟨h.noneColl, fun _ => Prob.cnt_le_card _, sT, sL, sB⟩ h.seedLaw bT bL bB h.late h.keyLocal
    h.entryLocal h.proofLocal h.coherent
    ⟨h.wires.1, h.wires.2.1, h.wires.2.2.1, h.wires.2.2.2, ⟨h.recordCode⟩⟩
    (schemeAt a) rfl

/-- Under 14 hypotheses, the 13 of `CoreAt a` and `HoleAt.soundFor a claim` (hypotheses of the
theorem: Lean's list of axioms does not show them): soundness of `verifyAt a` for the claim, with
the extractor named, for every description a. The steps from index binding on are
`Rec.soundForWith_systemE_ext` (Johnson/Top/FrontCommit.lean). -/
theorem verify_sound_at_for (claim : a.I → List Token → List Token → Prop) (h : CoreAt a)
    (hs : HoleAt.soundFor a claim) :
    SoundForWith (systemAt a) (extractorAt a) claim (soundnessErrorAt a) :=
  Rec.soundForWith_systemE_ext (schemeOverOneHashFunction a.m (schemeAt a)) (extractorOverOneHashFunction a.m (indexExtractorAtRootAndOutOfDomainSample a.W)) a.enc
    a.ext a.bound a.π₀ a.nextToken
    (bindingR_one a.W a.m (blocks_leaf a.m (by norm_num)) (blocks_node a.m (by norm_num))
      (ZKCP.Special.toPair (ZKCP.languageRelation (IsTrueAt a))) (schemeAt a) _
      (fun tC tP St Ct Pt hC hP => h.binds tC tP St Ct Pt hC hP))
    (fun k x π => noCoin_overOne a.m _ (noCoin_of_detBound _ _ (detBound_VR a.W a.Sd a.p k x π)))
    h.commitment claim a.x₀ hs
    (fun tC tP => le_of_eq (congrArg (fun e => e + a.εId (tC + tP))
      (Rec.epsC_sum a.W a.εs tC tP)))

/-- Under the 14 named hypotheses `HolesAt a` (hypotheses of the theorem: Lean's list of axioms does
not show them), for every description a: for every committer and every prover with at most t queries
to the hash function together, the probability that `verifyAt a` accepts while the extractor gives
no index, or an index at which the output tokens are not the model's, is at most
`soundnessErrorAt a t`. -/
theorem verify_sound_at (h : HolesAt a) :
    SoundForWith (systemAt a) (extractorAt a) (systemAt a).IsModelOutput (soundnessErrorAt a) :=
  verify_sound_at_for a _ h.toCoreAt h.sound

/-- The scheme's verifier is the compiled verifier with a record, at the key made whole from the
root, the record and what the proof brings. -/
example (k : KeyRoot 256 a.L) (x : a.X) (π : PrfRoot 256 a.L) :
    (schemeAt a).V k x π = VC a.W a.Sd a.p ⟨k.cm, k.rcd, π.piT, [π.link]⟩ x ⟨0, π.piB⟩ := rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.verify_sound_at_for
#print axioms VerifiableInference.OnPublicFiles.verify_sound_at
