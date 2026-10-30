-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Cms.lean: the compiled verifier for an object with records (`Iop.HolographicProtocol`,
Hiop/RecInterface.lean), over the compiler's verifier side
(lean/OnBytes/TypedOracleCompiler/Compile/Batch/). Definitions and statements. The proofs: CmsBcs.lean,
CmsGlue.lean.

After lean/Johnson/RecCompile/Cms.lean, in that file's words. What differs:
  * the typed oracles' carrier holds what that file's `L.carrierC` holds of the verifier's side,
    nothing of the honest side (no index, no encoding), and three letters more: `Bd`, the type of
    the body of a leaf, and `aT`, `aL` (`typedOracleCarrier L Bd aT aL`, Carrier.lean);
  * a symbol is written into a leaf by the wire's own functions (`W.embT`, `W.embL`, `W.embB`,
    `W.embE`);
  * the wire has a list of trees for a component of a round;
  * the key's protocol may join: Test and Link stand with an annotation of their rounds as local or
    shared (`aT`, `aL`; `batTC L aT` = ⟨L.offline, aT⟩), two letters beside the object, whose type does
    not change. Where the kind of the rounds goes from local to shared and back, the compiler's
    chain seals the slot's chain into a request tree, opens the shared chain on that tree's root,
    and opens the last chain on both values: three hash chains in one file. At `RoundSplits.allLocal` it is
    that file's `BatchInteractiveOracleProof.ofProto`;
  * each of the three calls has its own depth of the request tree (`W.depthReqT`, `W.depthReqL`,
    `W.depthReq`). The errors of the shared rounds of Test and Link count once for each slot
    (`Err.timesShared`); at depth 0 that is once;
  * the seeds are meant to follow the programs (Seeds.lean of this folder): two nested queries at
    one tag, from the table's name; no role. The tie is the coding's matter: no Lean makes it. Two
    points hang on it: `S.cfg` and `S.shape` are one for all tables, which is right only if the two
    tables' names differ in the root alone; `S.pl1` is fixed, which is right only if the programs'
    round call for a seed holds no nonce;
  * the number of the stored copy is a field of a proof (`RequestProof.copy`, apart from `RequestProof.leaf`, the
    entry's place in the key's list), and it must stand in the session's proof string where the
    first query of its chain takes it in (`OutOfDomainSampleQueryLayout.num`, a letter: which place that is depends on the
    object);
  * the records of Test and Link stand in the first query's list, behind the root(s), as the
    session's does in that file: `cmsT` = root, then the record; `cmsL` = the two roots, then the
    two records. Their chains have no instance in the field x. So the round `L.late`, in which a
    chain takes in the whole instance, touches the session's chain alone;
  * `L.late = none` is not asked: the session's instance may come in two parts (`L.early` in the
    first query, the whole in the query of the round `L.late`), as in the library's own compiler.

Spelled otherwise than the programs spell it, by reading. None harms soundness (a one-to-one
coding can send the verifier's points to the format's strings); each falls to the coding:
  * a session's list holds the root twice (`cmsB`); `cmsT` shows that this is not needed;
  * a session's record stands three times in (F1) (the list, and twice in the field x), and again in
    the late query;
  * (F4) repeats the whole list, records included;
  * the front's commitment (the limits of Front.lean);
  * the record's code in the first query is one to one on the whole record, seed and answers
    (`S.OK.inj`, as `cms_bcs` opens it); the programs' first query holds the answers and recomputes
    the seed: the description departs here. A list that holds a code of the answers
    alone is not made here. It is made in CmsAns.lean and CmsAnsPr.lean of this folder for the
    whole verifier (`verifyAtFullKey`), and in LinkAns.lean and LinkAnsPr.lean for the link alone.

Limits: one clause, index binding. No committer, no prover, no completeness, nothing on hiding.
  * The oracles are typed.
  * `S.Law` is a premise on the sampler and the object together, and `eR` is idle.
  * `W.OKG` asks exactly uniform verifier messages from K digests, so it can hold only at an object
    that went through the pass `Iop.HolographicProtocol.pull`.
  * There is no proof of work on a seed's queries, and there must be none, or one root would have
    many seeds.
  * `S.num` is a letter under no law: no proof leans on its test, which can only make `VC` refuse
    more.
  * What shows that `OKC W S` and `S.Law` can be met: Wire.lean of this folder (`okc_wireOf`,
    `okc_passed`, `seedLaw_of_fibres`). What it does not show: no wire with two trees for a
    component; none at an annotation of Test or Link with shared rounds; and no `OutOfDomainSampleQueryLayout` with a code
    of one length: `S.OK.len` is met by nothing shown (the `exists_seedW` of
    lean/Johnson/RecCompile/SeedBS.lean has a code without a fixed length and does not carry over).
    So the theorems may be true and empty. That is said of `VC`. `verifyAtFullKey` (CmsAns.lean)
    asks no `S.OK`: its laws `OKA` ask `AnsOK` of the code of the answers in its place (one to one,
    one length), which no file of this folder meets at a code either.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.Bcs
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestSound
import OnBytes.TypedOracleCompiler.Compile.Batch.TVQB
import Johnson.TypedOracleCompiler.RecCompile.Seeds

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ}

/-- The key. -/
structure FullKey (lam : ℕ) (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape) where
  cm : Dig lam
  rcd : L.Rec
  piT : Option (OneProtocolProof lam (batTC L aT))
  links : List (Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL)))

/-- A proof. -/
structure RequestProof (lam : ℕ) (L : HolographicProtocol I X) where
  /-- the place of the entry in the key's list -/
  leaf : ℕ
  /-- the number of the stored copy, as the session's chain takes it in. The number tested is the
  prover's free choice, tied to the entry picked by nothing. -/
  copy : ℕ
  piB : Option (OneProtocolProof lam L.onlineBatch)

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

def wTC : ProtocolQueryLayout lam W.K (batTC L aT) :=
  ⟨W.T.sh, W.T.ext, W.T.decO, W.T.nOpen, W.T.maxDepth⟩
def wLC : ProtocolQueryLayout lam W.K (batLC L aL) :=
  ⟨W.Lk.sh, W.Lk.ext, W.Lk.decO, W.Lk.nOpen, W.Lk.maxDepth⟩
def wBC : ProtocolQueryLayout lam W.K L.onlineBatch := ⟨W.B.sh, W.B.ext, W.B.decO, W.B.nOpen, W.B.maxDepth⟩

/-- the list that a session's chain is handed: the root (twice: places 0 and 1 are read as roots),
then the record -/
def cmsB (cm : Dig lam) (rec : L.Rec) : List (Dig lam) := cm :: cm :: S.code rec

/-- the list that the key's chain is handed: the root, then the record -/
def cmsT (cm : Dig lam) (rec : L.Rec) : List (Dig lam) := cm :: S.code rec

/-- the list that a link's chain is handed: the two roots, then the two records -/
def cmsL (cm cm' : Dig lam) (rec rec' : L.Rec) : List (Dig lam) :=
  cm :: cm' :: (S.code rec ++ S.code rec')

def xinB (a : X × L.Rec) : Option L.XC := some (some a.1, a.2, a.2)

def vTC (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.test (batTC L aT) (wTC W)
    W.embT id (fun _ => none) W.embE W.depthReqT (cmsT W S cm rec) rec π

def vLC (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.link (batLC L aL) (wLC W)
    W.embL id (fun _ => none) W.embE W.depthReqL (cmsL W S cm cm' rec rec')
    (rec, rec') π

def vBC (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.onl L.onlineBatch (wBC W) W.embB id xinB
    W.embE W.depthReq (cmsB W S cm rec) (x, rec) π

/-- The verifier: the seeds of the two tables, the three compiled verifiers, all run, then the
conjunction, with the test `S.num` on the session's proof string and the proof's number of the
stored copy (`S.num`: a letter; no law). -/
def VC (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT
                                   aL) Bool :=
  match v.piT, v.links[π.leaf]?, π.piB with
  | some πT, some (cmj, recj, some πL), some πB =>
      (outOfDomainSeedIs W S v.cm v.rcd.1).bind fun s0 =>
      (outOfDomainSeedIs W S cmj recj.1).bind fun sj =>
      (vTC W S p v.cm v.rcd πT).bind fun a =>
      (vLC W S p v.cm cmj v.rcd recj πL).bind fun b =>
      (vBC W S p cmj x recj πB).bind fun c =>
      OComp.pure (S.num π.copy πB.plains && s0 && sj && a && b && c)
  | _, _, _ => OComp.pure false

/-- The index extractor: the index decoder on (what the committer's trace determines under the first
root, the key's first record). -/
def extractorC0 :
    ZKCP.Gen.Extractor (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) (RequestProof lam L)
        where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm) v.rcd
  Ew := fun _ _ _ _ _ => ()

/-- The laws of the wires. -/
structure OKC : Prop where
  base : W.OKG
  T    : (wTC W).OKG
  Lk   : (wLC W).OKG
  B    : (wBC W).OKG
  seed : S.OK

/-! the three compiled verifiers without the strict format: objects of the analysis -/
def vTC' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyB Tag.test (batTC L aT) (wTC W)
    W.embT id (fun _ => none) W.embE W.depthReqT (cmsT W S cm rec) rec π
def vLC' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyB Tag.link (batLC L aL) (wLC W)
    W.embL id (fun _ => none) W.embE W.depthReqL (cmsL W S cm cm' rec rec')
    (rec, rec') π
def vBC' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT
                                            aL) Bool :=
  verifyB Tag.onl L.onlineBatch (wBC W) W.embB id xinB
    W.embE W.depthReq (cmsB W S cm rec) (x, rec) π

/-- a bound on the number of queries of VC on one proof -/
def tVC : ℕ :=
  4 + (tVQB (wTC W) W.depthReqT + tVQB (wLC W) W.depthReqL + tVQB (wBC W) W.depthReq)

def epsC (εs : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVC W + 1 : ℕ) : ℝ≥0∞) * εs + 2 * ((tC + tP + tVC W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- What holds outside a rare event, on traces that hold the verifier's queries. -/
def BcsAtC (Rt : I → X → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    -- a seed that the verifier has recomputed at a root is no collision seed of the word under it
    (∀ tr cm s, ¬ Bad tr → RunsIn tr (outOfDomainSeedIs W S cm s) true → ¬ L.hasCollisionAt (extEnc W tr cm) s) ∧
    -- the word under a root is fixed when the first query of the root's seed is asked
    (∀ tr tr' cm (a : FsAns lam W.K), ¬ Bad (tr ++ tr') → fbE S.t (seedQ0 W S cm) a ∈ tr →
      extEnc W tr cm = extEnc W (tr ++ tr') cm) ∧
    (∀ tr cm rec π, ¬ Bad tr → RunsIn tr (vTC' W S cm rec π) true →
      L.hasCollisionAt (extEnc W tr cm) rec.1 ∨ L.decodeIndex (extEnc W tr cm) rec ≠ none) ∧
    (∀ tr cm cm' rec rec' π, ¬ Bad tr → RunsIn tr (vLC' W S cm cm' rec rec' π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) ∧
    (∀ tr cm x rec π, ¬ Bad tr → RunsIn tr (vBC' W S cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)

namespace Spec

/-- Outside a rare event, from SoundAtR alone (one record in all slots): no law RecShared, no
premise on mixed records. -/
def cms_bcs : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits
                                L.link.shape)
      (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞),
    L.SoundAtR Rno wit eR εT εL εB → S.Law εs →
    Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs →
    Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs →
    Err.Below εB εs → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    aT.Coherent → aL.Coherent → L.onlineBatch.ann.Coherent → OKC W S →
    BcsAtC W S (fun i x => ∃ w, Rno i x w) εs

/-- Index binding for the languages, for every scheme whose verifier is VC, from SoundR. -/
def cms_binding_lang : Prop :=
  ∀ (I X Wn ISK : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits
                                L.link.shape)
      (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (p : Params) (Ryes Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞)
      (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w),
    L.SoundR Rno wit εs → S.Law εs → L.offline.IsLocal → L.link.IsLocal →
    L.onlineBatch.loc.IsLocal → aT.Coherent → aL.Coherent → L.onlineBatch.ann.Coherent →
    W.depthReqT = 0 → W.depthReqL = 0 → OKC W S →
    ∀ A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) ISK (RequestProof
                                  lam L),
      A.V = VC W S p →
      ZKCP.Gen.HasIndexBindingWith
        (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
        A (extractorC0 W) (epsC W εs)

end Spec
end TypedOracleCompiler.Compile.Batch.Cms
