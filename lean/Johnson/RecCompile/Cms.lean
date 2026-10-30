-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Cms.lean: A COMPILED VERIFIER FOR AN OBJECT
WITH RECORDS (Iop.HolographicProtocol, Hiop/RecInterface.lean) IN WHICH NO TYPE OF THE LIBRARY's COMPILER IS TURNED.
Definitions and statements. The proofs: CmsBcs.lean, CmsGlue.lean.

The design (the one that the heads of CompileK/RecScheme.lean and RecBindSpec.lean tell as
the text's): the seed of a record is the answer to a query of its own on the root alone; every
chain's first query holds the record(s) beside the root(s); so does a session's SHARED query; the
key holds (root, seed, answer);
the verifier asks the seed's query again and compares.
How it is rendered with the library's terms as they stand:
  the seed's query: to the Fiat-Shamir oracle fb t, of the format (round 1, head f1 [cm] none [], no
    root, a fixed
    plain part): no chain of the library asks such a query (a head f1 stands in round 0 only:
    Compile/Batch/Rooted.lean, rooted, «_ + 1, .f1 _ _ _ => none»). No salt, no instance, no work. t
    = S.t0 for the first encoded index, t = S.t1 for further ones: two letters of the record's wire
    (binding holds for every pair, equal ones too: OutOfDomainSampleQueryLayout.Tags, S.t0 ≠ S.t1, is asked by no proof of
    it; which pair suits completeness is the honest side's matter: the library's lemmas want a
    chain's own oracle untouched when the chain starts). The seed is S.seed of the answer's K
    digests.
  Test, Link: the library's verifyOneProtocol on L.offline, L.link themselves (no rounds in front); the instance
    (the record; the two
    records) stands typed in the field x of the first query (f1).
  a session: verifyOneProtocol on L.onlineBatch, instance (x, record) in the field x of f1, AND the list of external
    roots
    handed to it is cm :: cm :: S.code record. The library writes that whole list into f1, f4 (the
    joining, shared query) and f5 (later shared queries); which places it reads as roots is the
    wire's matter (checksExt reads cms.getD (we.which p)), and under OKC these are place 0 (Test, a
    session) and places 0, 1 (Link), nothing behind; and it drops a slot from a shared query if the
    slot's list differs from the shared query's (slotFn, Rooted.lean). So slots with another record
    drop out as slots with another root do.
DECLARED. (1) S.code must be injective (one record in the list: no second reading). (2) Of S.seed
the statements ask what is used and no more (SeedLaw): for every word, the seed of K uniform digests
is a collision seed with probability at most εs. IT IS A PREMISE ON THE SAMPLER AND THE OBJECT
TOGETHER; with it the count eR of SoundAtR.rcd is idle in cms_bcs. It follows from rcd and a bound
on the fibres of S.seed (seedLaw_of_fibres, Wire.lean); at no object of ours is such a map written.
An exactly uniform S.seed has it (seedLaw_of_unif, CmsBcs.lean), but exists only if |OutOfDomainSeed| divides
2^(lam K); a sampler with a small bias can have it too. THE SAME VACUITY ONE LEVEL UP IS NOT MENDED:
W.OKG asks an exactly uniform verifier message of every round (WireRB.OKG.chal_unif); the library
meets that by passing an object through its samplers (draws | pull), which are written for BatchProtocol; no
such pass exists for an HolographicProtocol. (3) late = none, as in RecBindSpec.lean. (4) No committer, no prover:
one clause (index binding), no completeness, no privacy. The clause with witnesses (cms_binding,
CmsGlue.lean) has a recomputing extractor and is no stronger than binding for the languages
(CompileK/Recompute.lean's head). (5) Typed oracles. (6) No proof of work on the seed's query, AND
THERE MUST BE NONE: a nonce there would give one root many seeds. εs knows no work. (7) The seed's
query lives in the oracle fb t, not in an oracle of its own name. (8) A root has one seed FOR EACH
ROLE (tag S.t0: first encoded index; tag S.t1: a further one). Binding stands if a root serves in
both; for hiding the honest side must never use one encoding in both roles (two records on one
encoding's pads): a condition on a committer that is not written here.

-/
import Johnson.RecCompile.Bcs
import Compile.Batch.GlueBinding

set_option autoImplicit false

noncomputable section

namespace Iop
variable {I X : Type}
namespace HolographicProtocol

/-- What the first query of a chain holds of an instance: Test: (none, rec, rec); Link: (none, first
record, further record); a session: (x, rec, rec). -/
abbrev XC (L : HolographicProtocol I X) : Type := Option X × L.Rec × L.Rec

/-- The carrier of the typed oracles: the object's own three shapes, annotation, alphabet. All else
is idle. -/
def carrierC (L : HolographicProtocol I X) : BatchProtocol I L.XC where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := fun _ => none
  offline := InteractiveOracleProof.hollow L.offline.shape
  link := InteractiveOracleProof.hollow L.link.shape
  maxBatchSize := L.maxBatchSize
  onlineBatch := ⟨InteractiveOracleProof.hollow L.onlineBatch.loc.shape, L.onlineBatch.ann⟩
  honestOfflineProver := { Coin := Unit, ext := fun w => L.encodeIndex w.1 w.2, strat := fun _ _ _ => Strat.dflt _ (),
                           Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun w => (L.encodeIndex w.1 w.2.1, L.encodeIndex w.1 w.2.2),
                        strat := fun _ _ _ => Strat.dflt _ (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w => L.encodeIndex w.1 w.2,
                               strat0 := fun _ _ => SStrat.hollow _ _, strat := fun _ _ _ _ => LStrat.hollow _ _,
                               Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := fun a => (a.1.map L.early, a.2)
  late := L.late

end HolographicProtocol
end Iop

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ}

/-- The wire of the record: the fixed plain part of a seed's query, how K digests give a seed, how a
record is written as a list of digests. -/
structure OutOfDomainSampleQueryLayout (lam K : ℕ) (L : HolographicProtocol I X) where
  /-- the tag of the Fiat-Shamir oracle that gives the seed of the first encoded index -/
  t0 : Tag
  /-- the same for further encoded indices -/
  t1 : Tag
  pl : (t : Tag) → PlainPart (shapeOf L.carrierC t) (annOf L.carrierC t)
  seed : (Fin K → Dig lam) → L.OutOfDomainSeed
  code : L.Rec → List (Dig lam)
  /-- equality of seeds, as data: the verifier compares two seeds -/
  decS : DecidableEq L.OutOfDomainSeed

structure OutOfDomainSampleQueryLayout.OK {K : ℕ} {L : HolographicProtocol I X} (S : OutOfDomainSampleQueryLayout lam K L) : Prop where
  inj : Function.Injective S.code

/-- One role, one tag. No proof of index binding asks it. -/
def OutOfDomainSampleQueryLayout.Tags {K : ℕ} {L : HolographicProtocol I X} (S : OutOfDomainSampleQueryLayout lam K L) : Prop := S.t0 ≠ S.t1

/-- What is used of the map from digests to seeds: for every word, the seed of K uniform digests is
a collision seed with probability at most εs. -/
def OutOfDomainSampleQueryLayout.Law {K : ℕ} {L : HolographicProtocol I X} (S : OutOfDomainSampleQueryLayout lam K L) (εs : ℝ≥0∞) : Prop :=
  ∀ y, pr (unif (Fin K → Dig lam)) {a | L.hasCollisionAt y (S.seed a)} ≤ εs

/-- The key. -/
structure FullKey (lam : ℕ) (L : HolographicProtocol I X) where
  cm : Dig lam
  rcd : L.Rec
  piT : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))
  links : List (Dig lam × L.Rec × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))

/-- A proof. -/
structure RequestProof (lam : ℕ) (L : HolographicProtocol I X) where
  leaf : ℕ
  piB : Option (OneProtocolProof lam L.onlineBatch)

variable {L : HolographicProtocol I X} (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)

def wTC : ProtocolQueryLayout lam W.K (BatchInteractiveOracleProof.ofProto L.offline) :=
  ⟨W.T.sh, W.T.ext, W.T.decO, W.T.nOpen, W.T.maxDepth⟩
def wLC : ProtocolQueryLayout lam W.K (BatchInteractiveOracleProof.ofProto L.link) :=
  ⟨W.Lk.sh, W.Lk.ext, W.Lk.decO, W.Lk.nOpen, W.Lk.maxDepth⟩
def wBC : ProtocolQueryLayout lam W.K L.onlineBatch := ⟨W.B.sh, W.B.ext, W.B.decO, W.B.nOpen, W.B.maxDepth⟩

/-- The seed's query: the root alone. -/
def seedQ (t : Tag) (cm : Dig lam) : FbIn lam L.carrierC t := ⟨1, .f1 [cm] none [], none, S.pl t⟩

/-- the list that a session's chain is handed: the root (twice: places 0 and 1 are read as roots),
then the record -/
def cmsB (cm : Dig lam) (rec : L.Rec) : List (Dig lam) := cm :: cm :: S.code rec

def xinT (r : L.Rec) : Option L.XC := some (none, r, r)
def xinL (rr : L.Rec × L.Rec) : Option L.XC := some (none, rr.1, rr.2)
def xinB (a : X × L.Rec) : Option L.XC := some (some a.1, a.2, a.2)

/-- ask the seed's query at the root cm; is its seed s? -/
def seedIs (t : Tag) (cm : Dig lam) (s : L.OutOfDomainSeed) : TypedOracleComputation lam W.K L.carrierC Bool :=
  (OComp.ask (S := spec lam W.K L.carrierC) (OracleName.fb t) (seedQ W S t cm)).bind fun a =>
    OComp.pure (@decide _ (S.decS (S.seed (show FsAns lam W.K from a).1) s))

def vTC (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    TypedOracleComputation lam W.K L.carrierC Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (wTC W)
    (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id xinT (fun s => some (.inl s)) W.depthReq [cm] rec π

def vLC (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) : TypedOracleComputation lam W.K L.carrierC Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (wLC W)
    (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id xinL (fun s => some (.inl s)) W.depthReq [cm, cm']
    (rec, rec') π

def vBC (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K L.carrierC Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.onl L.onlineBatch (wBC W) (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id xinB
    (fun s => some (.inl s)) W.depthReq (cmsB W S cm rec) (x, rec) π

/-- The verifier: the two seeds' queries, the three compiled verifiers, all run, then the
conjunction. -/
def VC (p : Params) (v : FullKey lam L) (x : X) (π : RequestProof lam L) : TypedOracleComputation lam W.K L.carrierC Bool :=
  match v.piT, v.links[π.leaf]?, π.piB with
  | some πT, some (cmj, recj, some πL), some πB =>
      (seedIs W S S.t0 v.cm v.rcd.1).bind fun s0 =>
      (seedIs W S S.t1 cmj recj.1).bind fun sj =>
      (vTC W p v.cm v.rcd πT).bind fun a =>
      (vLC W p v.cm cmj v.rcd recj πL).bind fun b =>
      (vBC W S p cmj x recj πB).bind fun c =>
      OComp.pure (s0 && sj && a && b && c)
  | _, _, _ => OComp.pure false

/-- The index extractor: the index decoder on (what the committer's trace determines under the first
root, the key's first record). -/
def extractorC0 :
    ZKCP.Gen.Extractor (spec lam W.K L.carrierC) I X Unit (FullKey lam L) (RequestProof lam L) where
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
def vTC' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    TypedOracleComputation lam W.K L.carrierC Bool :=
  verifyB Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (wTC W)
    (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id xinT (fun s => some (.inl s)) W.depthReq [cm] rec π
def vLC' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    TypedOracleComputation lam W.K L.carrierC Bool :=
  verifyB Tag.link (BatchInteractiveOracleProof.ofProto L.link) (wLC W)
    (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id xinL (fun s => some (.inl s)) W.depthReq [cm, cm']
    (rec, rec') π
def vBC' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) : TypedOracleComputation lam W.K L.carrierC Bool :=
  verifyB Tag.onl L.onlineBatch (wBC W) (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id xinB
    (fun s => some (.inl s)) W.depthReq (cmsB W S cm rec) (x, rec) π

/-- a bound on the number of queries of VC on one proof -/
def tVC : ℕ :=
  2 + (tVQB (wTC W) W.depthReq + tVQB (wLC W) W.depthReq + tVQB (wBC W) W.depthReq)

def epsC (εs : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVC W + 1 : ℕ) : ℝ≥0∞) * εs + 2 * ((tC + tP + tVC W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- What holds outside a rare event, on traces that hold the verifier's queries. -/
def BcsAtC (Rt : I → X → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L.carrierC β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    -- the seed that a root's own query gives is no collision seed of the word under that root
    (∀ tr t cm (a : FsAns lam W.K), ¬ Bad tr → fbE t (seedQ W S t cm) a ∈ tr →
      ¬ L.hasCollisionAt (extEnc W tr cm) (S.seed a.1)) ∧
    -- the word under a root is fixed when the root's seed is drawn
    (∀ tr tr' t cm (a : FsAns lam W.K), ¬ Bad (tr ++ tr') → fbE t (seedQ W S t cm) a ∈ tr →
      extEnc W tr cm = extEnc W (tr ++ tr') cm) ∧
    (∀ tr cm rec π, ¬ Bad tr → RunsIn tr (vTC' W cm rec π) true →
      L.hasCollisionAt (extEnc W tr cm) rec.1 ∨ L.decodeIndex (extEnc W tr cm) rec ≠ none) ∧
    (∀ tr cm cm' rec rec' π, ¬ Bad tr → RunsIn tr (vLC' W cm cm' rec rec' π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) ∧
    (∀ tr cm x rec π, ¬ Bad tr → RunsIn tr (vBC' W S cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)

namespace Spec

/-- Outside a rare event, FROM SoundAtR ALONE (one record in all slots): no law RecShared, no
premise on mixed records. -/
def cms_bcs : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : HolographicProtocol I X) (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)
      (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞),
    L.SoundAtR Rno wit eR εT εL εB → S.Law εs → Err.Below εT εs → Err.Below εL εs →
    Err.Below εB εs → L.late = none → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → OKC W S → BcsAtC W S (fun i x => ∃ w, Rno i x w) εs

/-- Index binding for the languages, for every scheme whose verifier is VC, from SoundR. -/
def cms_binding_lang : Prop :=
  ∀ (I X Wn ISK : Type) (lam : ℕ) (L : HolographicProtocol I X) (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)
      (p : Params) (Ryes Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞)
      (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w),
    L.SoundR Rno wit εs → S.Law εs → L.late = none → L.offline.IsLocal → L.link.IsLocal →
    L.onlineBatch.loc.IsLocal → L.onlineBatch.ann.Coherent → OKC W S →
    ∀ A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (FullKey lam L) ISK (RequestProof lam L),
      A.V = VC W S p →
      ZKCP.Gen.HasIndexBindingWith
        (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
        A (extractorC0 W) (epsC W εs)

end Spec
end Compile.Batch.Cms
