-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/RecBindSpec.lean: index binding of the compiled verifier for an object with records: the
statements. Definitions and statements (`Compile.Batch.Spec.rec_bcs`, `Spec.rec_binding_lang`,
`Spec.rec_binding`). **Statements only: nothing here is proved**.
Over the compiler's typed oracles.

The object: `Iop.HolographicProtocol` (Hiop/RecInterface.lean): after each encoded index a seed is drawn and
answered; (seed, answer) is its record; the index decoder reads (word, record). So the index may lie
beyond unique decoding of its code.
The verifier: `VR` of CompileK/RecScheme.lean, as it stands: the key holds the first root, its
record, the offline string, and for each further encoded index its root, its record, the link's
string; three compiled verifiers of the library's kind (`verifyOneProtocol`), on the offline IOP and the link
IOP with the two rounds of the record phase of their new encoded index in front (`InteractiveOracleProof.led`,
Hiop/RecLine.lean): the seed is the verifier message of the first round of that chain, so the answer
of its first, salted, query, which holds the root(s); the IOP's own verifier compares the key's
record with it; and a session on (x, record).
The extractors: `extractorR` of CompileK/RecScheme.lean. E_i: the index decoder on (what the
committer's trace determines under the first root, the key's first record). E_w recomputes: `re`
(the extracted index) x.

Main names:
  `W.OKR`: the laws of a wire: those of the library on the carrier of the typed oracles
    (`L.carrier a0`, CompileK/RecScheme.lean), and for each of the three protocols as it is run
    (numbers of openings).
  `tVR`, `epsR`: ε = (tC + tP + tVR + 1) εs + 2 (tC + tP + tVR + 2)² / 2^λ: the form of `epsB`
    (Compile/Batch/SpecBinding.lean). The record clause costs no term of its own: a collision seed
    is the bad event of the first round of a chain, one more round error, as a probability at most
    εs by `SoundR.rcd`.
  `BcsAtR Rt εs`: there is an event Bad on traces, of probability at most t εs + 2 (t + 1)² / 2^λ
    for an algorithm with at most t queries and kept when a trace goes on, such that outside it, on
    traces that hold the queries of `vOff'`, `vLink'`, `vBat'` and on which these accept (they are
    the library's `verifyB`: no strict format, and one path for each opening; `VR` runs `verifyOneProtocol`):
    offline: the decoder answers at the key's record; link: the first index does not decode, or the
    further index decodes, with its record, to the same index; session: its encoded index does not
    decode with its record, or `Rt i x` holds of the index i to which it decodes (in `Spec.rec_bcs`:
    x has a witness for i). Outside it, what a trace determines under an announced root does not
    change when the trace goes on.
  `Spec.rec_bcs`: `BcsAtR` from index binding of the object with explicit lists (`SoundAtR`) and
    (Snd-B) with a witness (`BatchInteractiveOracleProof.SndBKT`, Ior/KnowWide.lean) of a session on vectors with
    mixed records, under the further hypotheses of its statement (eR ≤ εs · |OutOfDomainSeed| for `SoundAtR`'s
    bound eR on the number of seeds with a collision; every error of the three lists, as a
    probability, at most εs (`Err.Below`); `L.late = none`; locality of the three protocols
    (`InteractiveOracleProof.IsLocal`); coherence of the session's annotation (`RoundSplits.Coherent`); `W.OKR`). Stated
    here, not proved here: no theorem of this file; the proof: Johnson/RecCompile/Bcs.lean.
  `Spec.rec_binding_lang`, `Spec.rec_binding`: index binding (`Gen.HasIndexBindingWith`,
    ZKCP/Gen.lean) at ε = `epsR W εs`, for every scheme whose verifier is `VR` (the clause reads the
    verifier alone): for the languages (extractor `extractorR0`: E_i alone); with witnesses and the
    recomputing extractor. Hypotheses: `sub` (`Ryes` lies in `Rno`: for the languages; witness by
    witness), `L.SoundR Rno wit εs`, locality, coherence, `W.OKR`, the two below; in
    `Spec.rec_binding` also: if x has a witness for i in `Rno`, then `re i x` is one. Of each of the
    two statements: Stated, not proved: no theorem of this library concludes it.

Hypotheses on the object beside `SoundR`, locality and coherence.
  `L.RecShared rd` (CompileK/RecScheme.lean): the shared plain part of a session's first shared
    round holds the record, and a slot's verifier accepts only if it is the slot's. Why: the
    library's first query of a shared chain has no field for an instance, so it holds no record;
    under one shared query a cheating prover can join chains from one root and different records,
    while `SoundR` speaks of one record in all slots. With the law the shared query holds the record
    (in its plain part). To be used through a lemma at the level of the IOP (one record in all slots
    + this law + coherence ⇒ vectors with mixed records, same errors), which is not part of this
    library.
  `L.late = none`: an instance is written into its chain at once. (With a late part the chain's
    rule, one for all three protocols, would write the first record a second time into a link's
    chain.)

Limits:
The design of the verifier that these statements speak of is not the technical report's, and
not the write-up's.
A write-up of ours (lean/CREDITS.md) settles it otherwise: the
seed of a record is the answer of a query of its own on the root alone (no salt; one oracle for the
first, one for further encoded indices); the chains come after it, and each chain's first query
holds the record(s) beside the root(s); the verifier recomputes the seed and compares it with the
key's. So these do not render the write-up's compilation: the record phase as the first two
rounds of the offline and of the link's chain; "the seed is the answer of the chain's first, salted
query"; "the offline chain's first query holds nothing of the record"; "the link's first query holds
the first record only". What is the write-up's: the key's fields; E_i with the key's
first record; the collision as the bad event of one more query, under the maximum; records known at
the start. The statements below remain statements on `VR` as CompileK/RecScheme.lean defines it.
Declared, against a print of the write-up's compilation
(a comparison by reading; the write-up is unrefereed and exists in several prints). (1) The record
in the shared chain: by a law of the object, not by a field
of the
query. (2) The answer's round has a chain query of its own, with error 0. (3) Which query gives the
seed of a further encoded index: here the first of the link's chain, which holds both roots and the
first record. (4) All that the head of CompileK/RecScheme.lean declares. On (1), in full: the law is
a condition on the object which the described protocol does not meet as written (the first shared
round of its test has no shared plain part): an instance has to add the record there; the proof
string then carries a copy of the record, unless a map on proofs takes it out; harmless for zero
knowledge (argued, not shown here: the record is public); that an honest answer at one seed tells
nothing of the index is a hypothesis (`ReadsR.hidE`, Hiop/RecInterface.lean), not shown here.
No committer and no prover: no completeness, no privacy: not the definition, one clause of it. Not
over one oracle. The witness clause with a recomputing extractor is no stronger than binding for the
language (CompileK/Recompute.lean). One pair (instance, proof) a run. No proof of work in these
statements (tests are added to protocols and wires before the terms are formed: `W.OKR` allows wires
with tests). This file says nothing on running times.

Terms: lean/GLOSSARY.md: index binding, encoded index, record, collision, index decoder, key,
offline IOP, link, session, slot, shared round, (Snd-B), trace, wire, typed oracle, chain query,
plain part, unique decoding, proof of work.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import CompileK.RecScheme
import Compile.Batch.SpecBinding

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} {a0 : L.OutOfDomainAnswer}

/-- The laws of a wire for an object with records. -/
structure _root_.Iop.QueryLayout.OKR (W : QueryLayout lam (L.carrier a0)) : Prop where
  base : W.OKG
  T    : (wOff W).OKG
  Lk   : (wLink W).OKG
  B    : (wBat W).OKG

variable (W : QueryLayout lam (L.carrier a0))

/-- the three compiled verifiers without the strict format (`verifyB`, where `VR` runs `verifyOneProtocol`):
objects of the analysis -/
def vOff' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto (L.offR a0))) :
    TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  verifyB Tag.test (BatchInteractiveOracleProof.ofProto (L.offR a0)) (wOff W)
    (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none)
    (fun s => some (.inl s)) W.depthReq [cm] rec π
def vLink' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto (L.linkR a0))) :
    TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  verifyB Tag.link (BatchInteractiveOracleProof.ofProto (L.linkR a0)) (wLink W)
    (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun rr => some (none, rr.1))
    (fun s => some (.inl s)) W.depthReq [cm, cm'] (rec, rec') π
def vBat' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  verifyB Tag.onl L.onlineBatch (wBat W) (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id xinR
    (fun s => some (.inl s)) W.depthReq [cm] (x, rec) π

/-- a bound on the number of queries of VR on one proof: `tVQB` of its three wires -/
def tVR : ℕ := tVQB (wOff W) W.depthReq + tVQB (wLink W) W.depthReq + tVQB (wBat W) W.depthReq

/-- ε, the bound of the two statements on index binding, as a function of tC and tP, the bounds on
the queries of the cheating committer and prover. -/
def epsR (εs : ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞ := fun tC tP =>
  ((tC + tP + tVR W + 1 : ℕ) : ℝ≥0∞) * εs + 2 * ((tC + tP + tVR W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- What holds outside a rare event, on traces that hold the verifier's queries. -/
def BcsAtR (Rt : I → X → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K (L.carrier a0) β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm rec π,
      ¬ Bad tr → RunsIn tr (vOff' W cm rec π) true → L.decodeIndex (extEnc W tr cm) rec ≠ none) ∧
    (∀ tr cm cm' rec rec' π, ¬ Bad tr → RunsIn tr (vLink' W cm cm' rec rec' π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) ∧
    (∀ tr cm x rec π, ¬ Bad tr → RunsIn tr (vBat' W cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)

namespace Spec

/-- Outside a rare event, from explicit lists. (not all hypotheses are named here: see the statement
below) Stated, not proved: no theorem of this library concludes it. -/
def rec_bcs : Prop :=
  ∀ (I X Wn : Type) (lam : ℕ) (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (W : QueryLayout lam (L.carrier a0))
      (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞),
    L.SoundAtR Rno wit eR εT εL εB →
    L.onlineBatch.SndBKT L.maxBatchSize (fun a => (L.early a.1, a.2)) L.late
      (fun a y w => L.relB Rno a.2 a.1 y w) wit εB →
    (eR : ℝ≥0∞) ≤ εs * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞) → Err.Below εT εs → Err.Below εL εs →
    Err.Below εB εs → L.late = none → L.offline.IsLocal → L.link.IsLocal → L.onlineBatch.loc.IsLocal →
    L.onlineBatch.ann.Coherent → W.OKR → BcsAtR W (fun i x => ∃ w, Rno i x w) εs

/-- Index binding for the languages, for every scheme whose verifier is VR. (not all hypotheses are
named here: see the statement below) Stated, not proved: no theorem of this library concludes it. -/
def rec_binding_lang : Prop :=
  ∀ (I X Wn ISK : Type) (lam : ℕ) (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (W : QueryLayout lam (L.carrier a0))
      (p : Params) (Ryes Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (rd : Plains L.onlineBatch.loc.shape → L.Rec) (εs : ℝ≥0∞)
      (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w),
    L.SoundR Rno wit εs → L.RecShared rd → L.late = none → L.offline.IsLocal → L.link.IsLocal →
    L.onlineBatch.loc.IsLocal → L.onlineBatch.ann.Coherent → W.OKR →
    ∀ A : Gen.Arg (spec lam W.K (L.carrier a0)) I X Unit (KeyR lam L a0) ISK (PrfR lam L), A.V =
        VR W p →
      Gen.HasIndexBindingWith (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
        A (extractorR0 W) (epsR W εs)

/-- Index binding with witnesses, the recomputing extractor. (not all hypotheses are named here: see
the statement below) Stated, not proved: no theorem of this library concludes it. -/
def rec_binding : Prop :=
  ∀ (I X Wn ISK : Type) (lam : ℕ) (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) (W : QueryLayout lam (L.carrier a0))
      (p : Params) (Ryes Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (rd : Plains L.onlineBatch.loc.shape → L.Rec) (re : I → X → Wn) (w0 : Wn) (εs : ℝ≥0∞)
      (sub : ∀ i x w, Ryes i x w → Rno i x w),
    L.SoundR Rno wit εs → L.RecShared rd → L.late = none → L.offline.IsLocal → L.link.IsLocal →
    L.onlineBatch.loc.IsLocal → L.onlineBatch.ann.Coherent → W.OKR → (∀ i x w, Rno i x w → Rno i x (re i x)) →
    ∀ A : Gen.Arg (spec lam W.K (L.carrier a0)) I X Unit (KeyR lam L a0) ISK (PrfR lam L), A.V =
        VR W p →
      Gen.HasIndexBindingWith (Gen.relPairW Ryes Rno sub) (Gen.withW Wn A)
        (extractorR W re w0) (epsR W εs)

end Spec
end Compile.Batch
