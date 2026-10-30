-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecInterface.lean: this file defines a kind of information-theoretic protocol (`HolographicProtocol`): a
holographic interactive oracle proof in which the party that encodes the index is not trusted; and
the properties that are asked of it.
In this library's words: the holographic IOP with an untrusted committer, with a record phase after
each encoded index (`HolographicProtocol`), and its properties.

Definitions and statements; the proofs of the statements are in Hiop/RecInterfaceProofs.lean.
No code, no distance, no field occurs here.

Why a record: beyond unique decoding a word has a list of codewords near it, and several of them may
hold good indices. A committer could then send one word and prove sessions for two indices. So right
after an encoded index is sent, and before any protocol reads it, the verifier draws a seed and the
prover answers. The pair (seed, answer) is the record of that encoded index.
But for a collision, an event of the seed alone, at most one member of the list agrees with the
record: the index decoder reads (word, record).

Main names:
  `HolographicProtocol`, the object: `Iop.BatchProtocol` of Iop/Batch.lean (dictionary: Hiop/Interface.lean), with these
    changes:
    `OutOfDomainSeed`, `OutOfDomainAnswer`, `honestOutOfDomainAnswer`: the record phase, abstract: the set of seeds; the set of answers; the
      honest answer, a function of (index, committer's randomness, seed). `L.Rec` = OutOfDomainSeed × OutOfDomainAnswer. It
      stands outside the three protocols: no round of `offline`, `link` or `onlineBatch` belongs to it. One
      record phase for each encoded index, the first and every further one alike.
    `hasCollisionAt y s`: the word y has a collision at the seed s: abstract, a property of (word, seed); no
      answer occurs in it.
    `decodeIndex y rec`: the index decoder reads the word and its record.
    `offline`: the offline IOP: explicit instance = the record.
    `link`: the link IOP on a first and a further encoded index: explicit instance = both records.
    `onlineBatch`: a session: the explicit instance of a slot = (x, record).
    `honestOfflineProver`, `honestLinkProver`, `honestOnlineBatchProver`: the honest sides: the private input holds, beside (index, committer's
      randomness), the seed of the record of each encoded index: the prover keeps the record with
      its prover encoded index. So the shared part of a session's honest prover, which by type sees
      no instance, knows the record.
  The properties:
    `WiredR`: the index decoder returns i on an honest encoded index with an honest record, at every
      seed; also `extT`, `extL`, `extB`.
    `SoundAtR`, `SoundR`: index binding, round-by-round, with a witness. Five clauses:
      `noneColl`: the index decoder says none at a collision.
      `rcd`: the record clause: for every word at most eR seeds give a collision. It is a clause of
        its own, not an entry of a protocol's list. The reason: let a word lie within the radius of
        two different codewords, each with an index of the index set. Then nothing is wrong with the
        word as far as the offline IOP can tell, and its errors are never charged; but if one record
        agreed with both codewords, a prover could run sessions for the one index today and for the
        other tomorrow.
      `sndT`: offline: on statements (record, word) without a collision: language "the index decoder
        answers".
      `sndL`: link: on statements whose first encoded index decodes and whose further one has no
        collision: language "the further one decodes to the same index". (The record clause, which
        speaks of every word, covers the further encoded index too.)
      `sndB`: a session: for each record, the batch IOP on instances x with that record in all slots
        has knowledge soundness, instance by instance (Ior/KnowWide.lean: `SndBKT`), for the
        relation "the index decoder says none, or the witness is valid for the decoded index". The
        list of errors is one for all records. The witness map may read the slot's instance with the
        record, the word, and the slot's whole local transcript.
    `ReadsR`: numbers of positions read, as in `BatchProtocol.Reads`; `hidE`: the law of (honest answer, the
      encoded index at any b positions) does not depend on the index, at every seed.
    `HidingR`, `CompleteR`: honest-verifier zero knowledge (exact form; the simulator is given the
      records, as part of the explicit instance; exactly: `Honest.HVZK`, Iop/InteractiveOracleProof.lean,
      `BatchHonestProver.HVZK`, Iop/Batch.lean, at the numbers `zT`, `zL`, `zO`) and completeness
      (`Honest.Acc`, Iop/InteractiveOracleProof.lean; `prT`, `prL`, `prB` at the numbers `pT`, `pL`, `pO`) of the
      three protocols on honest records: "for every output of the committer and every record of an
      honest record phase" (`validT`, `validL`, `validB`; `validB` also asks `Ryes` of index and
      instance).
    `PropsH`: all properties but index binding and `sub`: no extractor and no relaxed relation
      occurs in them; `PropsR`: all together.



    `L.atRec r`: an object with records, all records fixed to r, as an `BatchProtocol`.





    `Spec.soundR_iff_at`: `SoundR` is `SoundAtR` for some eR and lists at most εs as probabilities
      (`Err.Below`; eR over the number of seeds).
    `Spec.soundR_lang`: what index binding says of languages.

Limits: (0) PropsR.sub is at the level of LANGUAGES (if x has a witness in Ryes it has one in Rno),
as in this library's Iop.BatchProtocol.Props; on paper the relation is contained in its relaxation WITH
witnesses.

Hiop/RecConf.lean's `ConfigurationWithOutOfDomainSample.Props` keeps the clause with witnesses. (a) Honest-verifier zero
knowledge is in this library's exact form (Ior/Honest.lean says why); an encoding with a positive
error is not covered. (b) Errors are counts. (c) The honest prover of a slot gets no witness
here. (d) `early` and `late` are kept from `Iop.BatchProtocol`, on the part x of an instance, so
that every `BatchProtocol` is an instance.
This file says nothing on whether any object has the properties. That one record is taken for each
encoded index is a fact about whoever runs the phases (honest-verifier zero knowledge of the whole
object: Hiop/RecWhole.lean): two records of one encoded index can give away functionals of the
index. This file says nothing on the compiled argument, and nothing on running times.
The object follows the worked example named in lean/CREDITS.md and this protocol's technical report,
which follows the paper that this protocol builds on; the record follows advice.

Terms: lean/GLOSSARY.md: object, record, collision, encoded index, index decoder, offline IOP, link,
  session, slot, honest side, list of errors, (Snd-B).
-/
import Hiop.RecKit
import Hiop.KnowWide

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- The algorithms, with a record phase after each encoded index, and the honest sides. -/
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

attribute [instance] HolographicProtocol.encodingRandomnessIsFinite HolographicProtocol.encodingRandomnessIsNonempty HolographicProtocol.outOfDomainSeedIsFinite HolographicProtocol.outOfDomainSeedIsNonempty

variable {I X Wn : Type}

namespace HolographicProtocol

/-- A record: the seed and the answer. -/
abbrev Rec (L : HolographicProtocol I X) : Type := L.OutOfDomainSeed × L.OutOfDomainAnswer

/-- the record of an honest record phase -/
def recOf (L : HolographicProtocol I X) (i : I) (r : L.EncodingRandomness) (s : L.OutOfDomainSeed) : L.Rec := (s, L.honestOutOfDomainAnswer i r s)

/-- a session with the record rec in all slots -/
abbrev batAt (L : HolographicProtocol I X) (rec : L.Rec) : BatchInteractiveOracleProof X (oneExternalString L.wordLength L.Symbol) :=
  L.onlineBatch.comap fun x => (x, rec)

/-- the relation of a session on (instance, word, witness), at a record -/
def relB (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop) (rec : L.Rec) :
    X → (oneExternalString L.wordLength L.Symbol).Str → Wn → Prop :=
  fun x y w => L.decodeIndex y rec = none ∨ ∃ i, L.decodeIndex y rec = some i ∧ Rno i x w

structure WiredR (L : HolographicProtocol I X) : Prop where
  dec_enc : ∀ i r s, L.decodeIndex (L.encodeIndex i r) (L.recOf i r s) = some i
  extT : ∀ i r s, L.honestOfflineProver.ext (i, r, s) = L.encodeIndex i r
  extL : ∀ i r s r' s', L.honestLinkProver.ext (i, (r, s), (r', s')) = (L.encodeIndex i r, L.encodeIndex i r')
  extB : ∀ i r s, L.honestOnlineBatchProver.ext (i, r, s) = L.encodeIndex i r

/-- Index binding, round-by-round, with a witness: explicit numbers. eR: seeds; εT, εL, εB: the
three lists. -/
structure SoundAtR (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) : Prop where
  noneColl : ∀ y (rec : L.Rec), L.hasCollisionAt y rec.1 → L.decodeIndex y rec = none
  rcd  : ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR
  sndT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT
  sndL : L.link.Sound
    (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL
  sndB : ∀ rec,
    (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec) (fun x y τ => wit (x, rec) y τ) εB

/-- Index binding; εs bounds every error, as a probability: that of the record clause and those of
the three lists. -/
structure SoundR (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞) : Prop where
  noneColl : ∀ y (rec : L.Rec), L.hasCollisionAt y rec.1 → L.decodeIndex y rec = none
  rcd  : ∃ eR : ℕ,
    (eR : ℝ≥0∞) ≤ εs * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞) ∧ ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR
  sndT : ∃ ε, Err.Below ε εs ∧ L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) ε
  sndL : ∃ ε,
    Err.Below ε εs ∧
    L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) ε
  sndB : ∃ ε : Err L.onlineBatch.loc.shape,
    Err.Below ε εs ∧
    ∀ rec,
      (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec) (fun x y τ => wit (x, rec) y τ) ε

structure ReadsR (L : HolographicProtocol I X) (b qT qpar qch qon : ℕ) : Prop where
  cntT  : ∀ x ρ, (L.offline.extReads x ρ).card ≤ qT
  cntLp : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isLeft)).card ≤ qpar
  cntLc : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isRight)).card ≤ qch
  cntB  : L.onlineBatch.ReadsAtMost L.maxBatchSize qon
  /-- the honest answer together with any b positions of the encoded index: a law that does not
  depend on the index -/
  hidE  : ∀ (S : Finset (Fin L.wordLength)), S.card ≤ b →
    ∀ (s : L.OutOfDomainSeed) i i', (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i r s, fun p : S => L.encodeIndex i r p)) =
      (unif L.EncodingRandomness).map (fun r => (L.honestOutOfDomainAnswer i' r s, fun p : S => L.encodeIndex i' r p))

/-- the inputs of the three honest sides: the records are those of honest record phases -/
def validT (L : HolographicProtocol I X) : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → Prop := fun w rec =>
  rec = L.recOf w.1 w.2.1 w.2.2
def validL (L : HolographicProtocol I X) : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → Prop :=
  fun w rr => rr = (L.recOf w.1 w.2.1.1 w.2.1.2, L.recOf w.1 w.2.2.1 w.2.2.2)
def validB (L : HolographicProtocol I X) (Ryes : I → X → Prop) : I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop := fun w a =>
  a.2 = L.recOf w.1 w.2.1 w.2.2 ∧ Ryes w.1 a.1

structure HidingR (L : HolographicProtocol I X) (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) : Prop where
  hidT : L.honestOfflineProver.HVZK L.validT zT
  hidL : L.honestLinkProver.HVZK L.validL zL
  hidB : L.honestOnlineBatchProver.HVZK L.maxBatchSize (L.validB Ryes) zO

structure CompleteR (L : HolographicProtocol I X) (Ryes : I → X → Prop) (pT pL pO : ℝ≥0∞) : Prop where
  accT : L.honestOfflineProver.Acc L.validT
  accL : L.honestLinkProver.Acc L.validL
  accB : L.honestOnlineBatchProver.Acc (L.validB Ryes)
  prT  : ∀ w x, L.validT w x → prRho (L.honestOfflineProver.withheld w x) ≤ pT
  prL  : ∀ w x, L.validL w x → prRho (L.honestLinkProver.withheld w x) ≤ pL
  prB  : ∀ w x, L.validB Ryes w x → prRho (L.honestOnlineBatchProver.one.withheld w x) ≤ pO

/-- All properties but index binding and `sub`: the honest side and the formats. No extractor, no
relaxed relation occurs here. -/
structure PropsH (L : HolographicProtocol I X) (Ryes : I → X → Prop) (M : LH.Nums) : Prop where
  wired    : L.WiredR
  reads    : L.ReadsR M.b M.qT M.qpar M.qch M.qon
  hidden   : L.HidingR Ryes M.zT M.zL M.zO
  complete : L.CompleteR Ryes M.pT M.pL M.pO
  localT   : L.offline.IsLocal
  localL   : L.link.IsLocal
  localB   : L.onlineBatch.loc.IsLocal
  cohB     : L.onlineBatch.ann.Coherent
  pointT   : Nonempty L.offline.shape.IsPoint
  pointL   : Nonempty L.link.shape.IsPoint
  pointB   : Nonempty L.onlineBatch.loc.shape.IsPoint

/-- All properties together. Ryes, Rno are relations with witnesses; the numbers are those of
`LH.Nums` (Iop/InteractiveOracleProof.lean). -/
structure PropsR (L : HolographicProtocol I X) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums) : Prop where
  sub    : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w
  sound  : L.SoundR Rno wit M.εs
  honest : L.PropsH (fun i x => ∃ w, Ryes i x w) M

/-- All records fixed to r: an `BatchProtocol`. -/
def atRec (L : HolographicProtocol I X) (r : L.Rec) : BatchProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := fun y => L.decodeIndex y r
  offline := L.offline.comap fun _ => r
  link := L.link.comap fun _ => (r, r)
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.batAt r
  honestOfflineProver := L.honestOfflineProver.comap (fun _ => r) (fun w => (w.1, w.2, r.1))
  honestLinkProver := L.honestLinkProver.comap (fun _ => (r, r)) (fun w => (w.1, (w.2.1, r.1), (w.2.2, r.1)))
  honestOnlineBatchProver := L.honestOnlineBatchProver.comap (fun x => (x, r)) (fun w => (w.1, w.2, r.1))
  early := L.early
  late := L.late

end HolographicProtocol

namespace Spec

def soundR_iff_at : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundR Rno wit εs ↔
    ∃ eR εT εL εB, L.SoundAtR Rno wit eR εT εL εB ∧
      (eR : ℝ≥0∞) ≤ εs * (Fintype.card L.OutOfDomainSeed : ℝ≥0∞) ∧
      Err.Below εT εs ∧ Err.Below εL εs ∧ Err.Below εB εs

/-- States what index binding (`SoundAtR`) says of languages: for each record, (Snd-B), late form,
for "the index decoder says none, or x is in the language of the decoded index". -/
def soundR_lang : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtR Rno wit eR εT εL εB →
    ∀ rec, (L.batAt rec).SndBL L.maxBatchSize L.early L.late
      (fun x y => L.decodeIndex y rec = none ∨ ∃ i, L.decodeIndex y rec = some i ∧ ∃ w, Rno i x w) εB

end Spec

end Iop
