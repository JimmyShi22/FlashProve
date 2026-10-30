-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/RecScheme.lean: the compiled argument for an object with records (`Iop.HolographicProtocol`,
Hiop/RecInterface.lean): the key, a proof, the verifier, the two extractors. Terms only, but for one
statement that holds by definition (`carrier_types`): a written target; no theorem on the scheme
stands behind it.

No rendering of the text's compilation. (d) below is written of a form of the text that leaves its
point open; the text settles it the other way than here. There the seed of a record is the answer
of a query of its own, on the root alone (no salt, no work, nothing else in the query), to a record
oracle: one such oracle for the first encoded index, one for further ones. So a root has one seed by
construction. The chains come after that query, and every chain's first query holds the record
beside the root; a link's holds both records. The key holds (root, seed, answers); the verifier
recomputes the seed and compares.
  Away from the text, therefore, in this file: the record phase played as the first two rounds of
    the offline and of the link's chain (`L.offR`, `L.linkR`); "the offline chain's first query
    holds nothing of the record"; "the link's first query holds the first record only"
    (by a reading of a print of this protocol's technical report
    (lean/CREDITS.md); not held against the report's latest edition). On (a): there a root has one
    seed, so records under one root can differ in their answers only; how much of (a)'s weight that
    leaves is not known here.
  What stands: the key's fields; E_i on the key's first record; records are known at the start of
    every chain, as `Iop.HolographicProtocol` types its instances. Hiop/RecLine.lean's one-line forms stay true as
    statements on the level of the IOP.
  The terms are left as they are: no theorem stands on them but `carrier_types`, which holds by
    definition.

The object is `Iop.HolographicProtocol` (Hiop/RecInterface.lean): after each encoded index the verifier draws a seed
and the prover answers; (seed, answer) is the record of that encoded index, and the index decoder
reads (word, record). Hiop/RecLine.lean plays the phase as two rounds in front of the first protocol
on a new encoded index (`InteractiveOracleProof.led`).
The compiled verifier of one chain is the library's, unchanged (`verifyOneProtocol`,
Compile/Batch/Verifier.lean, which is generic in the protocol and in its type of instances): same
oracles, same formats of queries, same argument strings. What differs is which protocols it is run
on, on which instances, and what of an instance the first query of a chain holds.

Main names:
  `L.offR a0`, `L.linkR a0`: the IOP's verifier compares the claimed record with the seed that the
    chain gives and the answer that the string holds.
  `L.carrier a0`: the interface of the library's kind over which the typed oracles are formed
    (`spec`, Compile/Batch/Oracles.lean). The oracles read of it: the alphabet of an encoded index,
    the three shapes, the annotation of a session, the type `L.XH`; the chain reads `early` and
    `late`. These are the object's. Its three verifiers reject everything, its decoder says none,
    its honest sides send the fixed substitutes: nobody runs them, and nothing is claimed of it.
  `PrfR`: a proof: the number of a further encoded index, the session's string of one instance.
  `VR`: the verifier: three compiled verifiers, all run, then the conjunction:
    offline (`vOffR`): external root: the first. Instance: the key's first record. The first query
      holds nothing of it (the record does not exist yet: that query's answer gives its seed).
    link (`vLinkR`): external roots: the first, number j. Instance: (first record, record number j).
      The first query holds the first record; its answer gives the seed of record number j.
    session (`vBatR`): external root: number j. Instance: (x, record number j). The first query of
      the instance's chain holds `L.early x` and the record.
    So the whole seed stands in the key and is compared with the chain, by the IOP's own verifier
      inside the compiled one: no new test, no new query.
  `extractorR`: E_i: the index decoder on (what the committer's trace determines under the first
    root, the key's first record): it reads the key and Merkle entries, as `extractorK`'s
    (CompileK/Main.lean). E_w recomputes (`Gen.recompute`, CompileK/Recompute.lean): `re` of the
    extracted index and the instance. It reads no verifier message but the seed in the key's first
    record, no part of the proof and not the prover's trace. This is the target text's extractor.
  `extractorRT`: an extra, no rendering of the text: the natural extractor for a wide witness map
    (CompileK/KnowExtT.lean): follow the instance's chain (`rhoRc`) in the committer's trace
    followed by the prover's; if it is all there: some (`wit` on the instance with the key's record
    number j, the extracted word, the extracted local transcript); else none. What it would add:
    that the prover itself sent a witness.
  `L.RecShared rd`: a law of the object, asked by nobody but the statements `Spec.rec_binding_lang`
    and `Spec.rec_binding` of CompileK/RecBindSpec.lean, which are not proved: the shared plain part
    of a session's first shared round holds the record, and the verifier of a slot accepts only if
    it is the slot's. One way out of (a) below.
  `Spec.carrier_types` (proved here, by definition): see its doc comment.

Notation: `L`: an `Iop.HolographicProtocol I X`: the object; `a0`: an `L.OutOfDomainAnswer`: a fixed answer, the last argument of
`recShape` (Hiop/RecLine.lean); `W`: a `QueryLayout lam (L.carrier a0)` (Iop/BatchWire.lean): a wire of
the carrier; `W.depthReq`: a natural number (Iop/BatchWire.lean): the depth of a request tree (the
instance tree of (e)); `p`: a `Params` (Compile/Star.lean): four numbers; `Tag.test`, `Tag.link`,
`Tag.onl`: of type `Tag` (Compile/Oracles.lean): the tags of the offline, the link's and the
session's protocol; E_i, E_w: the fields `Ei`, `Ew` of `Gen.Extractor` (ZKCP/Gen.lean); `rd`: a map
(`Plains L.onlineBatch.loc.shape → L.Rec`) from the plain parts of all prover messages (`Plains`,
Iop/Shape.lean) to records.

Limits:







DECLARED, against the target text (a comparison by reading).
  (a) The shared chain's first query holds no record. Away from the text: an index-binding theorem
    on this scheme must meet it. The format has the external root, the root of the tree over the
    instances' values, a root and a plain part, and no field for an instance. The text has the
    record in the first query of every chain of a session, because one root may have many records.
    Why it matters: the object's clause on a session speaks of one record in all slots.
    Under one shared query a cheating prover can join chains that start from one root and different
      records (a key may list a root twice). If the shared query held the record, slots with another
      record could be dropped, as slots with another root are: no verifier accepts them with that
      query. As it is, the joint error of a shared round is owed once for each record present.
    Two ways out: a field for the record in that format (a change of the compiler's terms: a further
      instance of the compiler); or, with the compiler as it stands, the law `L.RecShared`: the
      record stands in the shared plain part, which that query holds; an argument string then holds
      the record, which a map on proofs can take out again, the verifier writing it back from the
      key (as Compile/GenPub.lean does for the links: `pubK`, Compile/Batch/StarK.lean). A third way
      out, no mend: a bound that pays the number of records under a root.
  (b) The answer's round has a chain query of its own. The library's compiled verifier asks one
    query for each round. The text's compiler asks one for each non-empty verifier message: a prover
    message that is followed by an empty one goes into the next query as a plain part. (That all
    rounds are counted and nothing is merged is the text's way of counting in theorems.) For
    soundness the query of the answer's round is an entry 0. The library's pass that joins such a
    round to the next (Iop/BatchRecut.lean) is not applied here.
  (c) If the object writes an instance into a chain in two parts (`late` is some round), the query
    of that round in a link's chain holds the first record a second time: the chain's rule is one
    for all three protocols. At late = none, as in the protocol of a print of the technical
    report (lean/CREDITS.md), nothing of the kind happens.
  (d) Which oracle gives a seed: here the Fiat-Shamir oracle of the offline argument, and of a link,
    at its first round; so a link's first query holds the first record only. Away from the text. The
    text's head names record oracles and its body does not say what they are; if they are oracles of
    their own that give a seed from the root(s), a link's first query could hold both records.
  (e) All that the head of CompileK/Main.lean declares of the first instance of the compiler: its
    seven points, among them: (2) a leaf of the instance tree (the tree over the instances' values
    of (a)) is the hash of the bare value of an instance; (7) one leaf oracle and one node oracle
    for all trees over oracles (`OracleName.leaf`, `OracleName.node`), and a pair of their own for the instance
    trees (`OracleName.rleaf`, `OracleName.rnode`, Compile/Batch/Oracles.lean).
No committer and no prover: so no scheme in the sense of ZKCP/Gen.lean, no completeness, no privacy.
The library's compiled prover cannot be run on `L.offR` or `L.linkR` as it stands: it is handed its
instance at the start, and here the instance holds a record whose seed the run itself produces. One
record for each encoded index, ever: a second offline proof, or a link made again on the same
further encoded index, must go on from the first one's chain behind the answer; every run of a led
protocol draws a new seed, and who keeps and reuses that piece of a chain is not modelled. No
index-binding theorem, nor one on any other form of binding: a cheating prover names the claimed
record after it has seen the seed, so what is to be used of the object is Hiop/RecLine.lean's
one-line forms, which quantify the claimed record behind the transcript.
Both parts of `extractorR` read their traces through Merkle entries alone, so the passage to one
oracle takes them (`LocalTo`, Rom/Family.lean), by reading. How much a witness clause with a
recomputing extractor is worth: the head of CompileK/Recompute.lean. Of `extractorRT`: how often it
says none while `VR` accepts is not bounded, and it reads Fiat-Shamir answers, so that passage does
not take it. No proof of work here: tests are added to protocols and wires before these terms are
formed.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecLine
import CompileK.KnowExtT
import CompileK.Recompute

set_option autoImplicit false

noncomputable section

namespace Iop

variable {I X : Type}

/-- a protocol of the shape s that reads nothing and rejects: it stands where only a shape is
wanted -/
def InteractiveOracleProof.hollow {Y : Type} {E : ExtSpec} (s : Shape) : InteractiveOracleProof Y E where
  shape := s
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => false

/-- the shared part's strategy that sends the fixed substitutes -/
def SStrat.hollow : (s : Shape) → (A : RoundSplits s) → SStrat s A
  | [], _ => ()
  | r :: s, (a, A) => ((a.split (r.dOrc, r.dPlain)).1, fun _ => SStrat.hollow s A)

/-- the same for a slot's part -/
def LStrat.hollow : (s : Shape) → (A : RoundSplits s) → LStrat s A
  | [], _ => ()
  | r :: s, (a, A) => ((a.split (r.dOrc, r.dPlain)).2, fun _ => LStrat.hollow s A)

namespace HolographicProtocol

/-- The offline IOP with the record phase of the first encoded index in front. Instance: the claimed
record. -/
def offR (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) : InteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol) := L.offline.led id a0

/-- The link IOP with the record phase of the further encoded index in front. Instance: (the first
record, the claimed record of the further one). -/
def linkR (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) : InteractiveOracleProof (L.Rec × L.Rec) (twoExternalStrings L.wordLength L.Symbol) :=
  L.link.led Prod.snd a0

/-- What the first query of a chain can hold of an instance: a link: (nothing, the first record); a
session: (x, the record). -/
abbrev XH (L : HolographicProtocol I X) : Type := Option X × L.Rec

/-- The carrier of the typed oracles. Read: wordLength, maxBatchSize, Symbol, the three shapes, the annotation, XH, early,
late. All else is idle. -/
def carrier (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) : BatchProtocol I L.XH where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  decodeIndex := fun _ => none
  offline := InteractiveOracleProof.hollow (L.offR a0).shape
  link := InteractiveOracleProof.hollow (L.linkR a0).shape
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

/-- two lists of plain parts have the same shared plain part in the first shared round -/
def _root_.Iop.Plains.SameJoin : (s : Shape) → (A : RoundSplits s) → Plains s → Plains s → Prop
  | [], _, _, _ => True
  | _ :: s, (a, A), (p, ps), (q, qs) =>
      match a.kind with
      | .sh => (a.plain p).1 = (a.plain q).1
      | .lo => Plains.SameJoin s A ps qs

/-- The law "the shared plain part of a session's first shared round holds the record": rd reads it
there and nowhere else; the verifier of a slot accepts only if it is the slot's record. A
definition: no statement of this library asks it but `Spec.rec_binding_lang` and `Spec.rec_binding`
(CompileK/RecBindSpec.lean), which are not proved. -/
structure RecShared (L : HolographicProtocol I X) (rd : Plains L.onlineBatch.loc.shape → L.Rec) : Prop where
  there : ∀ pl pl', Plains.SameJoin L.onlineBatch.loc.shape L.onlineBatch.ann pl pl' → rd pl = rd pl'
  tied  : ∀ x rec y (τ : Tr L.onlineBatch.loc.shape),
    L.onlineBatch.loc.accept (x, rec) y τ = true → rd τ.plains = rec

end HolographicProtocol
end Iop

namespace Compile.Batch
open Iop Rom ZKCP

variable {I X Wn : Type} {lam : ℕ}

/-- The key. -/
structure KeyR (lam : ℕ) (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer) where
  /-- the root of the tree over the first encoded index -/
  cm : Dig lam
  /-- its record -/
  rcd : L.Rec
  /-- the offline string -/
  piT : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto (L.offR a0)))
  /-- for each further encoded index: its root, its record, the link's string -/
  links : List (Dig lam × L.Rec × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto (L.linkR a0))))

/-- A proof. -/
structure PrfR (lam : ℕ) (L : HolographicProtocol I X) where
  /-- the number of a further encoded index -/
  leaf : ℕ
  /-- the session's string of the instance -/
  piB : Option (OneProtocolProof lam L.onlineBatch)

variable {L : HolographicProtocol I X} {a0 : L.OutOfDomainAnswer} (W : QueryLayout lam (L.carrier a0))

/-! the carrier's wires, read as wires of the three protocols: the same data (a wire speaks of a
protocol's shape, annotation and kind of external oracles alone) -/

def wOff : ProtocolQueryLayout lam W.K (BatchInteractiveOracleProof.ofProto (L.offR a0)) :=
  ⟨W.T.sh, W.T.ext, W.T.decO, W.T.nOpen, W.T.maxDepth⟩
def wLink : ProtocolQueryLayout lam W.K (BatchInteractiveOracleProof.ofProto (L.linkR a0)) :=
  ⟨W.Lk.sh, W.Lk.ext, W.Lk.decO, W.Lk.nOpen, W.Lk.maxDepth⟩
def wBat : ProtocolQueryLayout lam W.K L.onlineBatch := ⟨W.B.sh, W.B.ext, W.B.decO, W.B.nOpen, W.B.maxDepth⟩

/-- the compiled offline verifier: external root cm; instance: the claimed record, of which the
first query holds nothing -/
def vOffR (p : Params) (cm : Dig lam) (rec : L.Rec)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto (L.offR a0))) :
    TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto (L.offR a0)) (wOff W)
    (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none)
    (fun s => some (.inl s)) W.depthReq [cm] rec π

/-- the compiled link verifier: external roots cm, cm'; instance: (first record, claimed record), of
which the first query holds the first record -/
def vLinkR (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto (L.linkR a0))) :
    TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto (L.linkR a0)) (wLink W)
    (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun rr => some (none, rr.1))
    (fun s => some (.inl s)) W.depthReq [cm, cm'] (rec, rec') π

/-- what the chain of an instance is handed of it: x and the record (its first query holds
`L.early x` and the record) -/
def xinR (a : X × L.Rec) : Option L.XH := some (some a.1, a.2)

/-- the compiled verifier of an instance of a session: external root cm; instance (x, record) -/
def vBatR (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.onl L.onlineBatch (wBat W) (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id xinR
    (fun s => some (.inl s)) W.depthReq [cm] (x, rec) π

/-- The verifier: the three compiled verifiers, all run, then the conjunction; false if the key's
offline string, the key's entry number `π.leaf` with its link's string, or the proof's string is
missing. -/
def VR (p : Params) (v : KeyR lam L a0) (x : X) (π : PrfR lam L) : TypedOracleComputation lam W.K (L.carrier a0) Bool :=
  match v.piT, v.links[π.leaf]?, π.piB with
  | some πT, some (cmj, recj, some πL), some πB => do
      let a ← vOffR W p v.cm v.rcd πT
      let b ← vLinkR W p v.cm cmj v.rcd recj πL
      let c ← vBatR W p cmj x recj πB
      pure (a && b && c)
  | _, _, _ => pure false

/-- the instance's chain, followed in a trace: its verifier messages; none if a query of the chain
does not stand there, or if the chain is not defined (the format of a round is not defined or a root
is missing) -/
def rhoRc (tr : Tc W) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    Option (Rho L.onlineBatch.loc.shape) :=
  ((recomputeChainOfProof Tag.onl L.onlineBatch (wBat W) id xinR [cm] (x, rec) π).follow tr).join.map fun z => z.1

/-- the extracted local transcript: oracles by Merkle extraction under the roots of the string, its
plain parts, the verifier messages ρ -/
def starRc (tr : Tc W) (π : OneProtocolProof lam L.onlineBatch) (ρ : Rho L.onlineBatch.loc.shape) : Tr L.onlineBatch.loc.shape :=
  trStar tr L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh (prjSym (L := L.carrier a0) Tag.onl)
    ((rtsPure L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh .first π.roots).getD (RootsOfChain.none _)) π.plains ρ

/-- the index extractor alone -/
def extractorR0 :
    Gen.Extractor (spec lam W.K (L.carrier a0)) I X Unit (KeyR lam L a0) (PrfR lam L) where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm) v.rcd
  Ew := fun _ _ _ _ _ => ()

/-- The two extractors: the index by decoding with the key's record; the witness recomputed from the
extracted index and the instance (w0 if no index is extracted). -/
def extractorR (re : I → X → Wn) (w0 : Wn) :
    Gen.Extractor (spec lam W.K (L.carrier a0)) I X Wn (KeyR lam L a0) (PrfR lam L) :=
  Gen.recompute (extractorR0 W) re w0

/-- an extra: the witness read off what the prover sent -/
def extractorRT (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) :
    Gen.Extractor (spec lam W.K (L.carrier a0)) I X (Option Wn) (KeyR lam L a0) (PrfR lam L) where
  Ei := fun v tr => L.decodeIndex (extEnc W tr v.cm) v.rcd
  Ew := fun v trC x π trP =>
    match v.links[π.leaf]?, π.piB with
    | some (cmj, recj, _), some πB =>
        (rhoRc W (trC ++ trP) cmj x recj πB).map fun ρ =>
          wit (x, recj) (extEnc W (trC ++ trP) cmj) (starRc W (trC ++ trP) πB ρ)
    | _, _ => none

/-! ## What the carrier carries: by definition -/

namespace Spec

/-- States: the typed oracles are formed over the object's own shapes (offline and link: with the
two rounds of the record phase in front), annotation and alphabet, with its wordLength and maxBatchSize. -/
def carrier_types : Prop :=
  ∀ (I X : Type) (L : HolographicProtocol I X) (a0 : L.OutOfDomainAnswer),
    shapeOf (L.carrier a0) Tag.test = recShape L.OutOfDomainSeed L.OutOfDomainAnswer a0 ++ L.offline.shape ∧
    shapeOf (L.carrier a0) Tag.link = recShape L.OutOfDomainSeed L.OutOfDomainAnswer a0 ++ L.link.shape ∧
    shapeOf (L.carrier a0) Tag.onl = L.onlineBatch.loc.shape ∧
    HEq (annOf (L.carrier a0) Tag.onl) L.onlineBatch.ann ∧
    (L.carrier a0).Symbol = L.Symbol ∧ (L.carrier a0).wordLength = L.wordLength ∧ (L.carrier a0).maxBatchSize = L.maxBatchSize

end Spec

theorem carrier_types : Spec.carrier_types := fun _ _ _ _ => ⟨rfl, rfl, rfl, HEq.rfl, rfl, rfl, rfl⟩

end Compile.Batch
