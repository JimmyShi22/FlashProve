-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofCoded.lean: one record of five laws on typed oracle functions, each in the form
in which another file of this library takes it as a premise, all at the format's own oracle
`Fmt.oracle`; and that what the proof file's encoding `mProof` reads out of the oracle made from
Lean's BLAKE2b (`oBits`, Run/OracleBits.lean) meets it. That these five are all that a tie of that
file asks of the oracle functions is not said here. `mProof` is the proof file's encoding alone: the
entry file's and the key file's chain queries go to `back`, but where the page's field `seeds`
writes; no one encoding of all three files' queries is given.

The five are proved in OnBytes/K/Arm/ProofAtBits.lean (the chains), ProofTrees.lean (leaves and
vertices) and ProofRequest.lean (the request tree). Here they stand side by side, at one family and
one oracle. For proofs only; the program does not import this file.

Main names.
 `ProofCoded C g bd` chains: `SpeaksQ g .onl C.P.proof Fmt.oracle (QProof C) (QgProof C)`
                (OnBytes/Maker/Page/ChainsQ.lean), from which that file has the seven laws of the
                three chains; leaves: `LeafRow g Fmt.oracle bd` at the leaf queries at which the
                page's taken spelling writes (OnBytes/Maker/Page/CodeRows.lean); nodes: `NodeIs g
                (Fmt.HO Fmt.oracle) C.P.cfg` (OnBytes/Maker/RecNodes.lean); rnodes, rleaves:
                `NodeCoded`, and `LeafCoded` at every depth below 63
                (OnBytes/TypedOracleCompiler/Joined/K/Request.lean).
 `proofCoded` `ProofCoded C (readBlocks (mProof C H back) oBits) bd`.

Asked: `ProofLaws C`; `Spells C.P.leafX bd` (OnBytes/K/Arm/KeyTrees.lean); the page's `sR` is a
salt's length as the format has it.

Not claimed. `ProofLaws` at any cut. That a total code `back` exists at any interface. That a
verifier's queries meet `QProof`, `QgProof` or are leaf queries at which the spelling writes. One
fixed function stands here, Lean's BLAKE2b, in the place of a random function. The encoding's
inverse is taken by choice (OnBytes/TypedOracleCompiler/Run/PageOf.lean). Nothing on soundness.

Where the page's first statement holds a request through the format's item, which is made of digests
of the request, `ProofLaws` cannot hold at a test of fitness that lets the first query of every
request through: there are more requests than items, so two such queries would have one call.
Nothing here shows that it holds at any test; what this cause leaves open is a test that lets
through a set of instances on which the item is one to one. That it is so on a given set is a
hypothesis on the hash that makes the digests. The set stands in the encoding. Whoever lays it has
to name it without knowledge of the hash function and before any run; nothing here enforces that.
For a request outside the set nothing is tied here.

The page's data hold three digests of parameter bytes. The laws on the three first queries
(OnBytes/K/Arm/ProofAtBits.lean) ask that each is the hash of its parameter bytes under the hash
that the function that is read gives. A cut laid so is chosen after the function: its encoding
serves a tie at one fixed function, and it is not fixed before a function is drawn, as a bound over
a drawn function asks. Of the configuration's digest the laws here ask the length alone.

The record can also be met at a cut that writes none of the file's chain queries and none of its
leaves: both tests false, both spellings silent; there `ProofLaws` asks no more than the digest's
length and three inequalities of labels. Then `chains` and `leaves` say nothing; `nodes`, `rnodes`
and `rleaves` say what they say at every cut. Whoever uses it has to bring, at the same cut,
`QProof` and `QgProof` at the file's own queries, and that the page's spelling of leaves writes at
the file's own leaf queries (for the carried code of leaves: OnBytes/K/Arm/LeafWritesAt.lean).

At a chain query of the format f2 whose head holds an instance the page has no call, so no law here
speaks of it. Where the compiled verifier is handed an instance, its query of the round that the
interface's field `late` names holds it (the head of OnBytes/TypedOracleCompiler/Compile/Batch/LateX.lean); the
shared chain's queries hold none. So the row laws reach a proof file's run only where that round is
none of the written rounds of the first and the third chain. That is asked nowhere here; the tie
asks it itself (`ReadL.late₁`, `ReadL.late₃`, OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean).

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.ProofAtBits
import OnBytes.K.Arm.ProofTrees
import OnBytes.K.Arm.ProofRequest

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The five laws on typed oracle functions, at the format's own oracle.** -/
structure ProofCoded (C : ProofCut L (K + 1)) (g : Fam (typedOracleFamily 256 (K + 1) L)) (bd : L.Bd → List Bool)
  :
    Prop where
  /-- the three chains' queries -/
  chains : SpeaksQ g .onl C.P.proof Fmt.oracle (QProof C) (QgProof C)
  /-- the leaves of the trees over oracles and over stored tables -/
  leaves : LeafRow g Fmt.oracle bd fun q => (C.P.leafX q).isSome
  /-- their vertices -/
  nodes : NodeIs g (Fmt.HO Fmt.oracle) C.P.cfg
  /-- the request tree's vertices -/
  rnodes : TypedOracleCompiler.Joined.K.NodeCoded g C.P.cfg
  /-- the request tree's leaves -/
  rleaves : ∀ d, d < 63 → TypedOracleCompiler.Joined.K.LeafCoded g d C.P.cfg C.P.sR (rsOf d)

/-- **What the proof file's encoding reads out of `oBits` meets all five.** -/
theorem proofCoded (C : ProofCut L (K + 1)) (H : ProofLaws C) (back : StrCode (AllPts 256 (K + 1)
  L))
    (bd : L.Bd → List Bool) (hS : Spells C.P.leafX bd) (hR : Fmt.saltLenOK C.P.sR = true) :
    ProofCoded C (readBlocks (mProof C H back) oBits) bd where
  chains := speaks_proof_bits C H back
  leaves := leafRow_proof_oBits C H back bd hS
  nodes := nodeIs_proof_oBits C H back
  rnodes := nodeCoded_proof_oBits C H back H.cfg
  rleaves := fun d hd => leafCoded_proof_oBits C H back d hd H.cfg hR

end OnBytes.K.Arm
