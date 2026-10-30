-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Main.lean: the compiler's data, extractor and simulator for an arbitrary holographic IOP
with an untrusted committer.

Definitions.

No protocol occurs here. The object is any interface L : Iop.BatchProtocol I X (Iop/Batch.lean; its parts in
words: the head of Hiop/Interface.lean) with a witness map "wit" that reads a witness off an
instance and the prover's oracles of a full local transcript of a session. An interface has an
encoder of the index (`encodeIndex`: the IOP's committer), an index decoder (`decodeIndex`), and three IOPs: an
offline IOP on one encoded index, a link IOP on a first and a further encoded index, and a batch
IOP with at most maxBatchSize instances on one encoded index.










Main names:
  `DataK L lam`: the data of the compilation: the prover's oracles are strings (`Shape.IsPoint`); a
    padding symbol; the announced numbers of opened positions; the samplers that make each verifier
    message from λ-bit blocks; numberings of positions and coins and the depth of the instance tree
    (`depthReq`; Lean's name for it: request tree), among the fields of `ax` (`BatchProtocol.Aux`,
    Iop/BatchWireOf.lean); salt lengths, the number of further encoded indices and of sessions on
    each; the index that the simulator encodes.
  The scheme at these data: withW (argBKE ..): key = root of the first encoded index, offline proof,
    and for each further encoded index its root and link proof; a proof = the number of a further
    encoded index, drawn uniformly, and the slot's string of the compiled session. Fresh coins; no
    seed, no pruned paths, no proof of work. The prover ignores the witness that it is handed
    (CompileK/GenWit.lean).
  `extractorK`: index: decode what the committer's trace determines under the root in the key.
    Witness: the roots in the proof; Merkle extraction from the committer's trace followed by the
    prover's; wit (CompileK/KnowExt.lean). Not the verifier's queries, no oracle; no value is taken
    by choice (Lean's list of the axioms under the extractor has `Classical.choice` all the same:
    for one, an equality of positions inside it is decided classically: Compile/Batch/Sound.lean:
    `prjSym`).
  `simulatorK`: the compiler's simulator around simulators Sm of the three IOPs.
  `codingK`: a named coding of the typed oracles in one oracle, from serialisers (`implReal`,
    Compile/Batch/Ser.lean).
  `FitK`: conditions on numbers and formats, to be discharged at the instance. Two of them bear on
    security: "good" is the law of the samplers (bias κ₀ a block), on which the three bounds rest;
    "budget" is the hiding condition: what the offline IOP and the links read of the first encoded
    index, and what a link and the sessions read of a further one, stays within the b positions
    that an encoded index hides. The others: κ₀ is at least 1; the verifiers open at most the
    announced numbers of positions; the batch bound is a power of two; the kinds of rounds of a
    session run local, shared, local, and a component of a prover message that is not sent is empty
    (`RoundSplits.Fmt`, Iop/BatchFmt.lean); n bounds the blocks of a protocol.

















The compiler's bounds are those of its theorem for languages (`mainBatchKEGrWithBOf`,
Compile/Batch/PubProgMainBGr.lean), letter for letter, at the numbers after the blocks
(`DataK.nums`): α = `alphaBG`, ε = `epsB` (number of queries times the field `εs` of these numbers,
plus a hash term), ζ = `zetaBGen` with the hash terms for one budget.

Lean's compiler is of the same architecture as the paper's construction and differs from it in what
is hashed and sent (a comparison by reading, clause by clause; no theorem. Here only Lean's side is
written out).
  The same: key, proof, the verifier as a conjunction of three compiled verifiers, the form of a
    batch, the index extractor, the two budget lines, the capacity term.
  In seven points Lean's scheme is another. What Lean has: (1) salts of the chain: one salt for the
    chain of an instance, in its first query; none for the shared chain. (2) the instance tree: a
    leaf is the hash of the bare value of an instance; the tree's root is a field of the proof. (3)
    external roots, offline and in a link: fields of the first chain query. (4) what a chain hands
    on: a λ-bit tail that every answer has beside its blocks. (5) a message with several oracles:
    one tree over all positions of a component of the message. (6) "no proof": the prover withholds
    where the verifier randomness lies in the IOP's withheld set; it never runs V; offline and link
    proofs may be withheld too; the notice still holds the number j. (7) Merkle oracles: one leaf
    oracle and one node oracle for all trees over oracles (`OracleName.leaf`, `OracleName.node`); the instance
    trees have a pair of their own (`OracleName.rleaf`, `OracleName.rnode`).
  So Lean's theorems and the paper's are on schemes of one architecture; neither implies the
    other. Not in Lean on this road: a prover that counts its sessions, randomness from keys,
    computational privacy, sizes, times, numbers of queries (but for upper bounds on the honest
    committer's and prover's: CompileK/CountsHonest.lean; and on the verifier's typed queries,
    `tVB`: `detBound_V`, Compile/Batch/GlueBinding.lean; the number written out:
    CompileK/Counts.lean). The paper's lemmas on the way are not rendered: Lean's is another proof.

Limits: this file says nothing on any interface having the properties. It says nothing on running
time: extractor and simulator are functions. The experiment of index binding has one pair (x, π),
not many. At bounds of 1 or more the clauses are empty. It does not say how much the witness clause
is worth: see the head of CompileK/Recompute.lean.

Terms: lean/GLOSSARY.md.

-/
import Hiop.Interface
import CompileK.KnowExt
import Compile.Batch.PubProgMainBGr
import Compile.Batch.HopTot
import Compile.Batch.Extraction
import Compile.Batch.Ser
import Iop.SerBPull
import Top.ProgDraw
import Rom.Carry
import ZKCP.SpecialAny
import ZKCP.GenOptional
import ZKCP.Optional

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type}

/-- The data of the compilation. -/
structure DataK (L : BatchProtocol I X) (lam : ℕ) where
  pT : L.offline.shape.IsPoint
  pL : L.link.shape.IsPoint
  pB : L.onlineBatch.loc.shape.IsPoint
  /-- a padding symbol; the announced numbers of opened positions; the samplers; numberings of
  positions and coins; salt lengths, number of further encoded indices, sessions on each -/
  z  : L.Symbol
  no : OpenNums
  dr : L.Draws lam
  ax : L.Aux pT pL pB
  p  : Params
  /-- the index that the simulator encodes -/
  i₀ : I

variable {L₀ : BatchProtocol I X} {lam : ℕ} (D : DataK L₀ lam)

/-- the interface after the verifier messages are made from blocks, the generic wires, the numbers
after the blocks -/
abbrev DataK.L : BatchProtocol I X := LBd lam L₀ D.dr
abbrev DataK.W : QueryLayout lam D.L := WBd lam L₀ D.pT D.pL D.pB D.z D.no D.dr D.ax
abbrev DataK.WP : WireBP D.L := WPBd lam L₀ D.pT D.pL D.pB D.dr D.ax
abbrev DataK.nums (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) : LH.Nums := numsDraw lam L₀ D.dr M κ₀ n

/-- The extractor. -/
def extractorK {Wn : Type} (wit : X → Orcs L₀.onlineBatch.loc.shape → Wn) (w0 : Wn) :
    Gen.Extractor (spec lam D.W.K D.L) I X Wn (IVKK lam D.L) (PrfK lam D.L) :=
  extractorBKW D.W (fun x o => wit x (Orcs.push (Samplers.ofDraws _ D.dr.B) o)) w0

/-- The simulator, around simulators of the three IOPs. -/
def simulatorK (Sm : Sims L₀) :
    Gen.Simulator (spec lam D.W.K D.L) Unit (IVKK lam D.L) X (PrfK lam D.L) :=
  simBKGr D.W D.p (simsD lam L₀ D.dr Sm) D.i₀

/-- A named coding of typed queries as strings, from serialisers for the interface (a tag for the
parameter set; instances; symbols; the prover's messages): every string is one block of the answer
of exactly one typed oracle at exactly one point. -/
def codingK (Se : SerLHB L₀) : OracleCoding (spec lam D.W.K D.L) lam :=
  implReal (Se.pull (Samplers.ofDraws _ D.dr.T)
      (Samplers.ofDraws _ D.dr.Lk) (Samplers.ofDraws _ D.dr.B))
    lam D.W.K

/-- Conditions on numbers and formats, to be discharged at the instance. -/
structure FitK (M : LH.Nums) (κ₀ : ℝ≥0∞) (n : ℕ) : Prop where
  one_le : 1 ≤ κ₀
  /-- the samplers obey their law, with bias κ₀ a block -/
  good   : D.dr.Good κ₀
  totLe  : D.dr.TotLe n
  opens  : L₀.Opens D.no
  slots  : L₀.maxBatchSize = 2 ^ D.ax.depthReq
  fmt    : L₀.onlineBatch.ann.Fmt
  /-- the hiding condition: offline reads + links' reads ≤ b;
  a link's reads + sessions' reads ≤ b -/
  budget : Budget D.p (D.nums M κ₀ n)

end Compile.Batch
