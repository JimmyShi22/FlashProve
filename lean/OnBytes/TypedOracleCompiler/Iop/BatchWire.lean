-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Iop/BatchWire.lean: a form of Iop/BatchWire.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Iop/BatchWire.lean, comments apart: definitions: `WireRB`, `QueryLayout`,
`WireRB.OKG`, `WireRB.OK`, `RoundsQueryLayout.DepthLe`, `QueryLayout.OKG`, `QueryLayout.OK`; proofs alone: `QueryLayout.OK.toG`;
new here: `BatchProtocolWithLeafBody`, `BatchProtocolWithLeafBody.batT`, `BatchProtocolWithLeafBody.batL`, `maxRt`. Every other declaration has that file's text.

Where the head below speaks of the two trees of a round and of the flags `has0`, `hasJ`: here each
of the two components of a round has a list of trees. `depth0` and `depthJ` are the lists of their
depths ([]: no tree, no root is sent and none is hashed), `tree p` is the number of the tree in
which a position stands, and `posAt0`, `posAtJ` take the number of a tree and the number of a leaf.
The scope of the verifier over these wires: at most `maxRt` = 2 trees a component (see `maxRt`).
Where the head below says that a wire has the depth of the request tree (`depthReq`, with the law
`slots`): here it has three depths, `depthReqT`, `depthReqL`, `depthReq`, and the law is for Batch's
alone.

The rest of this head is the head of Iop/BatchWire.lean, to be read with these changes; the files
that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name, this
folder's.

Iop/BatchWire.lean: the wire of an interface with batches, that is of a `BatchProtocolWithLeafBody` (this file):
what layer 1 (the compiler, Compile/) needs beside `BatchProtocolWithLeafBody` in order to write down the compiled batch
verifier as a term. Data, and its laws.

A round differs from `WireR` (Iop/Wire.lean). The prover message of a round is the
pair of the shared and the slot's own component, and each has a Merkle root and a role of its own.
So a round has two trees: the positions with own p = false are in the tree of the shared component,
those with own p = true in the tree of the slot's component. Besides, a wire has the depth of the
request tree (`depthReq`, with the law `slots`).
A root only where something is committed: the flags `has0` and `hasJ` say whether a component has a
tree at all. A component without oracle positions needs none; then no root is sent and none is
hashed. The law is one-sided: a flag may be false only if the component has no position. (With both
flags true in every round every sent component has a root, over padding leaves if need be. The
theorems of layer 1 are for every lawful wire, so they cover that case too.)

Limits: only what the verifier needs is here (no enumerations of coins, no decision of the withheld
set), but for: (1) the records of the tests (`GrW`: `gr0`, `grJ`), which the honest prover of layer
1 reads, with `pass` and `zero`, which hypotheses of layer 1 read (Compile/Batch/SpecFit.lean); (2)
`place` and `QueryLayout.depth`, which the laws tie to what the verifier reads (`posAt0`, `posAtJ`;
`ext.depth`).
Terms: lean/GLOSSARY.md: wire, interface, layer, batch IOP, slot, request tree, test bits (proof of
work), withheld set.

-/
import Iop.Batch
import Iop.Wire

namespace TypedOracleCompiler.Iop
open _root_.Iop Prob

/-- Here: the interface of the library, and beside it the type of the body of a leaf of a tree over
oracles (what a leaf holds beside its salt) and the annotations of Test and of Link. The files of
this folder never look into a body: they write one with the functions emb.. and read one with the
functions prj.. of the wire (QueryLayout). This record extends the library's BatchProtocol: every
field and every notion of BatchProtocol is reached through it. -/
structure BatchProtocolWithLeafBody (I X : Type) extends _root_.Iop.BatchProtocol I X where
  Bd : Type
  /-- Here: the annotation of Test's rounds, and of Link's: which rounds are shared -/
  annT : RoundSplits toBatchProtocol.offline.shape
  annL : RoundSplits toBatchProtocol.link.shape

/-- Here: Test, and Link, with their annotations -/
def BatchProtocolWithLeafBody.batT {I X : Type} (L : BatchProtocolWithLeafBody I X) : BatchInteractiveOracleProof Unit (oneExternalString L.wordLength L.Symbol) := ⟨L.offline, L.annT⟩
def BatchProtocolWithLeafBody.batL {I X : Type} (L : BatchProtocolWithLeafBody I X) : BatchInteractiveOracleProof Unit (twoExternalStrings L.wordLength L.Symbol) := ⟨L.link, L.annL⟩

/-- Here: at most this many roots of one query count as occurring (`rootFields`,
Compile/Batch/Events.lean), and the verifier rejects a component with more trees (`takeRt`,
Compile/Batch/Verifier.lean). The scope: wires with at most maxRt = 2 trees a component; at more
this verifier rejects everything, while the programs' byte format has no such cap (its limit is 2^16
trees a chain; no shipped setting sends more than two roots in a round). The types are general in
the number of roots; the verifier stops at maxRt (so does the test ok on the description of a
format, which is not in this folder). Its value is used in Compile/Batch/Hash.lean alone: 1 ≤ maxRt
in three counts (3 ≤ maxRt + 2), and maxRt ≤ 2 in the sum of `hashEvents` (`rts_sum_range_le`). -/
def maxRt : ℕ := 2

/-- A round with a test ("grinding", proof of work), as layer 1 sees it. C: the verifier messages of
the round; P: the plain part that the Fiat-Shamir query of the round contains (a slot's in a local
round, the shared one in a shared round). The plain part ends in a nonce, which stands for a number,
and the verifier message has b test bits. The honest prover of layer 1 tries the nonces 0, 1, 2, ..,
one query each, until all test bits of the answer are 0. Data only. Nothing here, and no hypothesis
of layer 1, says that the verifier rejects where a test bit is 1: that is how the interface with
tests is built (Iop/Grind.lean: `InteractiveOracleProof.grind`). What layer 1 asks is the other direction: where all
test bits are 0 the verifier accepts the honest prover, with any numbers written in as nonces, for a
valid input and outside the withheld set (Compile/Batch/SpecFit.lean: `GrFit.acc`). -/
structure GrW (C P : Type) where
  /-- the number of test bits -/
  b : ℕ
  /-- the test bits of a verifier message -/
  tst : C → Fin b → Bool
  /-- the verifier message with other test bits (tst and set are a lens: GrW.OK) -/
  set : (Fin b → Bool) → C → C
  /-- the honest prover tries the nonces 0, .., more: at most more + 1 tries -/
  more : ℕ
  /-- the plain part with the nonce for the number k written over its nonce -/
  put : ℕ → P → P
  /-- the number for which the nonce of a plain part stands -/
  get : P → ℕ

/-- the test: all test bits are 0 -/
def GrW.ok {C P : Type} (g : GrW C P) (c : C) : Bool := decide (g.tst c = fun _ => false)

/-- One round of a batch IOP: its oracle is a string. Here: the depths of the trees of its two
components; in which tree of its component a position stands, and where among that tree's leaves;
how K blocks of lam bits give a verifier message (of one slot, in a local round). -/
structure WireRB (lam K : ℕ) (r : Round) (a : RAnn r) where
  pt : r.IsPoint
  /-- the depths of the trees over the shared component m_0, in the order in which their roots are
  sent. []: nothing is committed for it, no root is sent and the queries of the round hold no root
  for it -/
  depth0 : List ℕ
  /-- the same for a slot's component m_j -/
  depthJ : List ℕ
  /-- the number of the tree of its component in which a position stands -/
  tree : r.Pos → ℕ
  place : r.Pos → ℕ
  /-- the position at (number of the tree, number of the leaf) -/
  posAt0 : ℕ → ℕ → Option r.Pos
  posAtJ : ℕ → ℕ → Option r.Pos
  chal : (Fin K → Dig lam) → r.Chal
  /-- are the opened leaves of a tree over the shared component checked together, in one walk over a
  pruned set of paths (true), or each along a path of its own (false)? One flag for all trees of the
  component. A matter of the format of proof strings only: no law of a wire speaks of it. (The
  library's Iop/BatchWirePr.lean sets it for the library's wire; `ofRB`, OnBytes/TypedOracleCompiler/Tagged.lean,
  carries that flag over.) -/
  pr0 : Bool := false
  /-- the same for the trees over a slot's component -/
  prJ : Bool := false
  /-- has the Fiat-Shamir query of a shared round, formats (F4) and (F5), a test? none: no, the
  round has no test. Read in shared rounds only. -/
  gr0 : Option (GrW r.Chal a.P0) := none
  /-- the same for the Fiat-Shamir query of a slot in a local round, formats (F1), (F2), (F3). Read
  in local rounds only. (The query to g in the joining round never has a test: its answer is no
  verifier message.) -/
  grJ : Option (GrW r.Chal a.Pj) := none

def RoundsQueryLayout (lam K : ℕ) : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => WireRB lam K r a × RoundsQueryLayout lam K s A

structure ProtocolQueryLayout (lam K : ℕ) {X : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof X E) where
  sh : RoundsQueryLayout lam K Q.loc.shape Q.ann
  ext : WireE E
  decO : DecidableEq (OPos Q.loc.shape)
  /-- the verifier of one slot opens at most this many positions, external ones included, in trees
  of at most the depth `maxDepth` (the request tree is not counted here: its depth is
  QueryLayout.depthReq; here: by the protocol, `QueryLayout.dReq`) -/
  nOpen : ℕ
  maxDepth : ℕ

structure QueryLayout (lam : ℕ) {I X : Type} (L : BatchProtocolWithLeafBody I X) where
  K : ℕ
  T : ProtocolQueryLayout lam K L.batT
  Lk : ProtocolQueryLayout lam K L.batL
  B : ProtocolQueryLayout lam K L.onlineBatch
  /-- depth of the tree over an encoded index -/
  depth : ℕ
  /-- depth of a request tree (here: of Batch's, the session's): there are 2^depthReq slots -/
  depthReq : ℕ
  /-- Here: the depth of a request tree of Test, and of Link; no law of a wire speaks of them. -/
  depthReqT : ℕ
  depthReqL : ℕ
  /-- Here: how a symbol is written into the body of a leaf, and read back: a symbol of an encoded
  index (E), of a prover oracle of Test (T), Link (L), Batch (B) -/
  embE : L.Symbol → L.Bd
  prjE : L.Bd → Option L.Symbol
  embT : (p : OPos L.offline.shape) → OSym L.offline.shape p → L.Bd
  prjT : (p : OPos L.offline.shape) → L.Bd → Option (OSym L.offline.shape p)
  embL : (p : OPos L.link.shape) → OSym L.link.shape p → L.Bd
  prjL : (p : OPos L.link.shape) → L.Bd → Option (OSym L.link.shape p)
  embB : (p : OPos L.onlineBatch.loc.shape) → OSym L.onlineBatch.loc.shape p → L.Bd
  prjB : (p : OPos L.onlineBatch.loc.shape) → L.Bd → Option (OSym L.onlineBatch.loc.shape p)

/-! ## The laws -/

/-- tst and set are a lens: the verifier messages are the pairs (a verifier message with test bits
0, test bits) -/
structure GrW.OK {C P : Type} (g : GrW C P) : Prop where
  tst_set : ∀ z c, g.tst (g.set z c) = z
  set_tst : ∀ c, g.set (g.tst c) c = c
  set_set : ∀ z z' c, g.set z (g.set z' c) = g.set z c
  /-- the nonces that the honest prover tries are read back: so they differ from each other -/
  get_put : ∀ k α, k ≤ g.more → g.get (g.put k α) = k

/-- The laws of the wire of a round that may have a test. The laws of WireRB.OK on trees, places and
verifier messages, and that the records of the tests are lenses. chal_unif is about the whole
verifier message, test bits included. -/
structure WireRB.OKG {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop where
  place_lt0 : ∀ p, a.own p = false → ∃ d, w.depth0[w.tree p]? = some d ∧ w.place p < 2 ^ d
  place_ltJ : ∀ p, a.own p = true → ∃ d, w.depthJ[w.tree p]? = some d ∧ w.place p < 2 ^ d
  posAt0_place : ∀ p, a.own p = false → w.posAt0 (w.tree p) (w.place p) = some p
  posAtJ_place : ∀ p, a.own p = true → w.posAtJ (w.tree p) (w.place p) = some p
  place_posAt0 : ∀ k j p, w.posAt0 k j = some p → a.own p = false ∧ w.tree p = k ∧ w.place p = j
  place_posAtJ : ∀ k j p, w.posAtJ k j = some p → a.own p = true ∧ w.tree p = k ∧ w.place p = j
  no0 : ∀ k, w.depth0.length ≤ k → ∀ j, w.posAt0 k j = none
  noJ : ∀ k, w.depthJ.length ≤ k → ∀ j, w.posAtJ k j = none
  chal_unif : (unif (Fin K → Dig lam)).map w.chal = unif r.Chal
  gr0_ok : ∀ g, w.gr0 = some g → g.OK
  grJ_ok : ∀ g, w.grJ = some g → g.OK

/-- The laws of the wire of a round without a test. (The last two clauses say that it has none:
every statement that assumes W.OK is about the scheme without tests.) -/
structure WireRB.OK {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop where
  place_lt0 : ∀ p, a.own p = false → ∃ d, w.depth0[w.tree p]? = some d ∧ w.place p < 2 ^ d
  place_ltJ : ∀ p, a.own p = true → ∃ d, w.depthJ[w.tree p]? = some d ∧ w.place p < 2 ^ d
  posAt0_place : ∀ p, a.own p = false → w.posAt0 (w.tree p) (w.place p) = some p
  posAtJ_place : ∀ p, a.own p = true → w.posAtJ (w.tree p) (w.place p) = some p
  place_posAt0 : ∀ k j p, w.posAt0 k j = some p → a.own p = false ∧ w.tree p = k ∧ w.place p = j
  place_posAtJ : ∀ k j p, w.posAtJ k j = some p → a.own p = true ∧ w.tree p = k ∧ w.place p = j
  /-- Here: no position stands at a number beyond the list of trees (so a component without a tree
  has no oracle position) -/
  no0 : ∀ k, w.depth0.length ≤ k → ∀ j, w.posAt0 k j = none
  noJ : ∀ k, w.depthJ.length ≤ k → ∀ j, w.posAtJ k j = none
  /-- uniform blocks give a uniform verifier message -/
  chal_unif : (unif (Fin K → Dig lam)).map w.chal = unif r.Chal
  /-- the round has no test -/
  gr0_none : w.gr0 = none
  grJ_none : w.grJ = none

theorem WireRB.OK.toG {lam K : ℕ} {r : Round} {a : RAnn r} {w : WireRB lam K r a} (h : w.OK) :
    w.OKG :=
  ⟨h.place_lt0, h.place_ltJ, h.posAt0_place, h.posAtJ_place, h.place_posAt0, h.place_posAtJ, h.no0,
    h.noJ, h.chal_unif, fun g e => (by rw [h.gr0_none] at e; cases e),
    fun g e => (by rw [h.grJ_none] at e; cases e)⟩

def RoundsQueryLayout.OKG {lam K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) => w.OKG ∧ RoundsQueryLayout.OKG s A W

def RoundsQueryLayout.OK {lam K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) => w.OK ∧ RoundsQueryLayout.OK s A W

def RoundsQueryLayout.DepthLe {lam K : ℕ} (d : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, W) => ((∀ e ∈ w.depth0, e ≤ d) ∧ ∀ e ∈ w.depthJ, e ≤ d) ∧
      RoundsQueryLayout.DepthLe d s A W

structure ProtocolQueryLayout.OK {lam K : ℕ} {X : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof X E} (wq : ProtocolQueryLayout lam K Q) : Prop where
  sh : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh
  ext : wq.ext.OK
  opens : ∀ x ρ pl, (Q.loc.reads x ρ pl).card + (Q.loc.extReads x ρ).card ≤ wq.nOpen
  depth : RoundsQueryLayout.DepthLe wq.maxDepth Q.loc.shape Q.ann wq.sh

theorem RoundsQueryLayout.OK.toG {lam K : ℕ} :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A}, RoundsQueryLayout.OK s A W → RoundsQueryLayout.OKG s A W
  | [], _, _, _ => trivial
  | _ :: _, (_, _), (_, _), h => ⟨h.1.toG, RoundsQueryLayout.OK.toG h.2⟩

structure ProtocolQueryLayout.OKG {lam K : ℕ} {X : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof X E} (wq : ProtocolQueryLayout lam K Q) : Prop where
  sh : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh
  ext : wq.ext.OK
  opens : ∀ x ρ pl, (Q.loc.reads x ρ pl).card + (Q.loc.extReads x ρ).card ≤ wq.nOpen
  depth : RoundsQueryLayout.DepthLe wq.maxDepth Q.loc.shape Q.ann wq.sh

theorem ProtocolQueryLayout.OK.toG {lam K : ℕ} {X : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof X E}
    {wq : ProtocolQueryLayout lam K Q} (h : wq.OK) : wq.OKG :=
  ⟨h.sh.toG, h.ext, h.opens, h.depth⟩

/-- The laws of a wire whose rounds may have tests: those of QueryLayout.OK, with OKG in the place of OK
for the three protocols. -/
structure QueryLayout.OKG {lam : ℕ} {I X : Type} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L) : Prop where
  T : W.T.OKG
  Lk : W.Lk.OKG
  B : W.B.OKG
  fits : L.wordLength ≤ 2 ^ W.depth
  slots : L.maxBatchSize = 2 ^ W.depthReq
  extDepth : W.T.ext.depth = W.depth ∧ W.Lk.ext.depth = W.depth ∧ W.B.ext.depth = W.depth
  depthT : W.depth ≤ W.T.maxDepth
  depthL : W.depth ≤ W.Lk.maxDepth
  depthB : W.depth ≤ W.B.maxDepth
  extT : ∀ p, W.T.ext.which p = 0 ∧ W.T.ext.leaf p = p.val
  extB : ∀ p, W.B.ext.which p = 0 ∧ W.B.ext.leaf p = p.val
  extL : (∀ p, W.Lk.ext.which (.inl p) = 0 ∧ W.Lk.ext.leaf (.inl p) = p.val) ∧
         (∀ p, W.Lk.ext.which (.inr p) = 1 ∧ W.Lk.ext.leaf (.inr p) = p.val)
  /-- Here: what is written into a body is read back -/
  prjE_emb : ∀ s, W.prjE (W.embE s) = some s
  prjT_emb : ∀ p a, W.prjT p (W.embT p a) = some a
  prjL_emb : ∀ p a, W.prjL p (W.embL p a) = some a
  prjB_emb : ∀ p a, W.prjB p (W.embB p a) = some a

structure QueryLayout.OK {lam : ℕ} {I X : Type} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L) : Prop where
  T : W.T.OK
  Lk : W.Lk.OK
  B : W.B.OK
  fits : L.wordLength ≤ 2 ^ W.depth
  /-- the number of slots is a power of two (the request tree is the perfect binary tree with
  exactly N leaves) -/
  slots : L.maxBatchSize = 2 ^ W.depthReq
  extDepth : W.T.ext.depth = W.depth ∧ W.Lk.ext.depth = W.depth ∧ W.B.ext.depth = W.depth
  depthT : W.depth ≤ W.T.maxDepth
  depthL : W.depth ≤ W.Lk.maxDepth
  depthB : W.depth ≤ W.B.maxDepth
  /-- where the external positions stand: position p of an encoding is leaf p of its tree; parent
  first, then child -/
  extT : ∀ p, W.T.ext.which p = 0 ∧ W.T.ext.leaf p = p.val
  extB : ∀ p, W.B.ext.which p = 0 ∧ W.B.ext.leaf p = p.val
  extL : (∀ p, W.Lk.ext.which (.inl p) = 0 ∧ W.Lk.ext.leaf (.inl p) = p.val) ∧
         (∀ p, W.Lk.ext.which (.inr p) = 1 ∧ W.Lk.ext.leaf (.inr p) = p.val)
  /-- Here: what is written into a body is read back -/
  prjE_emb : ∀ s, W.prjE (W.embE s) = some s
  prjT_emb : ∀ p a, W.prjT p (W.embT p a) = some a
  prjL_emb : ∀ p a, W.prjL p (W.embL p a) = some a
  prjB_emb : ∀ p a, W.prjB p (W.embB p a) = some a

theorem QueryLayout.OK.toG {lam : ℕ} {I X : Type} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} (h : W.OK) : W.OKG :=
  ⟨h.T.toG, h.Lk.toG, h.B.toG, h.fits, h.slots, h.extDepth, h.depthT, h.depthL,
    h.depthB, h.extT, h.extB, h.extL, h.prjE_emb, h.prjT_emb, h.prjL_emb, h.prjB_emb⟩

/-! ## Rounds with a test: what the verifier randomness of a local transcript says of them -/

/-- are all test bits of this verifier message 0? The kind of the round says which record is read.
true in a round without a test -/
def WireRB.pass {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) (c : r.Chal) : Bool :=
  match a.kind with
  | .lo => match w.grJ with
    | none => true
    | some g => g.ok c
  | .sh => match w.gr0 with
    | none => true
    | some g => g.ok c

/-- the verifier message with all test bits set to 0; itself in a round without a test -/
def WireRB.zero {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) (c : r.Chal) : r.Chal :=
  match a.kind with
  | .lo => match w.grJ with
    | none => c
    | some g => g.set (fun _ => false) c
  | .sh => match w.gr0 with
    | none => c
    | some g => g.set (fun _ => false) c

/-- all tests of a local transcript are passed -/
def RoundsQueryLayout.pass {lam K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Rho s → Bool
  | [], _, _, _ => true
  | _ :: s, (_, A), (w, W), (c, ρ) => w.pass c && RoundsQueryLayout.pass s A W ρ

/-- the verifier randomness with all test bits set to 0 -/
def RoundsQueryLayout.zero {lam K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Rho s → Rho s
  | [], _, _, _ => ()
  | _ :: s, (_, A), (w, W), (c, ρ) => (w.zero c, RoundsQueryLayout.zero s A W ρ)

end TypedOracleCompiler.Iop
