-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Star.lean: the compiled scheme (C, P, V), `argB`. (Words of this library:
lean/GLOSSARY.md.)

C encodes the index once (the first encoding, under cm) and M + 1 more times (the copies), with
fresh coins, keeps all in isk, and runs Test and, for each copy, Link once. P places a batch of at
most maxBatchSize requests in the maxBatchSize slots by a sampled placement and proves it by one execution of Batch on a
uniform copy, sampled for each batch. V rejects a proof string `none` (no proof).

C and P are first token programs (`Cp`, `Pp`); the scheme has `realQ` of what `erase`
(Compile/Star.lean) makes of them.

* P is given a list of requests. Request number a is in slot σ a for a sampled permutation σ of the
  slots (uniform if `WP.perm` has `Enum.OK`, Iop/Wire.lean). A request beyond the maxBatchSize-th gets no slot,
  and a proof without a slot's proof string.
* `Pp` has an argument fr: for which requests a proof string is made at all. The scheme has fr =
  true everywhere (P is not told to whom a request belongs); the analysis of privacy uses the
  program that makes proof strings, and so reveals, only for the adversary's own requests.
* All trees over prover messages are token trees, for Test and Link too; for the trees over encoded
  indices: Compile/Batch/TokTree.lean.
* V rejects what fails the strict-format check (`verifyOneProtocol`, Compile/Batch/Verifier.lean; the field
  `leaf` of a proof must be the number of a copy), so it takes the parameters p.

Test and Link: tying further masked copies of one commitment to the first by links. The tree of
linked encodings of the index is after the work that this protocol builds on (lean/CREDITS.md,
"Further work").
-/
import Compile.Batch.Prover
import Compile.Star
import ZKCP.Gen

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

structure IVK (lam : ℕ) (L : BatchProtocol I X) where
  cm : Dig lam
  piT : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))

/-- one encoding as the prover keeps it -/
structure Node (lam : ℕ) (L : BatchProtocol I X) where
  r : L.EncodingRandomness
  tree : TreeH lam

structure LeafRec (lam : ℕ) (L : BatchProtocol I X) where
  node : Node lam L
  piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))

/-- isk with tokens in the place of secret strings -/
structure IskH (lam : ℕ) (L : BatchProtocol I X) where
  i : I
  root : Node lam L
  leaves : List (LeafRec lam L)

/-- isk: the tokens, and the strings that they denote -/
abbrev ISK (lam : ℕ) (L : BatchProtocol I X) : Type := IskH lam L × List Bits

structure Prf (lam : ℕ) (L : BatchProtocol I X) where
  leaf : ℕ
  cm : Dig lam
  piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))
  piB : Option (OneProtocolProof lam L.onlineBatch)

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- a fresh encoding of i and its salted tree -/
def nodeP' (i : I) : St lam W.K L (Node lam L) :=
  (drawT WP.ri).bind fun r =>
  (commitE p.sMT W.depth fun j =>
      if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true) else (none, false)).bind fun t =>
  pure ⟨r, t⟩

/-- the compiled Test on the first encoding -/
def proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    St lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))) :=
  (proveB p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
      (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [tree] (i, r)
      (fun _ => true) [some ()]).bind fun l =>
  pure (l.headD none)

/-- the compiled Link between the first encoding and a copy -/
def proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    St lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))) :=
  (proveB p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
      (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [root, tree]
      (i, r₀, r) (fun _ => true) [some ()]).bind fun l =>
  pure (l.headD none)

def leavesC (i : I) (root : Node lam L) : ℕ → St lam W.K L (List (LeafRec lam L))
  | 0 => pure []
  | n + 1 =>
      (nodeP' W WP p i).bind fun nd =>
      (proveLk W WP p root.tree nd.tree i root.r nd.r).bind fun π =>
      (leavesC i root n).bind fun rest => pure (⟨nd, π⟩ :: rest)

/-- the committer, as a token program -/
def Cp (i : I) : St lam W.K L (IVK lam L × IskH lam L) :=
  (nodeP' W WP p i).bind fun root =>
  (proveT W WP p root.tree i root.r).bind fun πT =>
  (leavesC W WP p i root (p.M + 1)).bind fun ls =>
  pure (⟨root.tree.root, πT⟩, ⟨i, root, ls⟩)

/-- what the slots hold: request number a is in slot σ a -/
def slotsOfReq {N : ℕ} (σ : Equiv.Perm (Fin N)) (xs : List X) : List (Option X) :=
  (List.finRange N).map fun j => xs[(σ.symm j).val]?

/-- the flags of the requests, as flags of the slots -/
def slotFlags {N : ℕ} (σ : Equiv.Perm (Fin N)) (fr : ℕ → Bool) : ℕ → Bool :=
  fun s => if h : s < N then fr (σ.symm ⟨s, h⟩).val else false

/-- the batch, once the copy j and the placement σ are sampled -/
def PpJ (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    St lam W.K L (List (Prf lam L)) :=
  match k.leaves[j]? with
  | none => pure (xs.map fun _ => ⟨j, default, none, none⟩)
  | some lf =>
      (proveB p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun πs =>
      pure ((List.range xs.length).map fun a =>
        ⟨j, lf.node.tree.root, lf.piL, if h : a < L.maxBatchSize then πs.getD (σ ⟨a, h⟩).val none else none⟩)

/-- the prover, as a token program: a uniform copy, a sampled placement (uniform if `WP.perm` has
`Enum.OK`, Iop/Wire.lean), one execution of Batch -/
def Pp (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : St lam W.K L (List (Prf lam L)) :=
  Step.sample p.M fun j => (drawT WP.perm).bind fun σ => PpJ W WP p k fr xs j.val σ

/-- a list cut or filled up to the length n -/
def fitLen {β : Type} (d : β) (n : ℕ) (l : List β) : {l' : List β // l'.length = n} :=
  ⟨(l ++ List.replicate n d).take n, by simp⟩

/-- what `erase` makes of the committer's and the prover's programs, queries to the ghost names
included: objects of the analysis (Compile/Batch/SpecGhost.lean: argBT), not algorithms of the
scheme -/
def Ctok (i : I) : TypedOracleComputation lam W.K L (IVK lam L × ISK lam L) :=
  (erase (Cp W WP p i) []).bind fun o => pure (o.1.1, (o.1.2, o.2))
def Ptok (k : ISK lam L) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (Prf lam L) b) :=
  (erase (Pp W WP p k.1 (fun _ => true) (b.map Prod.fst)) k.2).bind fun o =>
    pure (fitLen ⟨0, default, none, none⟩ b.length o.1)

/-- C, P, V as oracle algorithms. C and P are `Ctok` and `Ptok` with every query to a ghost name
`fbw t k` turned into the query to `fb t` (Compile/Batch/Oracles.lean: realQ): every proof-of-work
attempt is a query to the Fiat-Shamir oracle fb t of its protocol. So no algorithm of the scheme
queries a ghost name. -/
def C (i : I) : TypedOracleComputation lam W.K L (IVK lam L × ISK lam L) := realQ (Ctok W WP p i)
def P (k : ISK lam L) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (Prf lam L) b) :=
  realQ (Ptok W WP p k b)
/-- V, with the strict-format check (Compile/Batch/Verifier.lean: verifyOneProtocol). It checks first,
without a query, that the field leaf is the number of a copy (after the match on the three proof
strings: if one is `none`, V returns false); it uses that field for nothing else. So an accepted
proof stays accepted if that number is replaced by any other of the M + 1 numbers of copies. In the
scheme of Compile/Batch/StarK.lean this check is idle: `reK` writes 0 into that field. What else of
a key or a proof can be changed freely (the header of Compile/Batch/Verifier.lean):
* the plain part of a component that is not sent;
* in Test and Link, whose chains do not join: the fields rtreq (any digest) and slot (any number
  below 2^depthReq);
* in a tree for which the wire record asks for pruned Merkle paths: the digests of the paths that
  the verifier does not read. -/
def V (v : IVK lam L) (x : X) (π : Prf lam L) : TypedOracleComputation lam W.K L Bool :=
  match v.piT, π.piL, π.piB with
  | some πT, some πL, some πB =>
      if π.leaf ≤ p.M then do
        let a ← vTS W p.sMT p.sFS v.cm πT
        let b ← vLS W p.sMT p.sFS v.cm π.cm πL
        let c ← vBS W p.sMT p.sFS π.cm x πB
        pure (a && b && c)
      else pure false
  | _, _, _ => pure false

/-- The compiled scheme. -/
def argB : ZKCP.Gen.Arg (spec lam W.K L) I X Unit (IVK lam L) (ISK lam L) (Prf lam L) where
  C := C W WP p
  P := P W WP p
  V := V W p

end Compile.Batch
