-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchWire.lean: the wire of an interface with batches, that is of an `BatchProtocol` (Iop/Batch.lean):
what layer 1 (the compiler, Compile/) needs beside `BatchProtocol` in order to write down the compiled batch
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

namespace Iop
open Prob

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

/-- One round of a batch IOP: its oracle is a string; the depths of the two trees; where a position
is among the leaves of the tree of its component; how K blocks of lam bits give a verifier message
(of one slot, in a local round). -/
structure WireRB (lam K : ℕ) (r : Round) (a : RAnn r) where
  pt : r.IsPoint
  /-- the depth of the tree over the shared component m_0 -/
  depth0 : ℕ
  /-- the depth of the tree over a slot's component m_j -/
  depthJ : ℕ
  /-- is there a tree over the shared component at all? false: nothing is committed for it, no root
  is sent and the queries of the round hold no root for it -/
  has0 : Bool
  /-- the same for a slot's component -/
  hasJ : Bool
  place : r.Pos → ℕ
  posAt0 : ℕ → Option r.Pos
  posAtJ : ℕ → Option r.Pos
  chal : (Fin K → Dig lam) → r.Chal
  /-- are the opened leaves of the tree over the shared component checked together, in one walk over
  a pruned set of paths (true), or each along a path of its own (false)? A matter of the format of
  argument strings only: no law of a wire speaks of it. Set by Iop/BatchWirePr.lean: `setPr`. -/
  pr0 : Bool := false
  /-- the same for the tree over a slot's component -/
  prJ : Bool := false
  /-- has the Fiat-Shamir query of a shared round, formats (F4) and (F5) (`Head`,
  Compile/Batch/Oracles.lean), a test? none: no. Read in shared rounds only. -/
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
  QueryLayout.depthReq) -/
  nOpen : ℕ
  maxDepth : ℕ

structure QueryLayout (lam : ℕ) {I X : Type} (L : BatchProtocol I X) where
  K : ℕ
  T : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto L.offline)
  Lk : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto L.link)
  B : ProtocolQueryLayout lam K L.onlineBatch
  /-- depth of the tree over an encoded index -/
  depth : ℕ
  /-- depth of a request tree: there are 2^depthReq slots -/
  depthReq : ℕ

/-! ## The laws -/

/-- tst and set are a lens: the verifier messages are the pairs (a verifier message with test bits
0, test bits) -/
structure GrW.OK {C P : Type} (g : GrW C P) : Prop where
  tst_set : ∀ z c, g.tst (g.set z c) = z
  set_tst : ∀ c, g.set (g.tst c) c = c
  set_set : ∀ z z' c, g.set z (g.set z' c) = g.set z c
  /-- the nonces that the honest prover tries are read back: so they differ from each other -/
  get_put : ∀ k α, k ≤ g.more → g.get (g.put k α) = k

/-- The laws of the wire of a round that may have a test. The laws of `WireRB.OK` on trees, places
and verifier messages, and that the records of the tests meet `GrW.OK`. `chal_unif` is about the
whole verifier message, test bits included. -/
structure WireRB.OKG {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop where
  place_lt0 : ∀ p, a.own p = false → w.place p < 2 ^ w.depth0
  place_ltJ : ∀ p, a.own p = true → w.place p < 2 ^ w.depthJ
  posAt0_place : ∀ p, a.own p = false → w.posAt0 (w.place p) = some p
  posAtJ_place : ∀ p, a.own p = true → w.posAtJ (w.place p) = some p
  place_posAt0 : ∀ j p, w.posAt0 j = some p → a.own p = false ∧ w.place p = j
  place_posAtJ : ∀ j p, w.posAtJ j = some p → a.own p = true ∧ w.place p = j
  no0 : w.has0 = false → ∀ j, w.posAt0 j = none
  noJ : w.hasJ = false → ∀ j, w.posAtJ j = none
  chal_unif : (unif (Fin K → Dig lam)).map w.chal = unif r.Chal
  gr0_ok : ∀ g, w.gr0 = some g → g.OK
  grJ_ok : ∀ g, w.grJ = some g → g.OK

/-- The laws of the wire of a round without a test. (By the last two clauses every statement that
assumes W.OK is about the scheme without tests.) -/
structure WireRB.OK {lam K : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop where
  place_lt0 : ∀ p, a.own p = false → w.place p < 2 ^ w.depth0
  place_ltJ : ∀ p, a.own p = true → w.place p < 2 ^ w.depthJ
  posAt0_place : ∀ p, a.own p = false → w.posAt0 (w.place p) = some p
  posAtJ_place : ∀ p, a.own p = true → w.posAtJ (w.place p) = some p
  place_posAt0 : ∀ j p, w.posAt0 j = some p → a.own p = false ∧ w.place p = j
  place_posAtJ : ∀ j p, w.posAtJ j = some p → a.own p = true ∧ w.place p = j
  /-- a component without a tree has no oracle position -/
  no0 : w.has0 = false → ∀ j, w.posAt0 j = none
  noJ : w.hasJ = false → ∀ j, w.posAtJ j = none
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
  | _ :: s, (_, A), (w, W) => (w.depth0 ≤ d ∧ w.depthJ ≤ d) ∧ RoundsQueryLayout.DepthLe d s A W

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
structure QueryLayout.OKG {lam : ℕ} {I X : Type} {L : BatchProtocol I X} (W : QueryLayout lam L) : Prop where
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

structure QueryLayout.OK {lam : ℕ} {I X : Type} {L : BatchProtocol I X} (W : QueryLayout lam L) : Prop where
  T : W.T.OK
  Lk : W.Lk.OK
  B : W.B.OK
  fits : L.wordLength ≤ 2 ^ W.depth
  /-- the number of slots is a power of two (the request tree is the perfect binary tree with
  exactly maxBatchSize leaves) -/
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

theorem QueryLayout.OK.toG {lam : ℕ} {I X : Type} {L : BatchProtocol I X} {W : QueryLayout lam L} (h : W.OK) : W.OKG :=
  ⟨h.T.toG, h.Lk.toG, h.B.toG, h.fits, h.slots, h.extDepth, h.depthT, h.depthL,
    h.depthB, h.extT, h.extB, h.extL⟩

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

end Iop
