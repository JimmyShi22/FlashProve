-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Told.lean: what shares a leaf. For each of the proof file's three chains and
each tree that the chain sends, in the order of sending: the tree's log-length, the words of a
symbol, and its tenants, that is, the oracle messages that share its leaves. It is computed from the
planner's record alone, off the planner's list of sendings (Johnson/G/Sends.lean), from which the
declared rounds themselves cut the trees (`treesSent`, Johnson/G/RoundsOfPlan.lean). No proof's byte
is read.
Why. The tests on the plan ask what may share a tree and where a tree may be opened
(Johnson/Desc/BookPlan.lean). A block that does not know its trees' tenants needs this table to
answer them truly.
  `tenantOf`    an oracle message as it is announced, as a tenant
  `toldAt`      the trees of one sending, each with the number of its round
  `toldChain`   a chain's trees, in the order of `treesSent`, and compared with `treesSent` itself:
                as many trees, each with its depth and width; otherwise it refuses
  `toldOf`      the three chains
Who uses it. `pubBy` (Pub.lean) calls `toldOf`, so a refusal here means that no public part, and no
description, is returned. The table itself goes into the field `told`; the proof file's description
does not read that field, only test harnesses do.
Limit. A sending does not say which groups a message joins, so every tenant here has `groups := []`.
For a block that takes its tenants from this table, the clauses of BookPlan.lean on groups test
nothing.

-/
import Johnson.G.RoundsOfPlan
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Params
open Johnson.G (Sending ChainSends)
open Johnson.G.OfPlan (Made Sent treesSent ownMasks)

/-- A tree with its tenants. -/
abbrev Root : Type := VerifiableInference.Desc.Oracle

/-- An oracle message as it is announced, as a tenant: its main words are its main rows times their
degree, its mask words its mask rows times 3, and it is sampled if it has answers to a sample. -/
def tenantOf (n : OracleNotice) : VerifiableInference.Desc.SymbolComponent :=
  { main := n.shape.mainRows * n.shape.mainDeg, mask := n.shape.maskRows * 3
    degree := n.shape.mainDeg, sampled := n.shape.answers != 0, groups := [] }

/-- The trees into which these messages are put (the planner's `layTrees`), each with its tenants in
the order of their parts. -/
def rootsOfSent (codes : Codes) (sent : List OracleNotice) : Option (List Root) :=
  (layTrees codes sent.toArray).map fun L =>
    L.shapes.toList.zipIdx.map fun t =>
      let mine := (sent.zipIdx.filter fun y => L.tree.getD y.2 0 == t.2).mergeSort fun a b =>
        L.part.getD a.2 0 ≤ L.part.getD b.2 0
      { logLength := t.1.logN, words := t.1.mainWidth + t.1.maskWidth
        tenants := mine.map fun y => tenantOf y.1 }

/-- The trees of one sending, each with the number, from 0, of the round that sends it. `off`: how
many of the plan's entries are not rounds. -/
def toldAt (codes : Codes) (off : Nat) (x : Sending) : Option (List (Nat × Root)) :=
  (rootsOfSent codes x.sent).map fun l => l.map fun r => (x.entry - 1 - off, r)

/-- A chain's trees in the order of sending. `extra`: the trees that go in a round other than a
"SEND seed", as `treesSent` finds them; `held`: the one message that each of them holds. -/
def toldChain (at_ : String) (c : ChainSends) (P : Fmt.Plan) (extra : List Sent)
    (held : Option OracleNotice) : Except String (List Root) := do
  let off := P.entries.length - P.rounds.length
  let l ← (c.sends.mapM (toldAt c.codes off)).elim
    (.error (at_ ++ ": the oracle messages of a sending cannot be placed in trees")) .ok
  let more : List (Nat × Root) := extra.map fun t =>
    (t.round, { logLength := t.a, words := t.W, tenants := held.toList.map tenantOf })
  let mine := ((l.flatten ++ more).mergeSort fun a b => a.1 ≤ b.1).map (·.2)
  let theirs ← treesSent at_ c P extra
  if mine.map (fun r => (r.logLength, r.words)) != theirs.map fun t => (t.1.a, t.1.W) then
    throw (at_ ++ ": the tenants' table and the list of trees sent part")
  pure mine

/-- The three chains' trees with their tenants, from the planner's record. -/
def toldOf (m : Made) : Except String (List Root × List Root × List Root) := do
  let S := m.p.chains.made.sized.proof.batch.shape
  let P₁ := m.p.chains.proof.shared.given.plan
  let mask := S.testOmega.head?.map fun st => foldMaskNotice (ioppFoldShape st {})
  let t₀ ← toldChain "the tenants, first chain" m.proof.1 m.p.chains.proof.first.given.plan [] none
  let t₁ ← toldChain "the tenants, shared chain" m.proof.2.1 P₁
    (ownMasks m.proof.2.1.codes S P₁.rounds) mask
  let t₂ ← toldChain "the tenants, second chain" m.proof.2.2 m.p.chains.proof.second.given.plan []
    none
  pure (t₀, t₁, t₂)

/-- A list of trees, cut as the declared rounds send them: one list for each round. -/
def cutRoots : List Root → List Fmt.DeclaredRound → List (List Root)
  | _, [] => []
  | l, d :: ds => l.take d.entry.roots :: cutRoots (l.drop d.entry.roots) ds

end ProofFile
