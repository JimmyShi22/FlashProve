-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Chain.lean: the last chain of a proof file as it is seated: K14's second part,
the taken trees' sources, the request's own proximity test (an argument), and the chain's end.
Definitions with code. No theorem.

This chain has three names: "the last chain" and "the third chain" in these files, "the second
chain" in the format (Johnson/Desc/Block.lean: the field `second`; the refusal "the second chain's
start") and in the program `verify-on-bytes`.

The end is the chains' ends' one text (Johnson/Desc/ChainEnd.lean) at this chain: a block without a
round that asks that a proximity test has begun on every group and that every sampled message names
a group that is there and is tested.

Main names: `end₃`, `ownAt`, `lastChainWithOwnTest`; `Last`, `last`: the start and the chain made of one
p.

Limits. A chain cannot be made without a last block (Johnson/Desc/Block.lean): so this chain
cannot be made without its end; the end is handed the very blocks that are laid in front of it (one
list, spent twice). ONE p BY THE MAKING, NOT BY A TEST: `last` makes the start and the chain of one
p, but `start₃F`, `startAtEnds` and `lastChainWithOwnTest` stay exported, each with a p of its own, and a
description takes start and chain as two fields: nothing refuses the start of one `last` beside the
chain of another. `batchLinearConstraintsSecondPart` never asks that the statement's codes are p's. Nothing on soundness or
on hiding.
-/
import Johnson.Desc.Third.TakenSources
import Johnson.Desc.ChainEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third

/-- **The third chain's last block.** inFront: the blocks that are laid in front of it. -/
def end₃ {Cl : Type} (inFront : List (Block S₃ Cl)) : Block S₃ Cl :=
  ChainEnd.chainEnd 3 3 false (inFront.flatMap (·.rounds)) fun s => ChainEnd.untestedL s.st

/-- The own test's block at its place in this chain. -/
def ownAt {Cl : Type} (own : Block S₃ Cl) : Block S₃ Cl :=
  { own with place := { own.place with chain := 3, link := none, piece := 2 } }

/-- **The third chain**: K14's second part is its first block (a working block without a round);
behind it the taken trees' sources and the own test's block; the chain's end is its last. -/
def lastChainWithOwnTest {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) : Chain S₃ Cl :=
  let f : Block S₃ Cl := batchLinearConstraintsSecondPart p
  let b : List (Block S₃ Cl) := [takenSources own, ownAt own]
  { first := f, front := [], links := [], back := b, last := end₃ (f :: b) }

/-- The last chain as a file's description takes it: its start and its blocks. -/
structure Last (XiPub S₁ S₂ Cl : Type) where
  start : XiPub → S₁ → S₂ → Except String S₃
  chain : Chain S₃ Cl

/-- **The last chain, made of one p**: the start and the blocks are handed the same public
parameters, so that a description cannot give them two. -/
def last {XiPub S₁ S₂ Cl : Type} (p : P₁₄) (first : S₁ → Option FirstEnd₃)
    (shared : S₂ → SharedOut) (own : Block S₃ Cl) : Last XiPub S₁ S₂ Cl :=
  { start := start₃F p first shared, chain := lastChainWithOwnTest p own }

end VerifiableInference.Desc.Third
