-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookOwnFresh.lean: the ninth of the files that compute the book of
coins (`ProverCoinCounts`, Honest/Frame.lean): the fresh table that a fold sends itself, in its round "FOLD
epsilon". The library's list of sendings does not hold it (the head of Johnson/G/Sends.lean: an
oracle message whose root goes in an entry of another name is not listed), so it is read from the
description: the round's declared root, the mask words that the sub-protocol declares for that
round's oracle message, the rounds "FOLD round" after it. From public data alone. It names no
prover's side. Executable definitions, and tests at synthetic lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

Its coins are the fold's own: the hiding polynomial's 2k + 1 coefficients, then the rows' random
tails: as a fresh table that is sent ahead has them (Honest/BookRows.lean).

  `OwnFresh`, `ownFreshIn`   such a fold: its part, the part that sends what it leaves, k, the rows
  `OwnFresh.row`   the row of the fold's part
  `OwnFresh.carry`   the entry by which the part after it carries the whole table

Limits.
  * The mask code's tail is for the caller to supply: the description does not hold it.
  * A row of the table is taken to be three mask words in a symbol.
  * The fold's part is taken to have no other coin.
  * Where the sub-protocol declares no oracle message at the round, the table counts as having no
    row; a remainder of the division by three is dropped.
  * An empty list from `ownFreshIn` says less than "no fold sends such a table": the function
    silently drops a fold at round 0, and one after which it finds nothing.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl : Type}

/-- A fold that sends its own fresh table. -/
structure OwnFresh where
  /-- the fold's part -/
  fold : Addr
  /-- the part that holds the first round "SEND seed" after it -/
  behind : Addr
  /-- the fold's rounds "FOLD round" -/
  k : Nat
  /-- the table's rows -/
  rows : Nat
  deriving DecidableEq

/-- The mask words that a chain's sub-protocols declare, round by round. -/
def maskWordsByRound (bs : List (Block S Cl)) : List Nat :=
  bs.flatMap fun b => (List.range b.rounds.length).map fun i =>
    ((b.oracles.getD i []).flatMap (·.tenants)).foldl (fun n t => n + t.mask) 0

/-- **The folds of a chain that send their own fresh table.** -/
def ownFreshIn (bs : List (Block S Cl)) : List OwnFresh :=
  let l := planOf bs
  let words := maskWordsByRound bs
  ((l.flatMap (·.rounds)).zipIdx.filter fun r =>
    r.1.entry.name == "FOLD epsilon" && r.1.entry.roots != 0).filterMap fun r =>
    -- the round before it, so that `behindFold` finds this very fold
    if r.2 == 0 then none else
    (behindFold l (r.2 - 1)).bind fun pq => (foldBehind l (r.2 - 1)).map fun f =>
      ⟨pq.1, pq.2, f.2.2, words.getD r.2 0 / 3⟩

/-- **The row of the fold's part.** `tail`: the mask code's random tail. -/
def OwnFresh.row (o : OwnFresh) (tail : Nat) : Addr × Due :=
  (o.fold, ⟨0, 2 * o.k + 1 + o.rows * tail⟩)

/-- **The part after it carries the whole table**, as message 0 of the fold's part. -/
def OwnFresh.carry (o : OwnFresh) (tail : Nat) : Ahead :=
  ⟨carriedName o.fold 0 o.behind, o.fold, ⟨0, 0⟩, (o.row tail).2, o.behind, false⟩

/-! ### Tests at synthetic lists -/

-- a fold of two rounds, one row, a tail of 156: five coefficients and the tail
#guard (OwnFresh.row ⟨toyTo 0, toyTo 1, 2, 1⟩ 156).2 == ⟨0, 161⟩
#guard (OwnFresh.carry ⟨toyTo 0, toyTo 1, 2, 1⟩ 156).count == ⟨0, 161⟩ &&
  !(OwnFresh.carry ⟨toyTo 0, toyTo 1, 2, 1⟩ 156).once &&
  (OwnFresh.carry ⟨toyTo 0, toyTo 1, 2, 1⟩ 156).name == "message 0 of 1.2.3.0 to 1.2.3.1: carried"

end ProofFile.Honest
