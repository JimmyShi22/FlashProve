-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Chain1.lean: a key file's first chain. Definitions only, all computable; nothing is
proved here.

The chain: two sendings; a link for each lookup (Johnson/Desc/Key/Link.lean); the lookups' rows laid
onto the ranges' group; the proximity test on that group; the batching of the pending rows (the rows
on the table); the sending of W; the chain's end.

Main names.
  firstChain: the chain.
  enterRanges, leaveRanges: what the proximity test's seat reads of the chain's state and writes
    back.
  firstEndOk: the part of the file's last test that looks at this chain's last state.
  rootsBefore, rootsAt, batchRound, lastSendRound, groupsTold, pieces: where in the declared rounds
    the places lie; which groups a sending's messages join; the places' numbers.

Limits. The blocks of the sendings, the batching and the end are made elsewhere
(Johnson/Desc/Key/One.lean), the proximity test's in its seat's file (Johnson/Desc/Key/Ranges.lean).
The rounds' places are found by the declared rounds' names. Nothing on soundness.
`firstEndOk` lets off the last group by its position in the list. That the group let off is the own
test's (`groupOwn`, Johnson/Desc/Key/Source.lean) is asked nowhere in this file.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Ranges
import Johnson.Desc.ProofFile.Told

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-- The trees that the declared rounds send in front of round r. -/
def rootsBefore (D : List Fmt.DeclaredRound) (r : Nat) : Nat := (D.take r).foldl
    (fun n d => n + d.entry.roots) 0

/-- The trees that round r of D sends (0 where there is no such round). -/
def rootsAt (D : List Fmt.DeclaredRound) (r : Nat) : Nat := ((D[r]?).map (·.entry.roots)).getD 0

/-- The first round of the batching of the rows on the table: the first that is named "BAT-sigma"
(the list's length where none is). -/
def batchRound (D : List Fmt.DeclaredRound) : Nat := D.findIdx fun d => d.entry.name == "BAT-sigma"

/-- The first round of W's sending: the last round that is named "SEND seed" (0 where none is). -/
def lastSendRound (D : List Fmt.DeclaredRound) : Nat :=
    (((D.zipIdx.filter fun d => d.1.entry.name == "SEND seed").getLast?).map (·.2)).getD 0

/-- **What the ranges' test's seat reads of chain 1's state**: the statement's record, the group's
number and the message that holds the first fold's mask. Asked: no count of rows waits; all lookups
are laid; the ranges' group's test has not begun, and the group holds as many rows as the lookups
have laid. -/
def enterRanges (one : OneTime) (s : FirstState) : Except String RangesLaid := do
  need "the seat: a count of rows waits in front of the test" s.noneWaits
  need "the seat: all lookups are laid" (s.base.keys.length == (lookupsOf one).length)
  need "the seat: the ranges' test has begun before, or the lookups' rows do not lie on its group"
      ((s.d.st.groups[s.grp]?).any fun G => !G.inRun && G.rows.size == s.base.rows.flatten.length)
  pure ⟨s.d, s.grp, s.rider⟩

/-- **What the seat writes back**: the statement, the book and the count of roots; no count of rows
is owed any more. Asked: the test has run to its end (`testEnded`). -/
def leaveRanges (s : FirstState) (t : VerifiableInference.Desc.K12.T12) :
    Except String FirstState :=
  if testEnded t then
    .ok { s with d := { s.d with st := t.st, book := t.book, roots := t.roots }, owed := none }
  else .error "the seat: the test has not run to its end"

/-- The part of the file's last test that looks at chain 1's last state: `firstChainEnded`; no
ledger is open; all lookups are laid; the ranges' group is there; it and every group behind it but
the last one have begun their tests and hold no open row. -/
def firstEndOk (one : OneTime) (s : FirstState) : Bool :=
  firstChainEnded s && s.base.fork.isNone && s.base.keys.length == (lookupsOf one).length &&
    decide (s.grp < s.d.st.groups.size) &&
        (((s.d.st.groups.toList.drop s.grp).dropLast).all fun G => G.inRun && G.rows.isEmpty)

/-- The groups that each oracle message of a sending of chain 1 joins, message by message in the
order of sending, off the tenants as told. n: the number in the chain of the sending's first tree;
k: how many trees it sends. -/
def groupsTold (told : List ProofFile.Root) (n k : Nat) : List (List Nat) :=
    ((told.drop n).take k).flatMap fun r => r.tenants.map (·.groups)

/-- The numbers of chain 1's places outside its links: the two sendings 1 and 2, the batching 13,
W's sending 14, the seal 15. The block "rng.0.rows" has the number 4 (`layRows`); the ranges' test's
number is written in its seat's text. -/
def pieces : Pieces := ⟨1, 2, 13, 14, 15⟩

/-- **Chain 1.** one: the one-time chain's public values; D: its declared rounds; told: its trees'
tenants as told; N: the numbers of the ranges' test's place. Its first block is the sending of the
index-mask message: A WORKING BLOCK WITH TWO ROUNDS: no quiet front is laid, for this chain has no
public test of its own in front; behind it the sending of the lookups' own message. Then a link for
each lookup. Behind: the lookups' rows are laid; the ranges' test, behind the seat that asks what
the kind's law takes as premises (`rangesTest`); the batching of the pending rows, the rows on the
table, which is handed the number of trees sent in front of it (`sent`); W's sending, where `sendW`
gives one. The chain's end is its last block; it is handed the rounds of all blocks that are laid in
front of it. -/
def firstChain (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting)
    (N : H2U.PlaceNums) : Chain FirstState Claim :=
  let sent := rootsBefore D (batchRound D)
  let first : Block FirstState Claim := sendIndexMasks one pieces (groupsTold told 0 (rootsAt D 0))
  let front : List (Block FirstState Claim) :=
      [sendOwnMessage one pieces (groupsTold told (rootsBefore D 2) (rootsAt D 2))]
  let links := (lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1
  let rng : Block FirstState Claim := rangesTest (enterRanges one) leaveRanges N
  let back₀ : List (Block FirstState Claim) :=
    [layRows one, rng, batchTableRows (·.keys) one pieces sent] ++
      (sendW one pieces sent
        (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D)))).toList
  let inFront : List (Block FirstState Claim) := first :: front ++ links.flatMap Link.blocksInOrder ++ back₀
  { first := first, front := front, links := links, back := back₀
    last := firstChainEnd pieces (inFront.flatMap (·.rounds)) }

end VerifiableInference.Desc.Key
