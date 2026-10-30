-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkSibAccepts.lean: tests: the written link at the small size (`linkSibSmall`,
OnBytes/Flat/LinkSibAt.lean) says yes on one written transcript, still yes on one damaged form of
the written values, and no on five others.

Why. `threeProtocolsFromDryRunAtSmallSize` (OnBytes/Flat/FilesAt.lean) holds `linkSibSmall` as the entry file's protocol. If
its verifier accepted nothing, its soundness would hold for free. Lean makes code for
`linkSibSmall`, so its own decision can be run.

WHAT THIS FILE IS: SEVEN TESTS, BY EVALUATION (`#guard`), AT THE SMALL SIZE ALONE. IT HOLDS NO
THEOREM. Each test is evaluated when the file compiles, by Lean's evaluator. The evaluator runs
compiled code; Lean's kernel checks no step of such a run. No theorem here says that
`linkSibSmall` accepts the written transcript exactly if one closed
Boolean (`decSmall`, OnBytes/Flat/EntryAccepts.lean) is true. The yes
itself is not checked by the kernel: OnBytes/Flat/EntryAccepts.lean's head
names two obstacles that are known for the link's decision.

What is run: `linkSibSmall.accept`, whole: every test bit of the proof of work is 0; each opening's
part has as many draws as it says; every symbol that is read of a stored table carries its position;
the verifier program's link (`linkVerify`) says yes on the view, at the keys written of the two
records.

Main definitions.
 `trWX`, `trSib`   the transcript: the prover's side is each round's own fixed message, all 0; the
                   verifier's messages are the pattern `blkW`, with every test bit 0.
 `oneT`, `trWXHit`, `trSibHit`   the same, but in one round every symbol of the prover's oracle
                   message has the word 1 in its first place.
 `tabHit`, `recHit`   two stored tables of zeros with one symbol of the first damaged; the record
                   `recW` with every answer 1.
The tests. Rounds are counted from 0 over the 24 rounds' data, without the round in front.
 1. Yes at the records (`recW`, `recW`), two stored tables of zeros (`tabW`) and `trSib`.
 2. No if the first stored table's symbol at position 8122602 is damaged. With test 1 this shows
    that the decision reads that symbol. (OnBytes/Flat/TestEntryAccepts.lean evaluates that number
    as the first draw of round 3 from the same pattern, in the library's form of the transcript;
    that `linkSibSmall` draws the same is not evaluated here.)
 3. Still yes if that table's symbol at position 0 is damaged: damage as such is not what test 2
    refuses. That position 0 is not opened is not evaluated here.
 4. No if the first record's answers are 1.
 5. to 7. No if the prover's oracle message of round 1, of round 13, of round 20 is damaged: the
    three rounds in which the prover sends a tree.

Not claimed. All that the head of OnBytes/Flat/EntryAccepts.lean does not claim. That the verifier
refuses every false transcript. In tests 5 to 7 an oracle message with the word 1 in every symbol's
first place is itself a word of the code: what is refused there is a wrong message, not a far word.
A verifier that accepted this one transcript alone would pass test 1 too. Nothing on an honest
prover for tables that are not 0, on a file, on hashes, at full size. This file is no evidence for
soundness or for any number.
The file takes about two minutes to compile.


-/
import OnBytes.Flat.LinkSibAt
import OnBytes.Flat.EntryAccepts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice
open _root_.Iop (Tr twoExternalStrings GPlain GChal)
open _root_.Run (ckP)
open _root_.Run.PQ (SgX PlainOf)

/-- The transcript over the rounds of the second compiler's form, at the library's data. -/
def trWX : (ds : List _root_.Run.PQ.RD) → ℕ →
    Tr (TypedOracleCompiler.Run.PQ.uL (ckP .two) (ds.map TypedOracleCompiler.Run.PQ.ofLib))
  | [], _ => ()
  | d :: ds, n =>
    ((TypedOracleCompiler.Run.PQ.zeroT d.tree.toList,
        GPlain.mk d.entry.work (PlainOf.dflt d.items) default),
      GChal.zero d.entry.work (fun i => blkW n i.val), trWX ds (n + 1))

/-- The transcript over the rounds of `linkSibSmall`. -/
def trSib : Tr linkSibSmall.shape := (((), ()), default, trWX (_root_.Run.PQ.rds wSmall) 0)

/-- An oracle message in which every symbol has the word 1 in its first place. -/
def oneT : (ts : List _root_.Fmt.Shape) → (p : TypedOracleCompiler.Run.PQ.PosT ts) →
    TypedOracleCompiler.Run.PQ.SymT ts p
  | _ :: _, .inl _ => fun j => if j.val == 0 then (1 : UInt64) else 0
  | _ :: ts, .inr p => oneT ts p

/-- `trWX`, but the prover's oracle message of round number hit is `oneT`. -/
def trWXHit (hit : ℕ) : (ds : List _root_.Run.PQ.RD) → ℕ →
    Tr (TypedOracleCompiler.Run.PQ.uL (ckP .two) (ds.map TypedOracleCompiler.Run.PQ.ofLib))
  | [], _ => ()
  | d :: ds, n =>
    ((if n == hit then oneT d.tree.toList else TypedOracleCompiler.Run.PQ.zeroT d.tree.toList,
        GPlain.mk d.entry.work (PlainOf.dflt d.items) default),
      GChal.zero d.entry.work (fun i => blkW n i.val), trWXHit hit ds (n + 1))

/-- `trSib`, but the prover's oracle message of round number hit is `oneT`. -/
def trSibHit (hit : ℕ) : Tr linkSibSmall.shape :=
  (((), ()), default, trWXHit hit (_root_.Run.PQ.rds wSmall) 0)

/-- The tables `tabW`, with the first word of the first table's symbol at position x read as 1. -/
def tabHit (a x : ℕ) : (twoExternalStrings (2 ^ a) SgX).Str :=
  (fun p => (p.val, if p.val == x then 1 :: List.replicate 255 0 else List.replicate 256 0),
    fun p => (p.val, List.replicate 256 0))

/-- The record `recW` with every answer 1. -/
def recHit : RecSmall := (recW.1, fun _ => toE (numW 1))

-- 1. yes at the written values
#guard linkSibSmall.accept (recW, recW) (tabW srS.P.T.a) trSib
-- 2. no: the first stored table's symbol at position 8122602 damaged
#guard !linkSibSmall.accept (recW, recW) (tabHit srS.P.T.a 8122602) trSib
-- 3. still yes: its symbol at position 0 damaged
#guard linkSibSmall.accept (recW, recW) (tabHit srS.P.T.a 0) trSib
-- 4. no: the first record's answers damaged
#guard !linkSibSmall.accept (recHit, recW) (tabW srS.P.T.a) trSib
-- 5. to 7. no: what the prover sends damaged
#guard !linkSibSmall.accept (recW, recW) (tabW srS.P.T.a) (trSibHit 1)
#guard !linkSibSmall.accept (recW, recW) (tabW srS.P.T.a) (trSibHit 13)
#guard !linkSibSmall.accept (recW, recW) (tabW srS.P.T.a) (trSibHit 20)

end OnBytes.Flat
