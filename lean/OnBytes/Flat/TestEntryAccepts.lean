-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/TestEntryAccepts.lean: tests: the one closed Boolean of OnBytes/Flat/EntryAccepts.lean
is true, and the program's link refuses seven damaged forms of the written values.

EACH TEST IS EVALUATED WHEN THE FILE COMPILES, BY LEAN'S EVALUATOR (`#guard`): NO TEST IS A THEOREM.
The evaluator runs compiled code; nothing that is checked of declarations is checked of it.
What the tests show.
 0. What the format's sampler draws from the written pattern: 102, 97, 66 and 66 positions in the
    four rounds that draw positions, no two of a round equal; the view has 24 rounds and 331
    columns.
 1. `decSmall` is true: with `entrySmall_accepts_iff`: the entry's verifier at the small size
    accepts the written transcript.
 2. The statement's side damaged: one entry of the first key's record 1; the seed's factor 0; one
    opened symbol of the first stored table 1: each is refused.
 3. What the prover sends damaged: the oracle message of round 1, of round 13, of round 20 not 0
    (the chain's three trees); the first answer of round 2 read as 1: each is refused.
The refusals' names were read off a first run of these lines; what was foretold before it was yes or
no. The key's form and the idea of a transcript for tables of zeros are those of the link's own test
on a made-up view (a module that the head of OnBytes/Slice/SmallRecYes.lean names and that is not in
this library); new here: typed verifier messages, from which the format's sampler draws, and
positions that differ.

Not claimed. All that the head of OnBytes/Flat/EntryAccepts.lean does not claim. That the link
refuses every false view. In the third group an oracle message with the word 1 in every symbol's
first place is itself a word of the code: what is refused there is a wrong message, not a far word.
The file takes about a minute and a half to compile. The program does not import this file.


-/
import OnBytes.Flat.EntryAccepts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat.TestEntryAccepts
open Iop _root_.Run _root_.Run.PQ OnBytes.Slice OnBytes.Maker
open Params (smallRecordRead)

/-- The name under which the program's link refuses a view at two keys; nothing if it does not. -/
def refusal (k0 k1 : TableKey) (V : Fmt.View) : Option String :=
  (linkVerify smallRecordRead.link k0 k1).failureOn (Entry.start smallRecordRead) V

/-- The written view. -/
def V0 : Fmt.View := viewW srD.ds srD.a srD.xs

-- what the sampler draws from the pattern: 102, 97, 66 and 66 positions in the four rounds that
-- draw positions, no two of a round equal; the view has the 24 rounds and 331 columns
#guard (drawnW srD.ds).map (fun x => (x.poss.length, x.poss.eraseDups.length)) ==
  [(0, 0), (0, 0), (0, 0), (102, 102), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (97, 97), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (66, 66),
    (0, 0), (66, 66)]
#guard (V0.rounds.length, V0.opened.length) == (24, 331)

-- 1. THE ONE CLOSED BOOLEAN
#guard decSmall
#guard refusal (keyW 0) (keyW 1) V0 == none

-- 2. the statement's side damaged
/-- The key with entry 0 of the record read as first, and the seed's factor as beta. -/
def keyD (item first beta : Nat) : TableKey :=
  { keyW item with
    record := (keyW item).record.set! 0 (E.ofTriple (numW first))
    seeds := (keyW item).seeds.map fun s => { s with beta := E.ofTriple (numW beta) } }

#guard refusal (keyD 0 0 5) (keyW 1) V0 == none
#guard refusal (keyD 0 1 5) (keyW 1) V0 == some "BASE: the linear claim"
#guard refusal (keyD 0 0 0) (keyW 1) V0 == some "refused"

/-- The tables, with the first word of the first table's symbol at position x read as 1. -/
def tabD (a x : Nat) : (twoExternalStrings (2 ^ a) SgX).Str :=
  (fun p => (p.val, if p.val == x then 1 :: List.replicate 255 0 else List.replicate 256 0),
    fun p => (p.val, List.replicate 256 0))

def viewTab (ds : List RD) (a : Nat) (xs : List XO) (x : Nat) : Fmt.View :=
  viewX (ckP .two) ds a xs (tabD a x) (trW ds 0)

#guard ((drawnW srD.ds)[3]?.bind fun d => d.poss[0]?) == some 8122602
#guard refusal (keyW 0) (keyW 1) (viewTab srD.ds srD.a srD.xs 8122602) ==
  some "BASE: the linear claim"

-- 3. what the prover sends damaged
/-- The transcript, but in round number hit every symbol of the prover's oracle message has the word
1 in its first place. -/
def trD (hit : Nat) : (ds : List RD) → Nat → Tr (uL (ckP .two) ds)
  | [], _ => ()
  | d :: ds, n =>
    (((fun _ j => if n == hit && j.val == 0 then 1 else 0),
        GPlain.mk d.entry.work (PlainOf.dflt d.items) default),
      GChal.zero d.entry.work (fun i => blkW n i.val), trD hit ds (n + 1))

def viewTr (hit : Nat) (ds : List RD) (a : Nat) (xs : List XO) : Fmt.View :=
  viewX (ckP .two) ds a xs (tabW a) (trD hit ds 0)

#guard ([1, 13, 20].map fun h => refusal (keyW 0) (keyW 1) (viewTr h srD.ds srD.a srD.xs)) ==
  [some "BASE: the linear claim", some "BASE: the linear claim",
    some "BASE: the symbols at the positions"]
#guard refusal (keyW 0) (keyW 1)
    { V0 with rounds := V0.rounds.modify 2 fun r =>
        { r with vals := .answer (numW 1) :: r.vals.drop 1 } } ==
  some "BASE: the linear claim"

end OnBytes.Flat.TestEntryAccepts
