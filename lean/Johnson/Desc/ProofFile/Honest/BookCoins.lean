-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookCoins.lean: the sixth of the files that compute the book of coins
(`ProverCoinCounts`, Honest/Frame.lean): where in a sender's coins each class of an oracle message's coins is:
one function for the sender, for whoever is given a message's coins, and for a toy example. And the
entries by which a part carries a whole message, with an executable test. From public data alone. It
names no prover's side. Executable definitions, and tests at made-up lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

The order is that of Honest/BookRows.lean: message by message, in the order of sending; in a
message: the main rows' tails; a masking word's main message; the pad, if it lies in a main row; the
mask rows' entries (of a fold's fresh table: its 2k + 1 coefficients); the mask rows' tails. The
coins of the base field and those of the extension field are numbered separately.

  1  `CoinSort`, `MsgDue.seat`   a class of coins; where it is inside its message's range, and how
     many
  2  `msgStretch`, `sortAt`   a message's whole range among its sender's coins; a class's
  3  `Cs.sort`   the coins themselves, cut from a sender's coins or from a carried block
  4  `carryEntry`, `carriesWhole`   the entry by which a part carries a message; an executable test:
     every carrying entry of a book is exactly one message's whole range

Limits.
  * It counts as Honest/BookRows.lean counts, and is compared here with no program and no other
    author's count.
  * Which messages a part carries is not said here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRows
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (Codes OracleNotice)

/-! ## 1 The classes -/

/-- A class of an oracle message's coins, in the order in which they come. -/
inductive CoinSort where
  | tails | word | pad | entries | maskTails
  deriving DecidableEq, Repr

/-- So many coins of the main rows' own field. -/
def MsgDue.own (d : MsgDue) (n : Nat) : Due := if d.deg == 1 then ⟨n, 0⟩ else ⟨0, n⟩

/-- **Where a class is inside its message's range, and how many coins it has.** -/
def MsgDue.seat (d : MsgDue) : CoinSort → Due × Due
  | .tails => (⟨0, 0⟩, d.own d.tails)
  | .word => (d.own d.tails, d.own d.word)
  | .pad => (d.own (d.tails + d.word), d.own d.pad)
  | .entries => (d.main, ⟨0, d.entries⟩)
  | .maskTails => (d.main.plus ⟨0, d.entries⟩, ⟨0, d.maskTails⟩)

/-! ## 2 Among a sender's coins -/

/-- **The whole range of message number j, from 0, among its sender's coins**: start, count. -/
def msgStretch (codes : Codes) (k : Nat) (ns : List OracleNotice) (j : Nat) : Option (Due × Due) :=
  (sendDue codes k (ns.take j)).bind fun a => (ns[j]?.bind (msgDue codes k)).map fun d => (a, d.all)

/-- **A class of that message's coins among the sender's**: start, count. -/
def sortAt (codes : Codes) (k : Nat) (ns : List OracleNotice) (j : Nat) (s : CoinSort) :
    Option (Due × Due) :=
  (sendDue codes k (ns.take j)).bind fun a =>
    (ns[j]?.bind (msgDue codes k)).map fun d => (a.plus (d.seat s).1, (d.seat s).2)

/-! ## 3 The coins -/

/-- **A class's coins, cut from coins.** `from_`: where the message's range begins in c: its start
among the sender's coins; ⟨0, 0⟩ where c is the carried block itself. -/
def Cs.sort {n : Due} (c : Cs n) (from_ : Due) (d : MsgDue) (s : CoinSort) :
    Option (Cs (d.seat s).2) :=
  c.cut (from_.plus (d.seat s).1) (d.seat s).2

/-! ## 4 Carrying -/

/-- **The entry by which the part at `dest` carries message number j of the sending that the part at
`sender` holds.** -/
def carryEntry (codes : Codes) (k : Nat) (ns : List OracleNotice) (sender : Addr) (j : Nat)
    (dest : Addr) : Option Ahead :=
  (msgStretch codes k ns j).map fun x => ⟨carriedName sender j dest, sender, x.1, x.2, dest, false⟩

/-- **Every carrying entry is exactly one message's whole range.** `sent`: for each part that holds
a sending: its address and its messages' ranges. -/
def carriesWhole (B : ProverCoinCounts) (sent : List (Addr × List (Due × Due))) : Bool :=
  (B.ahead.filter (!·.once)).all fun e =>
    sent.any fun x => x.1 == e.owner && x.2.contains (e.start, e.count)

/-! ### Tests at made-up lists -/

-- toyA: three rows over the base field with a mask row: 15 tails of F; 32 entries and a tail of 4
#guard (msgDue toyCodes 3 toyA).map
    (fun d => [d.seat .tails, d.seat .pad, d.seat .entries, d.seat .maskTails]) ==
  some [(⟨0, 0⟩, ⟨15, 0⟩), (⟨15, 0⟩, ⟨0, 0⟩), (⟨15, 0⟩, ⟨0, 32⟩), (⟨15, 32⟩, ⟨0, 4⟩)]
-- toyB, after it: a row over the extension field: its range begins after toyA's; its entries
-- after its own tail of 7
#guard msgStretch toyCodes 3 [toyA, toyB] 1 == some (⟨15, 36⟩, ⟨0, 43⟩)
#guard sortAt toyCodes 3 [toyA, toyB] 1 .entries == some (⟨15, 43⟩, ⟨0, 32⟩) &&
  sortAt toyCodes 3 [toyA, toyB] 1 .entries ==
    (maskStart toyCodes 3 [toyA, toyB] 1).map (·, ⟨0, 32⟩)
-- the classes' counts add up to the message's
#guard (msgDue toyCodes 3 toyB).any fun d =>
  [CoinSort.tails, .word, .pad, .entries, .maskTails].foldl (fun n s => n.plus (d.seat s).2)
    ⟨0, 0⟩ == d.all
-- the coins: coin number i of the extension field is i: the entries of toyB begin at 43
#guard ((msgDue toyCodes 3 toyB).bind fun d =>
    ((⟨fun _ => 0, fun i => OnBytes.Slice.toE (i.val.toUInt64, 0, 0)⟩ : Cs ⟨15, 79⟩).sort ⟨15, 36⟩ d
      .entries).bind fun c => (c.eAt 0).toOption.map OnBytes.Slice.ofE) == some (43, 0, 0)
-- a carrying entry, and the test: true at the whole range; false at one coin fewer
#guard (carryEntry toyCodes 3 [toyA, toyB] (toyTo 0) 1 (toyTo 2)).any fun e =>
  carriesWhole { first := [], shared := [], second := [], ahead := [e], cuts := [] }
      [(toyTo 0, [(⟨0, 0⟩, ⟨15, 36⟩), (⟨15, 36⟩, ⟨0, 43⟩)])] &&
    !carriesWhole { first := [], shared := [], second := [], cuts := []
                    ahead := [{ e with count := ⟨0, 42⟩ }] }
      [(toyTo 0, [(⟨0, 0⟩, ⟨15, 36⟩), (⟨15, 36⟩, ⟨0, 43⟩)])]

end ProofFile.Honest
