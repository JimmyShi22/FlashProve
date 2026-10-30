-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookRows.lean: the second of the files that compute the book of coins
(`ProverCoinCounts`, Honest/Frame.lean): the rows of the parts that hold a sending: how many coins such a part
takes, and where in them each oracle message's coins are. From public data alone: a description, and
the sendings that the library lists from the three public files (`Johnson.G.sendsOf`,
Johnson/G/Sends.lean). It names no prover's side. Executable definitions, and tests at made-up
lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What is a coin of a sender, by the format's pages (docs/format/09-key-and-leaf-files.md, its head
and R12.1, R12.3, R12.10, R12.11; FORMAT.md, section 16). A code is (a, l, r): l entries of a
message, r of the random tail.
  a main row's tail   r coins, in the row's own field
  a mask row   l' + r' coins of the extension field: every entry is sampled
  a fold's fresh table   (mask rows alone, no sample) not so: the 2k + 1 coefficients of the fold's
     hiding polynomial, and its rows' tails; all else in it is computed from these or is 0
     (docs/format/toys/1-product.md, 2.1). k: the fold's rounds "FOLD round"
  the sample's pad   in the last mask row: no further coin; where the message has no mask row: in
     its last main row: one coin for each answer; three for each if the main rows are over the base
     field
  the masking word of a proximity test's last step   its main row's message too: l coins. It is
     recognised by its notice: main rows, and no answer
Not computed here: the oracle message that a proximity test's switch sends. Its rows hold what the
fold leaves, which is no new coin, and sampled elements in the room that is left free: another
count. `rowsIn` leaves such a sending out and `switchesIn` lists it. A segment's carrying message is
computed: it has main rows alone, and its free room holds zeros.

The order of a sender's coins. Message by message, in the order of sending; in each message: the
main rows' tails, row by row; a masking word's main message; the pad, if it lies in a main row; all
entries of the mask rows by the format's own number (entry 0 of row 0, entry 0 of row 1, .., then
entry 1 of row 0, ..), or, of a fold's fresh table, the 2k + 1 coefficients: by variable, the linear
then the quadratic one, the last variable's constant before its two others; the mask rows' tails,
row by row. The coins of the base field and those of the extension field are each numbered through
all messages in this order. Later steps take a message's free entries by increasing number: so what
one of them takes is one range.

  1  `MsgDue`, `isFresh`, `msgDue`, `MsgDue.all`   one oracle message's coins, by what they are
  2  `sendDue`, `maskStart`   a sending's coins; where a message's mask entries begin in them
  3  `addrOfRound`, `seedRounds`, `isSwitch`, `foldK`, `rowsIn`, `switchesIn`   the part that holds
     a round; the fold after a sending; a chain's rows

Limits.
  * That a kept message's pad is sampled anew at each sending is assumed, on a reading of the
    programs that was made in another part of this project.
  * Which fold spends a fresh table is taken to be the first fold after its sending, in its chain
    or, if there is none, in the chain that the caller names after it.
  * The fresh mask that a fold sends itself in "FOLD epsilon" is not among the library's sendings
    and has no row here.
  * The key file and the leaf file are not looked at.
  * The entries of a book are not computed here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookOf
import Johnson.G.Sends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)
open OnBytes (Codes OracleNotice)

variable {S Cl : Type}

/-! ## 1 One oracle message -/

/-- One oracle message's coins, in the order in which they come. `deg`: 1: its main rows are over
the base field; 3: over the extension field. -/
structure MsgDue where
  deg : Nat
  /-- the main rows' tails -/
  tails : Nat
  /-- a masking word's main message -/
  word : Nat
  /-- the pad, where it lies in a main row -/
  pad : Nat
  /-- all entries of the mask rows; of a fold's fresh table: its polynomial's coefficients -/
  entries : Nat
  /-- the mask rows' tails -/
  maskTails : Nat
  deriving DecidableEq, Repr

/-- A fold's fresh table, by its notice: mask rows alone, and no sample. -/
def isFresh (n : OracleNotice) : Bool :=
  n.shape.mainRows == 0 && n.shape.maskRows != 0 && n.shape.answers == 0

/-- **An oracle message's coins**, from its notice and the chain's codes; `none` where it names a
code that the chain does not have. `k`: the number of rounds "FOLD round" of the fold that spends a
fresh table: read at such a table alone. -/
def msgDue (codes : Codes) (k : Nat) (n : OracleNotice) : Option MsgDue :=
  let s := n.shape
  let no : OnBytes.Code := ⟨0, 0, 0⟩
  (if s.mainRows == 0 then some no else codes.base[s.code]?).bind fun b =>
  (if s.maskRows == 0 then some no else codes.mask[s.maskCode]?).map fun m =>
    { deg := s.mainDeg
      tails := s.mainRows * b.r
      word := if s.answers == 0 then s.mainRows * b.ell else 0
      pad := if s.maskRows == 0 && s.mainRows != 0 then
          (if s.mainDeg == 1 then 3 * s.answers else s.answers) else 0
      entries := if isFresh n then 2 * k + 1 else s.maskRows * m.ell
      maskTails := s.maskRows * m.r }

/-- What comes before the mask rows' entries, by field. -/
def MsgDue.main (d : MsgDue) : Due :=
  if d.deg == 1 then ⟨d.tails + d.word + d.pad, 0⟩ else ⟨0, d.tails + d.word + d.pad⟩

/-- All of the message's coins, by field. -/
def MsgDue.all (d : MsgDue) : Due := d.main.plus ⟨0, d.entries + d.maskTails⟩

/-! ## 2 A sending -/

/-- **A sending's coins**: its messages', added up. -/
def sendDue (codes : Codes) (k : Nat) (ns : List OracleNotice) : Option Due :=
  (ns.mapM (msgDue codes k)).map fun l => l.foldl (fun n d => n.plus d.all) ⟨0, 0⟩

/-- **Where the mask entries of message number j, from 0, begin** among the sending's coins. -/
def maskStart (codes : Codes) (k : Nat) (ns : List OracleNotice) (j : Nat) : Option Due :=
  (sendDue codes k (ns.take j)).bind fun a =>
    (ns[j]?.bind (msgDue codes k)).map fun d => a.plus d.main

/-! ## 3 A chain's rows -/

/-- The address of the part that holds round number i, from 0, of a chain: by the cut of
Honest/BookOf.lean. -/
def addrOfRound : List (Block S Cl) → Nat → Option Addr
  | [], _ => none
  | b :: bs, i =>
    if i < b.rounds.length then
      let starts :=
        (partsCut b).foldl (fun (l : List Nat × Nat) k => (l.1 ++ [l.2], l.2 + k)) ([], 0)
      some ⟨b.place, (starts.1.filter (· ≤ i)).length - 1⟩
    else addrOfRound bs (i - b.rounds.length)

/-- The numbers of a chain's rounds "SEND seed", in order. -/
def seedRounds (bs : List (Block S Cl)) : List Nat :=
  ((bs.flatMap (·.rounds)).zipIdx.filter fun r => r.1.entry.name == "SEND seed").map (·.2)

/-- A proximity test's switch, by the label that the library gives the sending. -/
def isSwitch (label : String) : Bool := (label.splitOn ", the code switch of stage ").length == 2

/-- The number of rounds "FOLD round" of the first fold among declared rounds; `none` if there is no
round "FOLD epsilon". -/
def foldK (rs : List Fmt.DeclaredRound) : Option Nat :=
  match rs.dropWhile fun r => r.entry.name != "FOLD epsilon" with
  | [] => none
  | _ :: u => some (u.takeWhile fun r => r.entry.name == "FOLD round").length

/-- **A chain's rows**: for each sending that is no switch: the part that holds its round, and its
coins. `later`: the declared rounds of the chain in which a fresh table is spent that no fold of
this chain follows. An error where the sendings are not as many as the chain's rounds "SEND seed",
where a round lies in no sub-protocol, where a message names a code that the chain does not have, or
where there is no fold after a fresh table. -/
def rowsIn (bs : List (Block S Cl)) (c : Johnson.G.ChainSends) (later : List Fmt.DeclaredRound := []) :
    Except String (List (Addr × Due)) :=
  if (seedRounds bs).length != c.sends.length then
    .error "the sendings are not as many as the chain's rounds SEND seed"
  else
    (((seedRounds bs).zip c.sends).filter fun x => !isSwitch x.2.label).mapM fun x =>
      let k := foldK ((bs.flatMap (·.rounds) ++ later).drop (x.1 + 1))
      if x.2.sent.any isFresh && k.isNone then
        .error (x.2.label ++ ": no fold stands behind its fresh table")
      else
      match addrOfRound bs x.1, sendDue c.codes (k.getD 0) x.2.sent with
      | some a, some d => .ok (a, d)
      | none, _ => .error (x.2.label ++ ": its round lies in no sub-protocol")
      | _, none => .error (x.2.label ++ ": a message names a code that the chain does not have")

/-- The sendings that `rowsIn` leaves out: their labels. -/
def switchesIn (c : Johnson.G.ChainSends) : List String :=
  (c.sends.filter fun x => isSwitch x.label).map (·.label)

/-! ### Tests at made-up lists -/

/-- Two base codes and a mask code. -/
def toyCodes : Codes := { base := #[⟨10, 64, 5⟩, ⟨8, 16, 7⟩], mask := #[⟨6, 32, 4⟩] }

/-- `toyA`, `toyB`: three rows over the base field with a mask row; a row over the extension field
with one. -/
def toyA : OracleNotice :=
  ⟨{ code := 0, mainRows := 3, mainDeg := 1, maskRows := 1, maskCode := 0 }, 0⟩
def toyB : OracleNotice :=
  ⟨{ code := 1, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 0 }, 0⟩

-- three rows over the base field with a mask row: three tails; no pad of its own; 32 entries, a
-- tail
#guard msgDue toyCodes 3 toyA == some ⟨1, 15, 0, 0, 32, 4⟩
-- two rows over the extension field, no mask row, one answer: two tails and one coin for the pad
#guard msgDue toyCodes 3 ⟨{ code := 1, mainRows := 2, mainDeg := 3, maskRows := 0 }, 0⟩ ==
  some ⟨3, 14, 0, 1, 0, 0⟩
-- rows over the base field, no mask row, two answers: six coins for the pad
#guard (msgDue toyCodes 3 ⟨{ code := 0, mainRows := 1, mainDeg := 1, answers := 2 }, 0⟩).map
  (·.all) == some ⟨11, 0⟩
-- mask rows alone, no sample: a fold's fresh table, at k = 3: seven coefficients and two tails
#guard (msgDue toyCodes 3 ⟨{ mainRows := 0, maskRows := 2, maskCode := 0, answers := 0 }, 0⟩).map
  (·.all) == some ⟨0, 15⟩
-- mask rows alone with a sample: every entry
#guard (msgDue toyCodes 3 ⟨{ mainRows := 0, maskRows := 2, maskCode := 0, answers := 1 }, 0⟩).map
  (·.all) == some ⟨0, 72⟩
-- the first fold among rounds: two rounds; none
#guard foldK [{ entry := { name := "BAT" } }, { entry := { name := "FOLD epsilon" } },
  { entry := { name := "FOLD round" } }, { entry := { name := "FOLD round" } },
  { entry := { name := "SEND seed" } }, { entry := { name := "FOLD round" } }] == some 2
#guard foldK [{ entry := { name := "BAT" } }] == none
-- a masking word: its main message too
#guard msgDue toyCodes 3
  ⟨{ code := 1, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 0, answers := 0 }, 0⟩ ==
  some ⟨3, 7, 16, 0, 32, 4⟩
-- a code that the chain does not have
#guard msgDue toyCodes 3 ⟨{ code := 2, mainRows := 1 }, 0⟩ == none
-- a sending of two messages; where the second's mask entries begin
#guard sendDue toyCodes 3 [toyA, toyB] == some ⟨15, 79⟩
#guard maskStart toyCodes 3 [toyA, toyB] 1 == some ⟨15, 43⟩
#guard isSwitch "the own test, the code switch of stage 2" && !isSwitch "link 3, moment 0"

end ProofFile.Honest
