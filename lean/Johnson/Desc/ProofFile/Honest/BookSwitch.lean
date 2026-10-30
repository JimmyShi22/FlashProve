-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookSwitch.lean: the seventh of the files that compute the book of
coins (`ProverCoinCounts`, Honest/Frame.lean): the rows of a proximity test's switches, which
Honest/BookRows.lean leaves out. From public data alone. It names no prover's side. Executable
definitions, and tests at made-up lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What a switch's sender samples, by the format's pages. The oracle message g of the next stage holds
what the fold leaves, which is no new coin, and room that is left free, which a prover fills with
sampled elements (FORMAT.md, section 16). New coins, in this order: g's main rows' tails; the
entries of g's mask table that are not carried, the pad among them; g's mask rows' tails. Then the
messages that are sent with g: the next fold's fresh table, or the masking word: as
Honest/BookRows.lean counts them.
Carried are, at a test's own switch: the messages of the old and of the fresh mask row, the main
row's tail and these two rows' tails: 2 l' + r + 2 r', with (.., l, r) the base code and (.., l',
r') the mask code of the stage before (`switchParts`, OnBytes/Iop/Cs.lean, with two mask rows, no
kept row and no kept member; docs/format/08-parameters.md, 8.4, item 14).

  1  `carriedOf`, `groupCodes`, `testOf`   what is carried; a sending's two codes; a switch's test
  2  `switchDue`, `roomOf`   one switch's coins; its free room
  3  `switchesDue`, `mergeRows`, `switchRows`   a chain's switches; rows at one address added up

Limits.
  * A switch with kept rows or kept members is not handled (a carrying message between two segments
    has no mask row and is counted by Honest/BookRows.lean).
  * The codes of a test's first stage are for the caller to supply, by the test's name.
  * The fresh table that a fold sends itself in "FOLD epsilon" has no row here either.
  * Subtraction is cut off at 0.
  * `switchesDue` takes the number k of a fold's rounds as `(foldK …).getD 0`: where no fold follows
    a switch, k is 0, and a fresh table that is sent with the switch is counted at one coefficient.
    Nothing returns an error there: `rowsIn` (Honest/BookRows.lean) and `foldEntries`
    (Honest/BookFolds.lean), which do so at other sendings, leave the switches out.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)
open OnBytes (Codes Code OracleNotice)

variable {S Cl : Type}

/-! ## 1 What is carried -/

/-- **What a test's own switch carries**, from the codes of the stage before. -/
def carriedOf (b m : Code) : Nat := 2 * m.ell + b.r + 2 * m.r

/-- The base code of a sending's first message with main rows, and the mask code of its first
message with mask rows. -/
def groupCodes (codes : Codes) (ns : List OracleNotice) : Option (Code × Code) :=
  ((ns.find? fun n => n.shape.mainRows != 0).bind fun n => codes.base[n.shape.code]?).bind fun b =>
    ((ns.find? fun n => n.shape.maskRows != 0).bind fun n => codes.mask[n.shape.maskCode]?).map
      fun m => (b, m)

/-- The test's name in a switch's label. -/
def testOf (label : String) : String := (label.splitOn ", the code switch of stage ").headD ""

/-! ## 2 One switch -/

/-- The free room of g, the pad included: from the codes of the stage before. -/
def roomOf (codes : Codes) (old : Code × Code) (g : OracleNotice) : Option Nat :=
  (msgDue codes 0 g).map fun d => d.entries - carriedOf old.1 old.2

/-- **One switch's coins**: g first, then what is sent with it. `k`: the rounds of the first fold
after the sending. -/
def switchDue (codes : Codes) (k : Nat) (old : Code × Code) : List OracleNotice → Option Due
  | [] => none
  | g :: riders =>
    (msgDue codes k g).bind fun d => (sendDue codes k riders).map fun r =>
      ({ d with entries := d.entries - carriedOf old.1 old.2 } : MsgDue).all.plus r

/-! ## 3 A chain -/

/-- A chain's switches, in order: the label, the round "SEND seed", the free room, the coins.
`prev`: the test of the switch before, with the codes of the stage that it made. `first`: the codes
of a test's first stage, by the test's name. Where no fold follows, k is taken as 0. -/
def switchesDue (codes : Codes) (rounds : List Fmt.DeclaredRound)
    (first : String → Option (Code × Code)) :
    List (Nat × Johnson.G.Sending) → Option (String × Code × Code) →
      Except String (List (String × Nat × Nat × Due))
  | [], _ => .ok []
  | x :: xs, prev =>
    let t := testOf x.2.label
    let old := match prev with
      | some p => if p.1 == t then some p.2 else first t
      | none => first t
    let k := (foldK (rounds.drop (x.1 + 1))).getD 0
    match old, x.2.sent.head? with
    | some o, some g =>
      match roomOf codes o g, switchDue codes k o x.2.sent, groupCodes codes [g] with
      | some room, some d, some now_ =>
        (switchesDue codes rounds first xs (some (t, now_))).map
          fun l => (x.2.label, x.1, room, d) :: l
      | _, _, _ => .error (x.2.label ++ ": a message names a code that the chain does not have")
    | none, _ => .error (x.2.label ++ ": the codes of the test's first stage are not laid")
    | _, none => .error (x.2.label ++ ": the sending holds no message")

/-- Rows at one address, added up; in the order in which the addresses first occur. -/
def mergeRows (l : List (Addr × Due)) : List (Addr × Due) :=
  (l.map (·.1)).eraseDups.map fun a =>
    (a, (l.filter fun r => r.1 == a).foldl (fun n r => n.plus r.2) ⟨0, 0⟩)

/-- **The rows of a chain's switches**: for each part that holds switches: all their coins. -/
def switchRows (bs : List (Block S Cl)) (c : Johnson.G.ChainSends)
    (first : String → Option (Code × Code)) : Except String (List (Addr × Due)) :=
  if (seedRounds bs).length != c.sends.length then
    .error "the sendings are not as many as the chain's rounds SEND seed"
  else
    (switchesDue c.codes (bs.flatMap (·.rounds)) first
      (((seedRounds bs).zip c.sends).filter fun x => isSwitch x.2.label) none).bind
      fun (l : List (String × Nat × Nat × Due)) =>
      (l.mapM fun (x : String × Nat × Nat × Due) =>
        (match addrOfRound bs x.2.1 with
          | some a => Except.ok (a, x.2.2.2)
          | none => Except.error (x.1 ++ ": its round lies in no sub-protocol") :
          Except String (Addr × Due))).map mergeRows

/-! ### Tests at made-up lists -/

/-- An address for the tests. -/
def toyTo' (part : Nat) : Addr := ⟨⟨1, none, 2, .K12⟩, part⟩

-- the stage before: base code (.., 64, 5), mask code (.., 32, 4): 2 · 32 + 5 + 2 · 4
#guard carriedOf ⟨10, 64, 5⟩ ⟨6, 32, 4⟩ == 77
/-- g: two main rows over the extension field under the code (8, 16, 7); four mask rows. -/
def toyG : OracleNotice :=
  ⟨{ code := 1, mainRows := 2, mainDeg := 3, maskRows := 4, maskCode := 0 }, 0⟩
-- its table has 4 · 32 entries: 51 are free
#guard roomOf toyCodes (⟨10, 64, 5⟩, ⟨6, 32, 4⟩) toyG == some 51
-- its coins: 14 of the main tails, 51, 16 of the mask tails; with a fresh table of four rows
-- at k = 3 after it: 7 and 16 more
#guard switchDue toyCodes 3 (⟨10, 64, 5⟩, ⟨6, 32, 4⟩) [toyG] == some ⟨0, 81⟩
#guard switchDue toyCodes 3 (⟨10, 64, 5⟩, ⟨6, 32, 4⟩)
  [toyG, ⟨{ mainRows := 0, maskRows := 4, maskCode := 0, answers := 0 }, 0⟩] == some ⟨0, 104⟩
#guard groupCodes toyCodes [toyG] == some (⟨8, 16, 7⟩, ⟨6, 32, 4⟩)
#guard testOf "the own test, the code switch of stage 2" == "the own test"
#guard mergeRows [(toyTo' 0, ⟨1, 2⟩), (toyTo' 1, ⟨0, 5⟩), (toyTo' 0, ⟨3, 4⟩)] ==
  [(toyTo' 0, ⟨4, 6⟩), (toyTo' 1, ⟨0, 5⟩)]

end ProofFile.Honest
