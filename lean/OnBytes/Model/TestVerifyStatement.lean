-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifyStatement.lean: tests of OnBytes/Model/VerifyStatement.lean.

statementHeld compares the item `request`, the 177 words that a proof's first chain binds, with the
public part, from which the sub-proofs take their numbers. Both are made from the parameter file and
the scale file, each by its own parser; the item takes the request file too. Here the two files are
those that are spelled out in OnBytes/Model/TestConfig.lean. The item is then changed in one word at
a time, every word in turn. Each test is checked when the file compiles. The file is no part of the
program.
-/
import OnBytes.Model.VerifyStatement
import OnBytes.Model.TestConfig

namespace OnBytes.Model.TestVerifyStatement

open Verify

/-- A request file: the token ids 0 to 63, then its last two words, r = 63 and e = 64. -/
def request : ByteArray := Fmt.cat ((List.range 64).map word32 ++ [word32 63, word32 64])

/-- The item `request` of these files and this request. -/
def item : ByteArray := (Proof.requestItem TestConfig.kit TestConfig.klFile request).getD .empty

/-- The item i with the lowest bit of word w flipped. -/
def turned (i : ByteArray) (w : Nat) : ByteArray := i.set! (4 * w) (i.get! (4 * w) ^^^ 1)

/-- What statementHeld says of each item of the list that `items` makes from the true item: the
refusal's name, or the empty text for none. `items` is a function so that the true item is made only
once. If the public part cannot be made, every entry says so. -/
def says (items : ByteArray → List ByteArray) : List String :=
  let all := items item
  match publicOf TestConfig.kit TestConfig.klFile none with
  | .error e => all.map fun _ => "no public part: " ++ e
  | .ok X =>
    all.map fun i =>
      match statementHeld X i with
      | .ok _ => ""
      | .error e => e

/-- The words that are not compared: the constant, the version, the digest of the scale file (words
95 to 102), the digest of the request (163 to 170), the reply's word. -/
def otherWords : List Nat :=
  [0, 1] ++ (List.range 8).map (· + 95) ++ (List.range 8).map (· + 163) ++ [171]

/-- The words that are compared: all others of the 177. They are numbers of the parameter file, the
digests of the three call lists and of the four tables, the security target and four numbers of the
committed table. -/
def heldWords : List Nat := (List.range 177).filter fun w => !otherWords.contains w

#guard otherWords.length == 19 && heldWords.length == 158

#guard item.size == 708
-- passes: the true item, and the item with one word of otherWords flipped, each alone
-- refused: the item with one byte more, and with one word of heldWords flipped, each alone
#guard says (fun i => [i, i.push 0] ++ heldWords.map (turned i) ++ otherWords.map (turned i)) ==
  ["", "internal-statement-two-ways"] ++ heldWords.map (fun _ => "internal-statement-two-ways") ++
    otherWords.map fun _ => ""

end OnBytes.Model.TestVerifyStatement
