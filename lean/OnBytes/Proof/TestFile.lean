-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/TestFile.lean: tests of the small readers under OnBytes/Proof/.

Each refusal of the readers of a head and of a place is met once, on short strings of bytes that are
made here. So are the branches of `refusalName`, the readers of a numeral and of an element as text,
and the refusals of the reader of a claims file. No whole proof file is checked here: the files are
too large for a test module. All values are made up by hand and come from no file. The large numbers
are 10^19 and 10^20, and the second field's prime, 2^64 - 2^32 + 1 = 18446744069414584321, with the
number before it. The program does not import this file.
-/
import OnBytes.Proof.ToyLinks

namespace OnBytes.Proof.Test

/-- The name under which a reader refuses; nothing if it does not refuse. -/
def refusal {α : Type} : Except String α → Option String
  | .ok _ => none
  | .error e => some e

/-! ## Heads -/

/-- The eight bytes of a good head. -/
def head (k : FileKind) : ByteArray := k.tag ++ versionOf .two

/-- A head with another version: byte i of the four is changed. -/
def headWith (k : FileKind) (i : Nat) : ByteArray :=
  k.tag ++ (versionOf .two).set! i (Fmt.byteAt (versionOf .two) i ^^^ 1)

#guard [FileKind.key, .entry, .proof].all fun k => (readHead .two k (head k)).toOption == some 8
#guard refusal (readHead .two .key ((head .key).extract 0 7)) == some "file-too-short"
#guard refusal (readHead .two .entry (head .key)) == some "file-of-another-kind"
#guard refusal (readHead .two .key (FileKind.key.tag ++ Fmt.ascii "HG01")) ==
  some "version-of-an-earlier-format"
#guard refusal (readHead .two .key (FileKind.key.tag ++ Fmt.ascii "H7xx")) ==
  some "version-of-an-earlier-format"
#guard refusal (readHead .two .key (headWith .key 2)) == some "version-of-another-field"
#guard refusal (readHead .two .key (headWith .key 3)) == some "version-of-another-hash"
#guard refusal (readHead .two .key (headWith .key 0)) == some "version-unknown"
#guard refusal (readHead .two .key (headWith .key 1)) == some "version-unknown"
#guard (readProofHead .two (head .proof ++ ⟨#[5, 1, 0, 0]⟩)).toOption == some (261, 12)
#guard refusal (readProofHead .two (head .proof ++ ⟨#[5, 1, 0]⟩)) == some "file-too-short"
#guard refusal (readProofHead .two (head .key ++ ⟨#[5, 1, 0, 0]⟩)) == some "file-of-another-kind"
#guard word32At ⟨#[1, 2]⟩ 0 == 513 && word32At ⟨#[1, 2]⟩ 2 == 0

/-! ## The place in the binding tree -/

/-- Made-up bytes: n bytes that count up from `first`. -/
def someBytes (first n : Nat) : ByteArray := ⟨(Array.range n).map fun i => UInt8.ofNat (first + i)⟩

/-- A digest of public files, a seal, a salt of 40 bytes and a sibling, all made up. -/
def cfg : ByteArray := someBytes 1 32
/-- See `cfg`. -/
def closing : ByteArray := someBytes 40 32
/-- See `cfg`. -/
def salt : ByteArray := someBytes 80 40
/-- See `cfg`. -/
def sibling : ByteArray := someBytes 130 32

/-- The bytes of a place: the number, the salt, the siblings. -/
def placeBytes (place : Nat) (siblings : List ByteArray) : ByteArray :=
  Fmt.u64 (UInt64.ofNat place) ++ salt ++ Fmt.cat siblings

/-- The root and the end that `readPlace` finds. -/
def found (depth : Nat) (b : ByteArray) : Option (ByteArray × Nat) :=
  (readPlace ⟨depth, 40⟩ cfg closing b 0).map fun p => (p.root, p.next)

-- a tree of one leaf: the leaf is the root
#guard found 0 (placeBytes 0 []) == some (Fmt.bindLeaf 0 0 cfg closing salt, 48)
-- two leaves: the sibling is the right child at place 0 and the left child at place 1
#guard found 1 (placeBytes 0 [sibling]) ==
  some (Fmt.vertexB cfg (Fmt.bindLeaf 1 0 cfg closing salt) sibling, 80)
#guard found 1 (placeBytes 1 [sibling]) ==
  some (Fmt.vertexB cfg sibling (Fmt.bindLeaf 1 1 cfg closing salt), 80)
-- a place that is no leaf's; bytes that end in the number, in the salt, in a sibling
#guard found 0 (placeBytes 1 []) == none && found 1 (placeBytes 2 [sibling]) == none
#guard found 0 ((placeBytes 0 []).extract 0 7) == none
#guard found 0 ((placeBytes 0 []).extract 0 47) == none
#guard found 1 ((placeBytes 0 [sibling]).extract 0 79) == none
-- shapes that the format does not admit: too deep; a salt of another length
#guard found 49 (placeBytes 0 []) == none
#guard (readPlace ⟨0, 32⟩ cfg closing (placeBytes 0 []) 0).isNone

/-! ## The names of refusals -/

-- the two tests' names as the proximity test makes them (OnBytes/Iop/Prox.lean)
#guard refusalName "x-" baseLinearName == "x-decision-linear-claim"
#guard refusalName "x-" basePositionsName == "x-decision-symbols-at-positions"
#guard refusalName "x-" replyCheck == "x-decision-reply"
#guard plainFailures.all fun n => refusalName "x-" n == "x-decision"
#guard refusalName "x-" "a caller's name" == "a caller's name"
#guard [baseLinearName, basePositionsName, replyCheck, unnamed].all
  fun n => (namesOf "x-").contains (refusalName "x-" n)

/-! ## Numerals, elements and claims -/

/-- `decimalBelow` on a text. -/
def numeral (bound : Nat) (s : String) : Option Nat := decimalBelow bound s.toUTF8.toList

#guard numeral 10 "0" == some 0 && numeral 10 "9" == some 9 && numeral 10 "10" == none
#guard numeral 10 "" == none && numeral 10 "01" == none && numeral 10 "1a" == none
#guard numeral (10 ^ 30) "100000000000000000000" == none
#guard numeral (10 ^ 30) "10000000000000000000" == some (10 ^ 19)

#guard elementOfText .two "1 2 3\n".toUTF8 == some (E.mk3 1 2 3)
-- no line feed; two line feeds; two blanks; two numbers; the prime itself
#guard elementOfText .two "1 2 3".toUTF8 == none && elementOfText .two "1 2 3\n\n".toUTF8 == none
#guard elementOfText .two "1  2 3\n".toUTF8 == none && elementOfText .two "1 2\n".toUTF8 == none
#guard elementOfText .two "18446744069414584321 0 0\n".toUTF8 == none
#guard (elementOfText .two "18446744069414584320 0 0\n".toUTF8).isSome

/-- A claims file of `links` links with `each` claims, whose lists are all empty. -/
def claimsFile (links each claims : Nat) : ByteArray :=
  Fmt.cat ((links :: each :: List.replicate (2 * claims) 0).map fun n => Fmt.u64 (UInt64.ofNat n))

#guard ((readClaims .two (claimsFile 3 2 6)).map fun l => l.map (·.length)) == some [2, 2, 2]
-- another number of claims in a link; a claim too few; a byte left over
#guard (readClaims .two (claimsFile 2 3 6)).isNone
#guard (readClaims .two (claimsFile 3 2 5)).isNone
#guard (readClaims .two (claimsFile 3 2 6 ++ ⟨#[0]⟩)).isNone
-- a file too short for its two words
#guard (readClaims .two ((claimsFile 3 2 6).extract 0 15)).isNone

/-- A claims file of one link whose first claim has a point of one element with the first coordinate
x. All other lists are empty. -/
def claimsWith (x : UInt64) : ByteArray :=
  Fmt.cat ([1, 2, 1, x, 0, 0, 0, 0, 0].map Fmt.u64)

-- the largest coordinate in canonical form, and the prime itself
#guard (readClaims .two (claimsWith 18446744069414584320)).isSome
#guard (readClaims .two (claimsWith 18446744069414584321)).isNone

end OnBytes.Proof.Test
