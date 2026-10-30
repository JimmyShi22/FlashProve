-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/TestRequestItem.lean: tests, without a hash, of the functions of Fmt/RequestItem.lean, which
give the values of the items "request" and "the request file's words" in the statement of a proof
file's first chain.
States, under no assumption (what is checked when the file compiles): tests (#guard) that need no
hash: the tests of the lines' reader from the Lean port of the C++ verifier, at the functions of
Fmt/RequestItem.lean; and, under a stand-in for the second hash function k that writes down each
call and returns 32 bytes made from the call's number and length, which calls are made, in which
order, under which numbers and on how many bytes. Main names (all in the namespace RequestItemTest):
  `noted`, `noted31`: the stand-ins. They are no hash.
  `madeUp`: a made-up parameter file, in which the number of each line that gives a word is the
  word's place in the item.
  `declaredOf`, `user`, `told`: a declared structure with given files, a caller's values, an outer
  statement with a given item "request" and given bytes for the request file's words.
Does not show (a test is an evaluation at the values that it names, not a theorem): (1) No content
of a hashed list is written down, so a wrong piece of the right length is seen by no test here. (2)
The made-up file is built from the lists of names of Fmt/RequestItem.lean, so no test here can tell
a wrong order inside such a list. (3) Tests of these functions at the second hash function itself,
which would see both, are not in this library (OnBytes/Proof/TestRequestItem.lean tests the port's).
(4) What the last tests show as NOT NOTICED is not noticed by the functions.

-/
import Fmt.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-! ## Tests that need no hash -/

namespace RequestItemTest

/-- A stand-in for k, and no hash: it writes down the call's number and THE NUMBER OF BYTES of its
list, and returns 32 bytes: the call's number as a word of four bytes, that number of bytes as a
word of four bytes, zeros. No content of a list is written down: a wrong piece of the right length
is seen by no test of this file (the law and the tests at the hash see it). -/
def noted (num : Nat) (w : ByteArray) : StateM (List (Nat × Nat)) ByteArray := do
  modify (· ++ [(num, w.size)])
  pure (fit 32 (lowBytes 4 num ++ lowBytes 4 w.size))

/-- The calls that were written down. -/
def callsOf {α : Type} (x : StateM (List (Nat × Nat)) α) : List (Nat × Nat) := (Id.run (x.run [])).2

/-- The value beside them. -/
def valueOf {α : Type} (x : StateM (List (Nat × Nat)) α) : α := (Id.run (x.run [])).1

-- the tree: 8 words and 128 words are one piece; 129 words are two pieces
-- and a second level under 11
#guard callsOf (olderTKW noted (zeroBytes 32)) == [(10, 32)]
#guard callsOf (olderTKW noted (zeroBytes 512)) == [(10, 512)]
#guard callsOf (olderTKW noted (zeroBytes 516)) == [(10, 512), (10, 4), (11, 64)]
-- 1025 words: nine pieces, then one piece of nine digests
#guard callsOf (olderTKW noted (zeroBytes 4100)) == List.replicate 8 (10,
  512) ++ [(10, 4), (11, 288)]
-- 16385 words: three levels, of 129, 9 and 1 pieces
#guard callsOf (olderTKW noted (zeroBytes 65540)) ==
  List.replicate 128 (10, 512) ++ [(10, 4)] ++ List.replicate 8 (11, 512) ++ [(11, 32), (11, 288)]
-- the value is the last call's
#guard valueOf (olderTKW noted (zeroBytes 516)) == some (fit 32 (lowBytes 4 11 ++ lowBytes 4 64))
-- fewer than eight words, or a length that is no multiple of four: nothing, and no call
#guard valueOf (olderTKW noted (zeroBytes 28)) == none && callsOf (olderTKW
  noted (zeroBytes 28)) == []
#guard valueOf (olderTKW noted (zeroBytes 33)) == none && callsOf (olderTKW
  noted (zeroBytes 33)) == []
-- a k whose values have 31 bytes: the levels run out
#guard olderTK (fun _ _ => zeroBytes 31) (zeroBytes 32) == none
#guard hex (textWords "call a b c\n".toUTF8) == "63616c6c2061206220630a00"
#guard textWords "abcd".toUTF8 == "abcd".toUTF8 && textWords ByteArray.empty == ByteArray.empty

/-- A small text in the form of a parameter file. -/
def someLines : ReqLines :=
  ReqLines.read "sec 128\ncall a b c\ncallA q\nlt 6\ncall d e\nlt 7\nx 01\nL 8\n".toUTF8

#guard someLines.value "L" == some 8 && someLines.value "sec" == some 128
-- a name in two lines, a leading zero, a name in no line
#guard someLines.value "lt" == none && someLines.value "x" == none && someLines.value "y" == none
#guard someLines.text "call" == "call a b c\ncall d e\n".toUTF8
-- a name is compared whole: the line callA is no line call
#guard someLines.text "callA" == "callA q\n".toUTF8
-- 20 bytes of text are five words; 8 bytes are two
#guard callsOf (someLines.callsW noted "call") == [(73, 20)]
#guard callsOf (someLines.callsW noted "callA") == [(73, 8)]
-- no line callH: without a text nothing and no call; with the six lines (115 bytes) one call on 116
#guard valueOf (someLines.callsW noted "callH") == none && callsOf
  (someLines.callsW noted "callH") == []
#guard callHIfNone.toUTF8.size == 115
#guard callsOf (someLines.callsW noted "callH" (some callHIfNone)) == [(73, 116)]
-- the largest number that a word holds, and the next
#guard (ReqLines.read "a 4294967295\nb 4294967296\n".toUTF8).value "a" == some 4294967295
#guard (ReqLines.read "a 4294967295\nb 4294967296\n".toUTF8).value "b" == none
-- the last five words: the line sec; then w, b, n, m of the line table b n i m e w
#guard (ReqLines.read "sec 128\ntable 1 2 3 4 5 6\n".toUTF8).lastWords ==
  some (cat ([128, 6, 1, 2, 4].map (lowBytes 4)))
-- a line with two blanks in a row, or with a blank at its end, comes back byte for byte
#guard (ReqLines.read "call a  b \ncall\n".toUTF8).text "call" == "call a  b \ncall\n".toUTF8
#guard splitAt 0x20 "a  b ".toUTF8.toList == ["a", "", "b", ""].map (·.toUTF8.toList)
#guard splitAt 0x20 [] == [[]]
#guard (names2.splitOn " ").length == 27 && (names37.splitOn " ").length == 34
#guard (names103.splitOn " ").length == 11 && (names130.splitOn " ").length == 25

/-- The lines "name number" for a list of names: the first gets the number
"start", the next one more. -/
def numberedLines (names : List String) (start : Nat) : String :=
  String.join ((names.zip (List.range names.length)).map fun x => x.1 ++ " " ++ toString (start +
      x.2) ++ "\n")

/-- A made-up parameter file. The number of each line that gives a word is the word's place in the
item by the table of R15.5, but for the line prof, which must be 20 and stands at the place 2. So lt
is 3 and a request has 10 words. The names' order is the lists' own: it is held against the format
page's program in the test module at the second hash function. The file has no line callH. -/
def madeUp : String :=
  "version H821\nsec 172\ntable 174 175 9 176 9 173\nprof 20\n" ++
  numberedLines ((names2.splitOn " ").drop 1) 3 ++ numberedLines (names37.splitOn " ") 37 ++
  numberedLines (names103.splitOn " ") 103 ++ numberedLines (names130.splitOn " ") 130 ++
  numberedLines ((List.range 8).map fun i => "tsilu" ++ toString i) 71 ++
  numberedLines ((List.range 8).map fun i => "tsig" ++ toString i) 79 ++
  numberedLines ((List.range 8).map fun i => "trope" ++ toString i) 87 ++
  numberedLines ((List.range 8).map fun i => "texp" ++ toString i) 114 ++
  "call a b\ncallA q\n"

/-- The item at the made-up file, a scale file of 516 bytes and a request of 10 words. -/
def madeUpItem : StateM (List (Nat × Nat)) (Option ByteArray) :=
  requestItemW noted madeUp.toUTF8 (zeroBytes 516) (zeroBytes 40)

/-- Word i of a string of bytes. -/
def wordOf (b : ByteArray) (i : Nat) : ByteArray := b.extract (4 * i) (4 * i + 4)

-- the calls, in the item's order: call; the scale file's tree; callA; callH; the request's tree
#guard callsOf madeUpItem ==
  [(73, 12), (10, 512), (10, 4), (11, 64), (73, 8), (73, 116), (10, 40)]
#guard (valueOf madeUpItem).map (·.size) == some 708
-- the first two words
#guard (valueOf madeUpItem).map (·.extract 0 8) == some (lowBytes 4 0x4D363100 ++ "H821".toUTF8)
-- every word that is a line's number stands at its place: 2 (prof); 3 to 28; 37 to 94; 103 to 121;
-- 130 to 154; 172 to 176
#guard (valueOf madeUpItem).map (wordOf · 2) == some (lowBytes 4 20)
#guard (valueOf madeUpItem).any fun b =>
  ((List.range 177).filter fun i =>
    (3 ≤ i && i ≤ 28) || (37 ≤ i && i ≤ 94) || (103 ≤ i && i ≤ 121) || (130 ≤ i && i ≤ 154) ||
      172 ≤ i).all fun i => wordOf b i == lowBytes 4 i
-- the five digests stand at the words 29, 95, 122, 155, 163: each stand-in tells its last call
#guard (valueOf madeUpItem).any fun b =>
  [(29, 73, 12), (95, 11, 64), (122, 73, 8), (155, 73, 116), (163, 10, 40)].all fun x =>
    b.extract (4 * x.1) (4 * x.1 + 32) == fit 32 (lowBytes 4 x.2.1 ++ lowBytes 4 x.2.2)
-- the word of the next token
#guard (valueOf madeUpItem).map (wordOf · 171) == some (lowBytes 4 0)
-- refused: a request of another length; a line twice; a line less; prof 19; NE 0 (the place 12);
-- a version of five characters
#guard valueOf (requestItemW noted madeUp.toUTF8 (zeroBytes 516) (zeroBytes 44)) == none
#guard valueOf (requestItemW noted (madeUp ++ "d 6\n").toUTF8 (zeroBytes
  516) (zeroBytes 40)) == none
#guard valueOf (requestItemW noted (madeUp.replace "d 6\n" "").toUTF8 (zeroBytes 516) (zeroBytes
  40)) == none
#guard valueOf (requestItemW noted (madeUp.replace "prof 20\n" "prof 19\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
#guard valueOf (requestItemW noted (madeUp.replace "NE 12\n" "NE 0\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
#guard valueOf (requestItemW noted (madeUp.replace "H821" "H8211").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
-- these altered copies differ from the file: each replacement found its text
#guard madeUp.replace "d 6\n" "" != madeUp && madeUp.replace "prof 20\n" "prof 19\n" != madeUp &&
  madeUp.replace "NE 12\n" "NE 0\n" != madeUp && madeUp.replace "H821" "H8211" != madeUp
-- no line call: refused; no line callA: refused
#guard valueOf (requestItemW noted (madeUp.replace "call a b\n" "").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
#guard valueOf (requestItemW noted (madeUp.replace "callA q\n" "").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
-- a k whose values under 73 have 31 bytes: the item would have 705 bytes: refused by the last test;
-- the same call at a k whose values all have 32 bytes has a value
#guard requestItem (fun num _ => zeroBytes (if num == 73 then 31 else 32))
  madeUp.toUTF8 (zeroBytes 32)
  (zeroBytes 40) == none
#guard (requestItem (fun _ _ => zeroBytes 32) madeUp.toUTF8 (zeroBytes 32) (zeroBytes 40)).isSome

/-- A declared structure with given public files; its other fields are not read here. -/
def declaredOf (files : List ByteArray) : Declared :=
  { files := files, setting := ⟨.two, 0, 0, 0, 0, 1⟩, table := default }

/-- A caller's values with a request of ten words. -/
def user : UserStm := ⟨zero32, [0x04030201, 2, 3, 4, 5, 6, 7, 8, 7, 8], 0⟩

#guard user.requestBytes.size == 40 && hex (user.requestBytes.extract 0 8) == "0102030402000000"
-- three files: the value is that of the first and the third (two stand-ins for the second give one
-- value: tested among the last tests)
#guard valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]).requestItemW noted user) ==
  valueOf (requestItemW noted madeUp.toUTF8 (zeroBytes 516) user.requestBytes)
#guard (valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]).requestItemW noted
  user)).isSome
-- the second and the third file in each other's places: here nothing, BECAUSE
-- 7 bytes are no whole words
-- (the order itself is not noticed: see the tests at the end); two files, four files: nothing
#guard valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 516, zeroBytes
  7]).requestItemW noted user) == none
#guard valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 516]).requestItemW noted user) == none
#guard valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516, zeroBytes
  516]).requestItemW noted user) == none
#guard callsOf ((declaredOf [madeUp.toUTF8, zeroBytes 516]).requestItemW noted user) == []

/-- What a proof's chains are told, with a given item "request" and given bytes for the item "the
request file's words": `user`'s request file, unless others are named. -/
def told (request : ByteArray) (words : ByteArray := user.requestBytes) : ProofStm :=
  { table := ⟨zero32, []⟩, copy := 0, request := request, words := words, reply := (0, 0, 0) }

-- the test: true at the function's value; false at that value with one byte turned, at the request
-- file's own bytes, at the empty string, and where the function gives nothing
#guard (valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]).requestItemW noted
  user)).any fun b =>
  valueOf ((told b).requestOkW noted (declaredOf [madeUp.toUTF8, zeroBytes
      7, zeroBytes 516]) user) &&
  !valueOf ((told (b.set! 700 (b.get! 700 + 1))).requestOkW noted
    (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user) &&
  !valueOf ((told b).requestOkW noted (declaredOf [madeUp.toUTF8, zeroBytes 516]) user)
#guard !valueOf ((told user.requestBytes).requestOkW noted
  (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user)
#guard !valueOf ((told ByteArray.empty).requestOkW noted
  (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user)
-- the request file's words: the test without a hash is true at the caller's request file; false
-- with one byte turned, a word less, a word more, at the empty string
#guard (told ByteArray.empty).wordsOk user &&
  !(told ByteArray.empty (user.requestBytes.set! 39 1)).wordsOk user &&
  !(told ByteArray.empty (user.requestBytes.extract 0 36)).wordsOk user &&
  !(told ByteArray.empty (user.requestBytes ++ lowBytes 4 0)).wordsOk user &&
  !(told ByteArray.empty ByteArray.empty).wordsOk user && user.requestBytes.get! 39 != 1
-- the test on both: at the right item "request", false as soon as the words are not the file's; and
-- false with the two strings in each other's places
#guard (valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]).requestItemW noted
  user)).any fun b =>
  !valueOf ((told b (user.requestBytes.set! 39 1)).requestOkW noted
    (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user) &&
  !valueOf ((told b ByteArray.empty).requestOkW noted
    (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user) &&
  !valueOf ((told b b).requestOkW noted
    (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user) &&
  !valueOf ((told user.requestBytes b).requestOkW noted
    (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user)

/-! ### Which calls are made at the declared structure, and what is not noticed
 -/

/-- The seven calls at the made-up file, a scale file of 516 bytes and a request of ten words. -/
def sevenCalls : List (Nat × Nat) :=
  [(73, 12), (10, 512), (10, 4), (11, 64), (73, 8), (73, 116), (10, 40)]

-- the five digests are computed whatever the lines say: the same calls
-- where the item is refused for
-- prof 19, for a line less, for a line twice
#guard callsOf (requestItemW noted (madeUp.replace "prof 20\n" "prof 19\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) ==
  sevenCalls
#guard callsOf (requestItemW noted (madeUp.replace "d 6\n" "").toUTF8 (zeroBytes 516) (zeroBytes
  40)) == sevenCalls
#guard callsOf (requestItemW noted (madeUp ++ "d 6\n").toUTF8 (zeroBytes 516) (zeroBytes 40)) ==
  sevenCalls
-- and where the request has another length: its tree is hashed all the same
#guard callsOf (requestItemW noted madeUp.toUTF8 (zeroBytes 516) (zeroBytes 44)) ==
  [(73, 12), (10, 512), (10, 4), (11, 64), (73, 8), (73, 116), (10, 44)]
-- at three files: these seven calls and no other, whatever the second file
-- is: none on the layout file,
-- be it one that a tree or a text would take (64 bytes)
#guard callsOf ((declaredOf [madeUp.toUTF8, zeroBytes 64, zeroBytes 516]).requestItemW noted user)
  == sevenCalls
#guard callsOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]).requestItemW noted user)
  == sevenCalls
#guard valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 64, zeroBytes
  516]).requestItemW noted user) ==
  valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]).requestItemW noted user)
-- no file, one, two, four, five, six files: nothing, and no call
#guard [0, 1, 2, 4, 5, 6].all fun n =>
  let D := declaredOf ((List.range n).map fun i => if i == 0 then madeUp.toUTF8 else zeroBytes 516)
  valueOf (D.requestItemW noted user) == none && callsOf (D.requestItemW noted user) == []
-- the same list at three files has a value: above the function gives nothing for the number alone
#guard (valueOf ((declaredOf ((List.range 3).map fun i =>
  if i == 0 then madeUp.toUTF8 else zeroBytes 516)).requestItemW noted user)).isSome
-- the test on the field runs the function once
#guard callsOf ((told ByteArray.empty).requestOkW noted
  (declaredOf [madeUp.toUTF8, zeroBytes 7, zeroBytes 516]) user) == sevenCalls
#guard callsOf ((told ByteArray.empty).requestOkW noted (declaredOf [madeUp.toUTF8, zeroBytes
  516]) user) == []

/-- A stand-in whose values have 31 bytes; it writes the calls down like `noted`. -/
def noted31 (num : Nat) (w : ByteArray) : StateM (List (Nat × Nat)) ByteArray := do
  modify (· ++ [(num, w.size)])
  pure (zeroBytes 31)

-- where the levels run out: sixteen calls, one a level, and no more
#guard callsOf (olderTKW noted31 (zeroBytes 32)) == (10, 32) :: List.replicate 15 (11, 31)
#guard valueOf (olderTKW noted31 (zeroBytes 32)) == none

-- NOT NOTICED, and shown here so that nobody takes it for tested:
-- the second and third file in each other's places, both of whole words: a value, and another one
#guard (valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 516, zeroBytes 64]).requestItemW noted
  user)).isSome
#guard valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 516, zeroBytes
  64]).requestItemW noted user) !=
  valueOf ((declaredOf [madeUp.toUTF8, zeroBytes 64, zeroBytes 516]).requestItemW noted user)
-- what stands behind a line's first number, or behind the version; an empty line
#guard madeUp.replace "d 6\n" "d 6 999\n" != madeUp && madeUp.replace "H821\n" "H821 x\n" != madeUp
#guard valueOf (requestItemW noted (madeUp.replace "d 6\n" "d 6 999\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) ==
  valueOf madeUpItem
#guard valueOf (requestItemW noted (madeUp.replace "H821\n" "H821 x\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) ==
  valueOf madeUpItem
#guard valueOf (requestItemW noted (madeUp.replace "d 6\n" "d 6\n\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) ==
  valueOf madeUpItem
-- NOTICED, again:
-- lines callH of the file's own are hashed, and not the six lines: 12 bytes of text in place of 116
#guard callsOf (requestItemW noted (madeUp ++ "callH a b c\n").toUTF8
  (zeroBytes 516) (zeroBytes 40)) ==
  [(73, 12), (10, 512), (10, 4), (11, 64), (73, 8), (73, 12), (10, 40)]
-- the line table with seven numbers, or with five: refused
#guard valueOf (requestItemW noted (madeUp.replace "9 173\n" "9 173 1\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
#guard valueOf (requestItemW noted (madeUp.replace " 9 173\n" " 173\n").toUTF8 (zeroBytes 516)
  (zeroBytes 40)) == none
#guard madeUp.replace "9 173\n" "9 173 1\n" != madeUp && madeUp.replace " 9 173\n" " 173\n" !=
  madeUp
-- a k with 31 bytes for the lines call and 33 for the lines callA: 708 bytes,
-- every word between shifted
#guard (requestItem (fun num w => zeroBytes (if num != 73 then 32 else if w.size == 12 then 31
  else if w.size == 8 then 33 else 32)) madeUp.toUTF8 (zeroBytes 32) (zeroBytes 40)).map (·.size)
      == some 708

end RequestItemTest

end Fmt
