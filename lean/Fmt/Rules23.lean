-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules23.lean: the format's hash formatHash, its numbers, the single oracle's strings, and the oracle
realised by BLAKE2b.

In standard terms: a domain-separated hash. Every call of the hash `formatHash` puts a label in front of its
input (a number for the call's purpose, a place for a tree's number, an index) and 32 bytes into the
parameter block: the start, which `hDom` asks to be all 0 under a number without one. The calls are
also written as queries to a single oracle on byte strings, one query for each 32 bytes of a digest;
that oracle is realised here on all strings.

The file renders sections 2 and 3 of the format page, that is docs/format/FORMAT.md, which comes
with the programs (the C++ implementation that comes with this Lean code), not at the edition that
ships: rules
R2.1 to R2.6, R3.1
to R3.5. At the edition rendered here R3.1 has a row for the number
179 and a cell for the tree under 174, R2.4 follows both,
and a leaf's label holds its shape.

Definitions that compute, on ByteArray and Nat; every known answer of the two sections as a test
(#guard) (ten), tests of this library's own, and 60 further answers made by the page's own program
(marked: not the page's known answers). No Mathlib; one small theorem (`HM_id`). The laws for all
inputs: Fmt/Rules23Laws.lean; the known answers as theorems: Fmt/Rules23Known.lean.

Main names: what the page rules, in this library's own words, and where it stands here.
  `numbers`, `isNumber`: (R3.1) the thirteen numbers under which a hash of the format is made (179,
    the commitment ID).

  `hasStart`, `hasTree`: (R3.1) seven of them take a start (a digest). At four the tree's place is
    filled: the three kinds of leaves, with their tree's number, and 162, where the chain's label
    stands in that place. A vertex (166; in the tree that binds a batch's requests: 178) has tree 0,
    index 0, and starts from the configuration's digest.
  `treeBound`: (R2.3).
  `isLeaf`, `leafPlace`, `placeTree`, `placeW`, `placeS`: (R2.1, R2.3) under the three numbers of
    leaves (164, 173, 174) the label's first word is number + 2^16 tree + 2^32 W + 2^56 s8, W the
    words of the leaf's content, s8 the words of its salt. How it is rendered: `label`, `formatHash`, `oStr`,
    `OQ` keep one number in the tree's place, "what stands above the number in the label's first
    word"; for a leaf it is `leafPlace tree W s8` = tree + 2^16 * W + 2^40 * s8. A caller of a
    leaf's hash has to write `leafPlace` there.
  `leafFill`, `leafOK`: (R2.3, R2.4, R7.3) what lies behind a leaf's label: W at least 1; s8 from 5
    to 8 (W below 2^24 and the tree's number below 2^16 by their places); under 173 and 174 the
    tree's number 0; 8 W bytes, the fill, all zeros, 8 s8 bytes.
  `idxOK`: (R2.3, R2.4).
  `retired`, `reserved`: (R3.2, R2.5) six numbers that are not given out and get no
    meaning; the number 177, under which no hash is made: left to a formal definition.
  `dlen`: (R2.2) the digest length: 64 under the number 162 (a call of a round's query), else 32.
  `label`: (R2.1).
  `pblock`: (R2.2) BLAKE2b's parameter block, 64 bytes: digest length; key length 0; fanout 1; depth
    1; 28 zero bytes; the start's 32 bytes (its fields "salt" and "personalization").
  `hDom`: the domain (R2.3, with R2.4's clause on the index): a number of the table; tree within its
    bound, and 0 where the table leaves the place empty; `idxOK`; at most 2^32 - 144 bytes; start of
    32 bytes, all 0 under a number without a start; `leafOK`.
  `formatHash`: (R2.1, R2.2) BLAKE2b as specified, sequential, no key, of label ++ bytes, with the start as
    salt and personalization. Total: outside the domain it still computes (the start cut or padded
    with 0 to 32 bytes; number + 2^16 tree and index as words modulo 2^64): whoever wants the page's
    H asks `hDom` beside it.
  `oStr`: (R2.4) the oracle's string of a hash: one byte for the half (0 or 1: the first or the
    second 32 bytes of the digest, as `oracle` answers), the block, the label, the bytes.
  `OQ`, `oParse`: a string read back: some (half, number, tree, index, start, bytes) exactly on the
    strings `oStr` of the domain with half 0 or 1.
  `oUsed`, `inImage`: (R2.4) the format's image, decided exactly: read back by `oParse`, with the
    half 0, or the half 1 under the number 162 alone. These are the strings `oStr` of the calls in
    the domain at such a half (`inImage_iff`, Fmt/Rules23Laws.lean). Strings under the reserved
    number 177 are outside.
  `oracle`: the single oracle O, 32 bytes, realised on all strings. In the image it is that half of
    formatHash. Outside it, it is formatHash under the reserved number 177, tree 0, index 0, no start, of the whole
    string (this library's own ruling, not the page's: R2.5 leaves 177 and these strings to a formal
    definition). Why: O stands for a random function on all strings, and a constant outside the
    image is visibly none. Why no clash: as inputs of BLAKE2b (block, label and bytes) a string of
    the image has a number other than 177, a string outside it the number 177 with the whole string
    behind the label.
  `HM ask`: the sections that hash are written over a variable monad and a variable hash; at
    `HM ask` they are trees of questions to the single oracle.
  `HO O`: the tie: HO oracle = formatHash on the domain: tests at values here; for all inputs:
    Fmt/Rules23Laws.lean.
  `nComp`: (R2.6).

Limits: R2.7 is rendered by no test of this file. By R2.7 data that would make a hashed string too
long, a chain of 2^63 rounds, a tree with 2^a + x from 2^63 on are no data of the format, and a
verifier refuses. `hDom` says which calls the hash admits; who refuses is a reader's matter. R3.6
rules nothing.
One point where `hDom` is narrower than the page's program. The program's H asserts R2.3 alone (an
index below 2^63); R2.4 takes out of the image the indices that the table does not name. `hDom`
follows R2.4, so that "in the domain" and "its string lies in the image" are one thing (at the half
0, for a number below 2^16, a place below 2^48, an index below 2^64 and a start of 32 bytes).
A leaf's content has at least one word: R2.3.



Under 173 and 174 the tree's number is 0 (R3.1's table; R2.4's clause on the tree; R7.4: the trees
of all stored tables have that one number): `leafOK` asks it. So a string under 174 with another
number lies outside the image, and the oracle realised here answers it as it answers every string
outside (under the reserved number). One known answer of the page's own section 7 (a leaf under 174
at the tree's number 5; a test of Fmt/Rules7.lean) is such a string.


formatHash does have that value there, but by the rules named above no valid
file has such a leaf.
This file does not say that BLAKE2b behaves as a random function: the instance's assumption. It does
not say what the bytes are under each number (sections 4, 5, 7), beyond the form that `leafOK` asks
of a leaf's.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Blake2b
import Fmt.Rules1

set_option autoImplicit false

namespace Fmt

/-- the numbers under which a hash of the format is made -/
def numbers : List Nat := [160, 162, 164, 166, 168, 169, 171, 172, 173, 174, 176, 178, 179]
def isNumber (n : Nat) : Bool := numbers.contains n
/-- the numbers that take a start; those at which the tree's place is filled -/
def hasStart (n : Nat) : Bool := [162, 164, 166, 171, 173, 174, 178].contains n
def hasTree (n : Nat) : Bool := [162, 164, 173, 174].contains n
/-- the three numbers of leaves -/
def isLeaf (n : Nat) : Bool := [164, 173, 174].contains n
/-- What stands in the tree's place of a leaf's label: the tree's number; W, the words of the leaf's
content; s8, the words of its salt -/
def leafPlace (tree W s8 : Nat) : Nat := tree + 2 ^ 16 * W + 2 ^ 40 * s8
/-- the three, read off the place -/
def placeTree (t : Nat) : Nat := t % 2 ^ 16
def placeW (t : Nat) : Nat := t / 2 ^ 16 % 2 ^ 24
def placeS (t : Nat) : Nat := t / 2 ^ 40
/-- R7.3's fill between a content of W words and a salt of s bytes: none if, the label's 16 bytes
counted in, the salt does not straddle a border between blocks of 128 bytes; else up to that border
-/
def leafFill (W s : Nat) : Nat :=
  if (16 + 8 * W) % 128 + s ≤ 128 then 0 else 128 - (16 + 8 * W) % 128
/-- What lies behind a leaf's label: a content of at least one word; a salt of 5 to 8 words; under
173 and 174 the tree's number 0; 8 W bytes, the fill, all zeros, 8 s8 bytes. Under a number that is
no leaf's: nothing is asked here -/
def leafOK (n t : Nat) (bytes : ByteArray) : Bool :=
  !isLeaf n ||
    (decide (1 ≤ placeW t) && decide (5 ≤ placeS t) && decide (placeS t ≤ 8) &&
      (!(n == 173 || n == 174) || placeTree t == 0) &&
      bytes.size == 8 * placeW t + leafFill (placeW t) (8 * placeS t) + 8 * placeS t &&
      (bytes.extract (8 * placeW t) (8 * placeW t + leafFill (placeW t) (8 * placeS t))).data ==
        (zeroBytes (leafFill (placeW t) (8 * placeS t))).data)
/-- what the tree's place can hold -/
def treeBound (n : Nat) : Nat := if n = 162 || isLeaf n then 2 ^ 48 else 2 ^ 16
/-- the index: below 2^63; one of the named values where the table names single values -/
def idxOK (n i : Nat) : Bool :=
  decide (i < 2 ^ 63) && (!([166, 176, 178, 179].contains n) || i == 0) &&
    (n != 169 || decide (i ≤ 2))
/-- given out once, never again; reserved -/
def retired : List Nat := [161, 163, 165, 167, 170, 175]
def reserved : Nat := 177

/-- the digest length -/
def dlen (number : Nat) : Nat := if number = 162 then 64 else 32

/-- The label. -/
def label (number tree index : Nat) : ByteArray := u64n (number + 65536 * tree) ++ u64n index

/-- The parameter block. -/
def pblock (number : Nat) (start : ByteArray) : ByteArray :=
  ⟨#[UInt8.ofNat (dlen number), 0, 1, 1]⟩ ++ zeroBytes 28 ++ fit 32 start

/-- The domain of formatHash. -/
def hDom (number tree index : Nat) (start bytes : ByteArray) : Bool :=
  isNumber number && decide (tree < treeBound number) && (hasTree number || tree == 0) &&
    idxOK number index && decide (bytes.size ≤ 2 ^ 32 - 144) && start.size == 32 &&
    (hasStart number || start.data == (zeroBytes 32).data) && leafOK number tree bytes

/-- The hash. -/
def formatHash (number tree index : Nat) (start bytes : ByteArray) : ByteArray :=
  blake2b (dlen number) ((fit 32 start).extract 0 16)
    ((fit 32 start).extract 16 32) (label number tree index ++ bytes)

/-- The oracle's string of a hash. -/
def oStr (half : UInt8) (number tree index : Nat) (start bytes : ByteArray) : ByteArray :=
  ⟨#[half]⟩ ++ pblock number start ++ label number tree index ++ bytes

/-- a string of the oracle, read back -/
structure OQ where
  half   : UInt8
  number : Nat
  tree   : Nat
  index  : Nat
  start  : ByteArray
  bytes  : ByteArray

/-- Reading a string back: none outside the strings of the domain. -/
def oParse (s : ByteArray) : Option OQ :=
  if s.size < 81 then none else
  let half := byteAt s 0
  let w0 := (wordAt s 65).toNat
  let q : OQ :=
    ⟨half, w0 % 65536, w0 / 65536, (wordAt s 73).toNat, s.extract 33 65, s.extract 81 s.size⟩
  if (half == 0 || half == 1) && hDom q.number q.tree q.index q.start q.bytes &&
      (s.extract 1 65).data == (pblock q.number q.start).data then some q
  else none

/-- the strings on which a hash of the format is the oracle -/
def oUsed (q : OQ) : Bool := q.half == 0 || q.number == 162

/-- The format's image. -/
def inImage (s : ByteArray) : Bool := (oParse s).any oUsed

/-- the oracle outside the image: the hash under the reserved number, of the whole string -/
def oOut (s : ByteArray) : ByteArray := formatHash reserved 0 0 zero32 s

/-- The one oracle, realised. -/
def oracle (s : ByteArray) : ByteArray :=
  match oParse s with
  | none => oOut s
  | some q =>
    if oUsed q then
      let h := formatHash q.number q.tree q.index q.start q.bytes
      if q.half == 0 then h.extract 0 32 else h.extract 32 64
    else oOut s

/-- The hash by asking the one oracle, in any monad: one question; two under the number 162, the
half 0 first. -/
def HM {m : Type → Type} [Monad m] (ask : ByteArray → m ByteArray)
    (number tree index : Nat) (start bytes : ByteArray) : m ByteArray :=
  if number = 162 then do
    let a ← ask (oStr 0 number tree index start bytes)
    let b ← ask (oStr 1 number tree index start bytes)
    pure (a ++ b)
  else ask (oStr 0 number tree index start bytes)

/-- The hash over any oracle that is a function. -/
def HO (O : ByteArray → ByteArray) (number tree index : Nat) (start bytes : ByteArray) :
    ByteArray :=
  if number = 162 then
    O (oStr 0 number tree index start bytes) ++ O (oStr 1 number tree index start bytes)
  else O (oStr 0 number tree index start bytes)

/-- asking in the identity monad is the function's form -/
theorem HM_id (O : ByteArray → ByteArray) (number tree index : Nat) (start bytes : ByteArray) :
    HM (m := Id) O number tree index start bytes = HO O number tree index start bytes := by
  unfold HM HO
  split <;> rfl

/-- calls of the compression function on a string of n > 0 bytes -/
def nComp (n : Nat) : Nat := (n + 127) / 128

/-! ### The ten known answers of sections 2 and 3 (of an edition that is neither the one rendered
here nor the one that ships) -/

#guard hex (oStr 0 164 (leafPlace 9 1 5) (2 ^ 33 + 12) (pattern 32) (u64n 1 ++ zeroBytes 40)) == "002000010100000000000000000000000000000000000000000000000000000000030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dca4000900010000050c00000002000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
#guard hex (oStr 1 162 0 3 (pattern 32) (pattern 4)) == "014000010100000000000000000000000000000000000000000000000000000000030a11181f262d343b424950575e656c737a81888f969da4abb2b9c0c7ced5dca2000000000000000300000000000000030a1118"
#guard hex (formatHash 168 0 0 (zeroBytes 32) ByteArray.empty) == "8313e9c466ac5287097eff32299fb13cd2f38c4149e5c06db3672e05c4c584df"
#guard hex (formatHash 168 0 5 (zeroBytes 32) (pattern 128)) == "4d26351ed3e9aacf02412551771a4182b2dd254e97c59b70b8276663cc4fde1f"
#guard hex (formatHash 168 0 (2 ^ 33 + 5) (zeroBytes 32) (pattern 129)) == "0dcff0ef969a659d79a3810bcab9ef0716b249a3d129f2659ed88ddf3f5d55fb"
#guard hex (formatHash 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)) == "a88e3190297571af06940920681fc835d3703d831b5c10d2c5c98ade7383b486"
#guard hex (formatHash 166 0 0 (pattern 32) (pattern 64)) == "af2a19aa20cc89e1e740e2ec4d34a275eae7bff385fcfc64e3064ccd7cc1b3f8"    -- a vertex
#guard hex (formatHash 178 0 0 (pattern 32) (pattern 64)) == "5060c36d8a53d1f4d4fcce8b2678190f7a3ab70d9a7e09c978a808fb3a01f408"    -- a vertex of the binding tree
#guard hex (formatHash 162 (2 ^ 32) 3 (pattern 32) (pattern 8 ++ u64n (4 + 256 * 8 + 65536 * 1) ++ u64n 5)) == "13aafa2ea680d9959c9f20ff463e4c6883414386b4d969a7aaa55496dbc49bdac42b398b0396076027de5292790cf2bd59b8b55c13ba2c3cb0488b791f0d4a93"    -- the message pattern(8), kind 4, w = 8, j = 1, nonce 5
#guard hex (formatHash 162 0 3 (pattern 32) (u64n 1 ++ u64n 0)) == "7dd1787fe5dee7994c6410b994bcd7aec9789019b120012e63ba79f094be483d62ab614467bab4323df78f9a77004db3462e2a38d4eb8e0d431ae6dc57c997ea"    -- no message, kind 1, w = 0, j = 0, nonce 0

/-! ### Tests of this library's own: the table; the domain; strings read back; in the image the
oracle is formatHash's halves; the image on both sides -/

-- the table: thirteen numbers; seven with a start; at four the tree's place is filled; no retired
-- or reserved number among them
#guard numbers.length == 13 && (numbers.filter hasStart).length == 7 && (numbers.filter hasTree).length == 4
#guard (retired ++ [reserved]).all fun n => !isNumber n && !hasStart n && !hasTree n
#guard [162, 164, 166, 171, 173, 174, 178].all fun n => isNumber n && hasStart n
#guard [0, 1, 159, 240, 241, 180, 65536 + 168].all fun n => !isNumber n && !hDom n 0 0 (zeroBytes 32) ByteArray.empty    -- numbers outside the table are not given out
-- sizes
#guard (label 164 (leafPlace 9 3 5) 12).size == 16 && (pblock 164 (pattern 32)).size == 64 && (oStr 0 168 0 0 (zeroBytes 32) ByteArray.empty).size == 81
#guard (formatHash 168 0 0 (zeroBytes 32) ByteArray.empty).size == 32 && (formatHash 162 0 3 (pattern 32) (pattern 16)).size == 64
-- the domain, at its borders
#guard hDom 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64) && hDom 168 0 (2 ^ 63 - 1) (zeroBytes 32) ByteArray.empty && hDom 164 (leafPlace 65535 1 5) 0 (zeroBytes 32) (pattern 48)
#guard !hDom 177 0 0 (zeroBytes 32) ByteArray.empty && !hDom 161 0 0 (zeroBytes 32) ByteArray.empty
-- 179: no tree, the index 0 alone, no start
#guard hDom 179 0 0 (zeroBytes 32) (pattern 40) && !hDom 179 0 1 (zeroBytes 32) (pattern 40) && !hDom 179 1 0 (zeroBytes 32) (pattern 40) && !hDom 179 0 0 (pattern 32) (pattern 40)
#guard !hDom 164 65536 12 (pattern 32) (pattern 64) && !hDom 168 1 0 (zeroBytes 32) ByteArray.empty && !hDom 168 0 (2 ^ 63) (zeroBytes 32) ByteArray.empty
#guard !hDom 168 0 0 (pattern 32) ByteArray.empty && !hDom 164 (leafPlace 9 3 5) 12 (pattern 31) (pattern 64) && !hDom 164 (leafPlace 9 3 5) 12 (pattern 33) (pattern 64)
-- A leaf's label holds its shape.
-- The place: put together and read back; number + 2^16
-- place is the page's word
#guard leafPlace 9 1 5 == 9 + 2 ^ 16 + 5 * 2 ^ 40 && 164 + 65536 * leafPlace 9 3 5 == 164 + 2 ^ 16 * 9 + 2 ^ 32 * 3 + 2 ^ 56 * 5
#guard [(0, 0, 5), (9, 1, 5), (65535, 2 ^ 24 - 1, 8), (3, 25, 6)].all fun x => placeTree (leafPlace x.1 x.2.1 x.2.2) == x.1 && placeW (leafPlace x.1 x.2.1 x.2.2) == x.2.1 && placeS (leafPlace x.1 x.2.1 x.2.2) == x.2.2 && decide (leafPlace x.1 x.2.1 x.2.2 < 2 ^ 48)
-- the fill: the values of the page's own program (the length of its leaf's bytes less content and
-- salt), contents of 0 to 33 words, all four lengths of a salt
#guard (List.range 34).map (fun W => leafFill W 40) == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 24, 16, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 24, 16, 8, 0, 0, 0, 0]
#guard (List.range 34).map (fun W => leafFill W 48) == [0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 32, 24, 16, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 32, 24, 16, 8, 0, 0, 0, 0]
#guard (List.range 34).map (fun W => leafFill W 56) == [0, 0, 0, 0, 0, 0, 0, 0, 48, 40, 32, 24, 16, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 40, 32, 24, 16, 8, 0, 0, 0, 0]
#guard (List.range 34).map (fun W => leafFill W 64) == [0, 0, 0, 0, 0, 0, 0, 56, 48, 40, 32, 24, 16, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 48, 40, 32, 24, 16, 8, 0, 0, 0, 0]
-- the salt's words: 5 to 8
#guard !hDom 164 (leafPlace 9 3 4) 12 (pattern 32) (pattern 56) && hDom 164 (leafPlace 9 3 8) 12 (pattern 32) (pattern 88) && !hDom 164 (leafPlace 9 3 9) 12 (pattern 32) (pattern 96) && !hDom 164 9 12 (pattern 32) (pattern 64)
-- the bytes behind the label: 8 W, the fill, 8 s8: one byte less or more, another W
#guard !hDom 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 63) && !hDom 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 65) && !hDom 164 (leafPlace 9 2 5) 12 (pattern 32) (pattern 64) && !hDom 164 (leafPlace 9 4 5) 12 (pattern 32) (pattern 64)
-- the fill is there and all zeros: a content of 10 words, a salt of 40 bytes: 32 bytes of fill
#guard hDom 164 (leafPlace 9 10 5) 12 (pattern 32) (pattern 80 ++ zeroBytes 32 ++ pattern 40) && !hDom 164 (leafPlace 9 10 5) 12 (pattern 32) (pattern 80 ++ pattern 40) && !hDom 164 (leafPlace 9 10 5) 12 (pattern 32) (pattern 152)
#guard !hDom 164 (leafPlace 9 10 5) 12 (pattern 32) (pattern 80 ++ zeroBytes 31 ++ ⟨#[1]⟩ ++ pattern 40) && !hDom 164 (leafPlace 9 10 5) 12 (pattern 32) (pattern 80 ++ ⟨#[1]⟩ ++ zeroBytes 31 ++ pattern 40)
-- the binding tree's leaves, a stored tree's leaves: the tree's number is 0
#guard hDom 173 (leafPlace 0 4 5) 12 (pattern 32) (pattern 72) && !hDom 173 (leafPlace 1 4 5) 12 (pattern 32) (pattern 72) && hDom 174 (leafPlace 0 4 5) 12 (pattern 32) (pattern 72) && !hDom 174 (leafPlace 1 4 5) 12 (pattern 32) (pattern 72)
-- under a number that is no leaf's, 162 apart, the place holds nothing: no W, no s8
#guard !hDom 166 (leafPlace 0 1 5) 0 (pattern 32) (pattern 64) && !hDom 168 (leafPlace 0 1 5) 0 (zeroBytes 32) (pattern 48)
-- a content of no word is outside
-- (R2.3)
#guard !hDom 164 (leafPlace 9 0 5) 12 (pattern 32) (pattern 40) && hDom 164 (leafPlace 9 1 5) 12 (pattern 32) (pattern 48)
-- two shapes that would give one string if a leaf's label did not hold its shape: a
-- content of 3 words with a salt of 40 bytes,
-- of 1 word with a salt of 56: the same 64 bytes behind the label, two labels
#guard hDom 164 (leafPlace 9 1 7) 12 (pattern 32) (pattern 64) && (oStr 0 164 (leafPlace 9 1 7) 12 (pattern 32) (pattern 64)).data != (oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)).data
-- under 162 the chain's label stands in the tree's place: below 2^48
#guard hDom 162 (2 ^ 32) 3 (pattern 32) (pattern 16) && hDom 162 (2 ^ 48 - 1) 3 (pattern 32) (pattern 16) && !hDom 162 (2 ^ 48) 3 (pattern 32) (pattern 16)
-- a vertex: no tree; index 0; a start (32 zero bytes are a start too)
#guard hDom 166 0 0 (pattern 32) (pattern 64) && hDom 178 0 0 (pattern 32) (pattern 64) && hDom 166 0 0 (zeroBytes 32) (pattern 64)
#guard !hDom 166 9 0 (pattern 32) (pattern 64) && !hDom 166 0 5 (pattern 32) (pattern 64) && !hDom 178 1 0 (pattern 32) (pattern 64) && !hDom 178 0 1 (pattern 32) (pattern 64)
-- the named values of the index
#guard hDom 169 0 0 (zeroBytes 32) ByteArray.empty && hDom 169 0 1 (zeroBytes 32) ByteArray.empty && hDom 169 0 2 (zeroBytes 32) ByteArray.empty && !hDom 169 0 3 (zeroBytes 32) ByteArray.empty && hDom 176 0 0 (zeroBytes 32) ByteArray.empty && !hDom 176 0 1 (zeroBytes 32) ByteArray.empty
-- a string read back
#guard (oParse (oStr 0 164 (leafPlace 9 1 5) (2 ^ 33 + 12) (pattern 32) (pattern 48))).any fun q =>
  q.half == 0 && q.number == 164 && q.tree == leafPlace 9 1 5 && placeTree q.tree == 9 && placeW q.tree == 1 && placeS q.tree == 5 && q.index == 2 ^ 33 + 12 && q.start.data == (pattern 32).data && q.bytes.data == (pattern 48).data
#guard (oParse (oStr 1 162 (2 ^ 32) 3 (pattern 32) (pattern 4))).any fun q =>
  q.half == 1 && q.number == 162 && q.tree == 2 ^ 32 && q.index == 3 && q.start.data == (pattern 32).data && q.bytes.data == (pattern 4).data && oUsed q
#guard (oParse (oStr 0 168 0 0 (zeroBytes 32) ByteArray.empty)).any fun q => q.number == 168 && q.bytes.size == 0
-- in the image the oracle is formatHash, half by half
#guard (oracle (oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))).data == (formatHash 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)).data
#guard (oracle (oStr 0 162 (2 ^ 32) 3 (pattern 32) (pattern 16)) ++ oracle (oStr 1 162 (2 ^ 32) 3 (pattern 32) (pattern 16))).data == (formatHash 162 (2 ^ 32) 3 (pattern 32) (pattern 16)).data
#guard (oracle (oStr 0 168 0 5 (zeroBytes 32) (pattern 128))).data == (formatHash 168 0 5 (zeroBytes 32) (pattern 128)).data
-- the tie: the hash over the realised oracle is the direct call, at six of the eight known hashes,
-- under 162 at other bytes, and at each number of the table
#guard (HO oracle 168 0 0 (zeroBytes 32) ByteArray.empty).data == (formatHash 168 0 0 (zeroBytes 32) ByteArray.empty).data
#guard (HO oracle 168 0 5 (zeroBytes 32) (pattern 128)).data == (formatHash 168 0 5 (zeroBytes 32) (pattern 128)).data
#guard (HO oracle 168 0 (2 ^ 33 + 5) (zeroBytes 32) (pattern 129)).data == (formatHash 168 0 (2 ^ 33 + 5) (zeroBytes 32) (pattern 129)).data
#guard (HO oracle 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)).data == (formatHash 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)).data
#guard (HO oracle 166 0 0 (pattern 32) (pattern 64)).data == (formatHash 166 0 0 (pattern 32) (pattern 64)).data
#guard (HO oracle 178 0 0 (pattern 32) (pattern 64)).data == (formatHash 178 0 0 (pattern 32) (pattern 64)).data
#guard (HO oracle 162 (2 ^ 32) 3 (pattern 32) (pattern 16)).data == (formatHash 162 (2 ^ 32) 3 (pattern 32) (pattern 16)).data
#guard (HO oracle 162 0 3 (pattern 32) (pattern 16)).data == (formatHash 162 0 3 (pattern 32) (pattern 16)).data
#guard numbers.all fun n =>
  let t := if n == 173 || n == 174 then leafPlace 0 1 5 else if isLeaf n then leafPlace 7 1 5 else if hasTree n then 7 else 0
  let i := if idxOK n 5 then 5 else 0
  let s := if hasStart n then pattern 32 else zeroBytes 32
  hDom n t i s (pattern 48) && (HO oracle n t i s (pattern 48)).data == (formatHash n t i s (pattern 48)).data && (formatHash n t i s (pattern 48)).size == dlen n
-- outside the domain, at one call under the number 177, they part: its string is outside the image
#guard (HO oracle 177 0 0 (zeroBytes 32) ByteArray.empty).data == (oOut (oStr 0 177 0 0 (zeroBytes 32) ByteArray.empty)).data
#guard (HO oracle 177 0 0 (zeroBytes 32) ByteArray.empty).data != (formatHash 177 0 0 (zeroBytes 32) ByteArray.empty).data
-- not read back: too short; a first byte that is reserved; a number that is not given out; a block
-- that does not fit its label
#guard (oParse (pattern 80)).isNone && (oParse ByteArray.empty).isNone
#guard (oParse (oStr 2 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))).isNone && (oParse (oStr 255 168 0 0 (zeroBytes 32) ByteArray.empty)).isNone
#guard (oParse (oStr 0 177 0 0 (zeroBytes 32) ByteArray.empty)).isNone && (oParse (oStr 0 161 0 0 (zeroBytes 32) ByteArray.empty)).isNone
#guard (oParse (oStr 0 168 0 0 (pattern 32) ByteArray.empty)).isNone && (oParse (oStr 0 168 3 0 (zeroBytes 32) ByteArray.empty)).isNone
#guard (oParse (⟨#[0]⟩ ++ pblock 162 (pattern 32) ++ label 164 (leafPlace 9 3 5) 12 ++ pattern 64)).isNone    -- digest length 64 over a label with the number 164
#guard (oParse (⟨#[0]⟩ ++ pblock 164 (pattern 32) ++ label 162 0 3 ++ pattern 16)).isNone    -- digest length 32 over a label with the number 162
#guard (oParse (⟨#[0, 32, 1, 1, 1]⟩ ++ zeroBytes 28 ++ pattern 32 ++ label 164 (leafPlace 9 3 5) 12 ++ pattern 64)).isNone    -- a key length that is not 0
#guard (oParse (⟨#[0, 32, 0, 1, 1]⟩ ++ zeroBytes 27 ++ ⟨#[1]⟩ ++ pattern 32 ++ label 164 (leafPlace 9 3 5) 12 ++ pattern 64)).isNone    -- a byte of the block's middle that is not 0
-- the image, on both sides
#guard inImage (oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64)) && inImage (oStr 0 162 0 3 (pattern 32) (pattern 16)) && inImage (oStr 1 162 0 3 (pattern 32) (pattern 16)) && inImage (oStr 0 168 0 0 (zeroBytes 32) ByteArray.empty)
#guard inImage (oStr 0 166 0 0 (pattern 32) (pattern 64)) && inImage (oStr 0 178 0 0 (pattern 32) (pattern 64)) && inImage (oStr 1 162 (2 ^ 32) 3 (pattern 32) (pattern 16))
#guard numbers.all fun n => inImage (oStr 0 n (if n == 173 || n == 174 then leafPlace 0 1 5 else if isLeaf n then leafPlace 7 1 5 else if hasTree n then 7 else 0) (if idxOK n 5 then 5 else 0) (if hasStart n then pattern 32 else zeroBytes 32) (pattern 48))
#guard numbers.all fun n => inImage (oStr 1 n (if n == 173 then leafPlace 0 1 5 else if isLeaf n then leafPlace 7 1 5 else if hasTree n then 7 else 0) (if idxOK n 5 then 5 else 0) (if hasStart n then pattern 32 else zeroBytes 32) (pattern 48)) == (n == 162)
#guard [ByteArray.empty, pattern 7, pattern 80, pattern 200, oStr 2 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64), oStr 1 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64), oStr 0 177 0 0 (zeroBytes 32) ByteArray.empty,
  oStr 0 161 0 0 (zeroBytes 32) ByteArray.empty, oStr 0 168 0 0 (pattern 32) ByteArray.empty, oStr 0 168 3 0 (zeroBytes 32) ByteArray.empty, oStr 0 168 0 (2 ^ 63) (zeroBytes 32) ByteArray.empty,
  oStr 0 164 65536 12 (pattern 32) (pattern 64), oStr 0 166 9 12 (pattern 32) (pattern 64), oStr 0 166 0 5 (pattern 32) (pattern 64), oStr 1 166 0 0 (pattern 32) (pattern 64), oStr 0 169 0 3 (zeroBytes 32) (pattern 8),
  oStr 0 176 0 1 (zeroBytes 32) ByteArray.empty, oStr 0 178 0 1 (pattern 32) (pattern 64)].all fun s => !inImage s && (oracle s).data == (oOut s).data
-- the oracle outside the image: ten values, each one call of a public implementation of BLAKE2b
-- (this library's own ruling: the page rules nothing there)
#guard hex (oracle ByteArray.empty) == "95a9b60608b3ac62e989a80c00bf42fbdf9218ac6e1c59b9a061c5133a71171f"
#guard hex (oracle (pattern 7)) == "3e9d8216fe31a76e94efba83619be57efd3dc2b519fece682eeb8f9f6ef61ac5"
#guard hex (oracle (pattern 80)) == "deb0ad441d399651b18337be0dd3261b02090bb5e552e0f96dca355598fb9e7e"
#guard hex (oracle (pattern 200)) == "3343b033b3d8dcde44e7107bf443dd522fd1552e3537a3e990f215522acfcb2f"
#guard hex (oracle (oStr 2 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))) == "214c60b87c40179f4ca773d1d481536c16b107918fdea4d517c0cc5399cf32a4"
#guard hex (oracle (oStr 1 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))) == "02a7f033d454cb4fc438ede5e28654142e66680e5a12aec8b565397a209ee034"
#guard hex (oracle (oStr 0 177 0 0 (zeroBytes 32) ByteArray.empty)) == "c3844a314d70b0ec69cec12840e04fb1d137c42a22b6d957483cd181290ec512"
#guard hex (oracle (oStr 0 166 9 12 (pattern 32) (pattern 64))) == "29cf0a5457ad0055550ff15c95c3ba1eba71107b81185e4f677a6e6bffc83d2d"    -- a vertex with a tree's number
#guard hex (oracle (oStr 0 166 0 5 (pattern 32) (pattern 64))) == "529a315bcf5eec20e334575c313657594b9644d06ade463cbdf0b64535822fe8"    -- a vertex with an index that the table does not name
#guard hex (oracle (oStr 0 169 0 3 (zeroBytes 32) (pattern 8))) == "855482c094552ab75c061aed162e4799294bcbd0bfccca90713187d2e80b8746"
-- the half 1 under a digest length of 32: read back, not used
#guard (oParse (oStr 1 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64))).any fun q => !oUsed q
-- the oracle's answers have 32 bytes at five strings (for all: `size_oracle`, Fmt/Rules23Laws.lean)
#guard [oStr 0 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64), oStr 1 162 0 3 (pattern 32) (pattern 16), oStr 1 164 (leafPlace 9 3 5) 12 (pattern 32) (pattern 64), pattern 7, pattern 200].all fun s => (oracle s).size == 32
-- the cost: a vertex (label and two digests: 80 bytes) is one call of the compression function
#guard nComp (label 166 0 0 ++ pattern 64).size == 1 && nComp 128 == 1 && nComp 129 == 2

/-! ### Further answers, not among the page's known answers: made for this file with the page's own
program: every number of the table but 179, inside the domain. Numbers that are no leaf's (its
function H, in an edition that is neither the one rendered here nor the one that ships; the rules
on them are the same in it and in the one rendered here): at 0, 111, 112, 113 and 240 bytes (around
the end of a block of 128, the label counted). The three numbers of leaves (another edition,
whose labels hold a leaf's shape: its functions leaf, leaf_bytes, H; under 174 at the tree's number
0, with the H of the edition rendered here): contents of 1, 9,
10, 6, 25 words with salts of 5, 5, 5, 8, 6 words: without a fill, up to a block's end, with a fill
-/

#guard hex (formatHash 160 0 9 zero32 (pattern 0)) = "48632b468043bd45c043dc0d46ed72b2206281f3167d2ee07fb6fd94059e241c"
#guard hex (formatHash 160 0 9 zero32 (pattern 111)) = "598c6e406f747e5466fee45e1a68c4037a4fcf2d93753c3801d53a30e8e3549f"
#guard hex (formatHash 160 0 9 zero32 (pattern 112)) = "6978c052263334f493915d21073a78219c0570f22f21e8285b67a8e4c7acd595"
#guard hex (formatHash 160 0 9 zero32 (pattern 113)) = "458e45b58bed2d65a3b4119c6fb3cba84dcf9ea336f87af0fb483610d01350c8"
#guard hex (formatHash 160 0 9 zero32 (pattern 240)) = "4789de8dcfc5b8567dc0512e47c5d353b9a2a1b2c8bca38ec28c61a6ce011c60"
#guard hex (formatHash 162 3 9 (pattern 32 5 1) (pattern 0)) = "47ee288ec6abb7b02dfbc243ae925d7c459de902ac17d68de41f50da5f03fd7af61f5969a83c3c35d6bff30b9a0200b44195e8328c06a07e0761cfd58c69b524"
#guard hex (formatHash 162 3 9 (pattern 32 5 1) (pattern 111)) = "97f09b7538686c75f9c98f825cc124b4d76f39c6eec71d31be92f578504a08a339e25d6caafae22b21f45042307ffc8080529d478502d1d060c1457e6f49ebc5"
#guard hex (formatHash 162 3 9 (pattern 32 5 1) (pattern 112)) = "6fca660076ce0debf35c9c0b7ff04aa611a375e49be5edf0595d6e232bd8dcc4cffd20c1f0b51c9d6080d02c036d493105c75e350f1c18ef3b4f57653d5c6613"
#guard hex (formatHash 162 3 9 (pattern 32 5 1) (pattern 113)) = "8126d769caac4e66bcc9eb9f5f1a5d335495bdcffb877f1e7c4c5d1378e06994ab9c776ccc2ca55acfc8924ee637a0fd5bbc50c7a95fdfca9863b810a1ab2f29"
#guard hex (formatHash 162 3 9 (pattern 32 5 1) (pattern 240)) = "8d76eccce8b843dd5d545aaa368080f14d6e37bdf6e1c5f1dea8f0e5f29f9a32f54ce5ca326b1630c5b3697be19e426e8f1373f3e1a7143f54cfb1bf4c1dea03"
#guard hex (formatHash 164 (leafPlace 3 1 5) 9 (pattern 32 5 1) (pattern 8 ++ zeroBytes 0 ++ pattern 40 5 1)) = "15a1265c986709927380ffb82defc301c2d6e6818b6df57e132e4642fa5b324c"
#guard hex (formatHash 164 (leafPlace 3 9 5) 9 (pattern 32 5 1) (pattern 72 ++ zeroBytes 0 ++ pattern 40 5 1)) = "63e8e0dc988dc9a1e322206dc1de4b369a015e0a230ab71c564cf3ea6ff79864"
#guard hex (formatHash 164 (leafPlace 3 10 5) 9 (pattern 32 5 1) (pattern 80 ++ zeroBytes 32 ++ pattern 40 5 1)) = "fb13bb20dc23ebafbe819eb869cf609294fac91f089898b23c6c24054f169d31"
#guard hex (formatHash 164 (leafPlace 3 6 8) 9 (pattern 32 5 1) (pattern 48 ++ zeroBytes 0 ++ pattern 64 5 1)) = "7cab14a3fa5610f23ca288fb97814598c12311c92b914db7b5173d71e99f4ad5"
#guard hex (formatHash 164 (leafPlace 3 25 6) 9 (pattern 32 5 1) (pattern 200 ++ zeroBytes 40 ++ pattern 48 5 1)) = "5164fa44b186f62493c95e5132e86e29d5ed6753390cc353de26c2b5481b018f"
#guard hex (formatHash 166 0 0 (pattern 32 5 1) (pattern 0)) = "9183c1346d98007d89b91f374cf124121bda288bdb42c8785bec15ddbb148b4d"
#guard hex (formatHash 166 0 0 (pattern 32 5 1) (pattern 111)) = "7418959d3e56744a24b81532b43092e1e2c8081519232ca87671d4c5b6d7f26e"
#guard hex (formatHash 166 0 0 (pattern 32 5 1) (pattern 112)) = "d0adf632e0a8ffc6a3970964d2bfc0fac3636ea8cffe06ab84ccd4baadcf6d72"
#guard hex (formatHash 166 0 0 (pattern 32 5 1) (pattern 113)) = "c99181c8353b36d999e4a6916be464bf53b69ede313887d44abc2fec27a40e45"
#guard hex (formatHash 166 0 0 (pattern 32 5 1) (pattern 240)) = "a8e8d36d7916d8fe36daecac8cb320b51fd5016aa16b1c8ead970b37e99a408b"
#guard hex (formatHash 168 0 9 zero32 (pattern 0)) = "ad84762370fc92d71e62700700361e2f45f3a50bb5d8ee2d6f26eef512643ad9"
#guard hex (formatHash 168 0 9 zero32 (pattern 111)) = "9908d84da63109ac4064f620af7f2b180577f7d144c2307346d3c6cbafd91ddf"
#guard hex (formatHash 168 0 9 zero32 (pattern 112)) = "d1e01127fd70e31718d9b31b530fdc591c94ff200c0d1a070fd6ab3139f5a9fa"
#guard hex (formatHash 168 0 9 zero32 (pattern 113)) = "b4a956fd77ee67361931a2fc1b2fd28c9a8cba2afbf5217929cd0f6fa7632f51"
#guard hex (formatHash 168 0 9 zero32 (pattern 240)) = "b3f7600f10294e4e6664332b8ab7b9aa1c250ca5dc8dbd21eb47b7b59efc6ccc"
#guard hex (formatHash 169 0 1 zero32 (pattern 0)) = "e6e8abc3205ed66a8e9cbf74c0ebba90d0379bfec77fda5fa673dc5c538ced0a"
#guard hex (formatHash 169 0 1 zero32 (pattern 111)) = "d15bcbb45730842c21cbfc46e613f10c343d1689e08534d208caa4a00cf71a65"
#guard hex (formatHash 169 0 1 zero32 (pattern 112)) = "7db7c0fc3d84d05274dc3fce5cf783ba18699d3476db18685640f71dec71014f"
#guard hex (formatHash 169 0 1 zero32 (pattern 113)) = "f8a3abec0fdee303a243bab18e88c9f2382e06a0b09748217471585c478524e2"
#guard hex (formatHash 169 0 1 zero32 (pattern 240)) = "5ec2c9d3197c35aafc7cc080eaf45ff493ca92cf60d1e0ab76369db99982897f"
#guard hex (formatHash 171 0 9 (pattern 32 5 1) (pattern 0)) = "7350e4b753160260c9190f2310f77bd26418d73cd1be9409f112e7263d30247e"
#guard hex (formatHash 171 0 9 (pattern 32 5 1) (pattern 111)) = "a7cacd95c16b17badcaddd560154ae76f8d831efa4dc2b6f618e451e7a00957b"
#guard hex (formatHash 171 0 9 (pattern 32 5 1) (pattern 112)) = "176639c36682fee110a9004fd4f586f0b3ac96ea0cfc396279fca1a38f2f7a59"
#guard hex (formatHash 171 0 9 (pattern 32 5 1) (pattern 113)) = "fa556bfb7eb48a4243efe8d105644e1b20cf2b4b8c1681f5ef5cf284f1bcbb28"
#guard hex (formatHash 171 0 9 (pattern 32 5 1) (pattern 240)) = "d6d9d52b31d7e5ee93b016a09ea0a04296b1497bcd42edc2d8274b0acdaef1d0"
#guard hex (formatHash 172 0 9 zero32 (pattern 0)) = "470ff40d563a84a132a487f33eabfd5d898937a236a28cbbb8ec6d9959eb9163"
#guard hex (formatHash 172 0 9 zero32 (pattern 111)) = "6d964110f701c1f2d5578f83c487c77c021c6c9c97d6edfeb1e9996b27ece4e6"
#guard hex (formatHash 172 0 9 zero32 (pattern 112)) = "85d56de7c0f948a104966b16fcf61864cee158799902589a39426a9e2875d337"
#guard hex (formatHash 172 0 9 zero32 (pattern 113)) = "68d222ffa04a6e095b71d7aa6b57ee4900ce57a224c39e6aaa27d227208181f2"
#guard hex (formatHash 172 0 9 zero32 (pattern 240)) = "3922f00f58fff729fca0c91f83b34ceccedfa08729997120f8f2ed0206049be5"
#guard hex (formatHash 173 (leafPlace 0 1 5) 9 (pattern 32 5 1) (pattern 8 ++ zeroBytes 0 ++ pattern 40 5 1)) = "5abfd85be4bdcc007057a82a5b5a1d59c79df77a164576901993fe964d34bfa7"
#guard hex (formatHash 173 (leafPlace 0 9 5) 9 (pattern 32 5 1) (pattern 72 ++ zeroBytes 0 ++ pattern 40 5 1)) = "cf088b5a66fa4aff3daa07aa7887cbb113574c706e345874eeef755b15c814c2"
#guard hex (formatHash 173 (leafPlace 0 10 5) 9 (pattern 32 5 1) (pattern 80 ++ zeroBytes 32 ++ pattern 40 5 1)) = "975f0987773e653bbdaf3c04f6a318d8fbd56cdfb8d4814a072be5fd35fa0402"
#guard hex (formatHash 173 (leafPlace 0 6 8) 9 (pattern 32 5 1) (pattern 48 ++ zeroBytes 0 ++ pattern 64 5 1)) = "1655528165075a888be10a1b387f7a0111fb6d9ead985878ed9fc9bc09cf6949"
#guard hex (formatHash 173 (leafPlace 0 25 6) 9 (pattern 32 5 1) (pattern 200 ++ zeroBytes 40 ++ pattern 48 5 1)) = "bd4691c18c324f01f3420b0b95384a2e3098c4bfae84011d48a92f33089f0450"
#guard hex (formatHash 174 (leafPlace 0 1 5) 9 (pattern 32 5 1) (pattern 8 ++ zeroBytes 0 ++ pattern 40 5 1)) = "11a0d0601ae605c94cdca7469b2965b9d756a6aebc9bafe2520dc2e0cde578a6"
#guard hex (formatHash 174 (leafPlace 0 9 5) 9 (pattern 32 5 1) (pattern 72 ++ zeroBytes 0 ++ pattern 40 5 1)) = "123f3b96899b287b906f4320551d9ed7dab7df0a50e1afde4ddc3d225a4e0f34"
#guard hex (formatHash 174 (leafPlace 0 10 5) 9 (pattern 32 5 1) (pattern 80 ++ zeroBytes 32 ++ pattern 40 5 1)) = "086100febfeb7f2427fc8e43c94427c975700cf342336d641562d6955600ad80"
#guard hex (formatHash 174 (leafPlace 0 6 8) 9 (pattern 32 5 1) (pattern 48 ++ zeroBytes 0 ++ pattern 64 5 1)) = "4bf7f724271a4fc5dd65fa037489d3c586b5d8967aa36bc2865e7f0e90b7a4a7"
#guard hex (formatHash 174 (leafPlace 0 25 6) 9 (pattern 32 5 1) (pattern 200 ++ zeroBytes 40 ++ pattern 48 5 1)) = "550c3741ac0189f084cc35de8cf0198127698eea3e577ef19e20bb16bddb99f7"
#guard hex (formatHash 176 0 0 zero32 (pattern 0)) = "ad2b900472b50492d7eae733cf4745f7cae9d57b7b8c02856ee8e4e957441054"
#guard hex (formatHash 176 0 0 zero32 (pattern 111)) = "a302031990bb118b23e96ab1f0bf91862b35cc66b38acd27fe97f58238a56432"
#guard hex (formatHash 176 0 0 zero32 (pattern 112)) = "b6157e2e7744580e489b08abe7ae85424fd4ab5a91ddad93289b4589832902e4"
#guard hex (formatHash 176 0 0 zero32 (pattern 113)) = "605147c9beb8a431745aded5794f55c6e5c933cb8c1cf80caa81014ec79e99e9"
#guard hex (formatHash 176 0 0 zero32 (pattern 240)) = "da698990e5d7788c08a56806042fb99b68af3c6abddb299417b715116d22f137"
#guard hex (formatHash 178 0 0 (pattern 32 5 1) (pattern 0)) = "b38973bd2ca8a30abef6eb3ccb6360c986ab13214e7937b9e333415ef23fcf1b"
#guard hex (formatHash 178 0 0 (pattern 32 5 1) (pattern 111)) = "0ce2a6595ceb19f402859cec352dd11cb023f5f40475ac7d3b89d375a84344f7"
#guard hex (formatHash 178 0 0 (pattern 32 5 1) (pattern 112)) = "2408747e44babbcfa08ec01293405f267f4f1dbc16cf5ed0bb797c0b1dfef5ca"
#guard hex (formatHash 178 0 0 (pattern 32 5 1) (pattern 113)) = "b1ca6bbe3b1d3bd1d5326c77f89a0146ef010adb8c554cb3b673117680edd194"
#guard hex (formatHash 178 0 0 (pattern 32 5 1) (pattern 240)) = "70ebb2c528809aab9cf1cf618194438fb91b74506e5f31e6cfaee2303bdf89e6"

end Fmt
