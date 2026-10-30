-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules1.lean: how words, field elements, digests, texts, lists, pairs and small values are
spelled as bytes, with readers that refuse.

In standard terms: the serialisation of the format's basic values into bytes, and parsers that
reject malformed input. All other files of Fmt/ stand on this one. Every function is total. The
programs are the C++ implementation that comes with this Lean code.

Sources. Section 1 (R1.1 to R1.9) of the format page (docs/format/FORMAT.md); this file is not
held against the page as it ships, and may differ from it.
The page's known answers stand as tests. No Mathlib; the file imports nothing.




1. What the file contains, rule by rule. Definitions that can be evaluated.
   R1.1 a word. An integer below 2^64: `u64`, `u64n`, `wordAt`.
   The order of bits. This library's own, fixed here once for all files: the page speaks of words
     and of their low bits, never of "bit i of a string". With `bitAt` "the first w bits of a block"
     are the page's "low w bits of its first word" (w at most 64).
   R1.2, R1.4 the two fields. `Fld.one`: p = 2^61 - 1, c = 5. `Fld.two`: p = 2^64 - 2^32 + 1, c = 2.
     The extension field is F[X] / (X^3 - c). Tests: 3 divides p - 1 and c^((p-1)/3) is not 1 modulo
     p, in both fields (so, p being prime, c is no cube).
   R1.3, R1.4 an element of F. A UInt64 below p (`Fld.ok`), spelled as that word (`elt`). Of E: a
     triple (e_0, e_1, e_2), spelled in this order: 24 bytes (`ext`).
   R1.5 a digest. Any 32 bytes, read as four words: `digestWord d i` = the word at byte 8 i.
   R1.6 a text, and any other string of bytes
   (by R1.7 a string of bytes is no list of
     integers). The word of its length, then its bytes as they are (`text`: it takes any bytes;
     `textS` for a name given as a Lean string).
   R1.7 a list (`list`). A pair (`pair`).
   R1.8 an integer, a truth value, a member of an enumeration. One word (`u64n`; `bool`;
     `enum num x`: the word of x's number).
   R1.9 By the page: the rules hold for hashed strings and for files alike. What a reader refuses,
     by the page: 8 bytes whose word is not below p (R1.3), a triple if one of its three is refused
     (R1.4); a truth value that is not 0 or 1 (`rdBool`); a member of an enumeration that is none of
     its numbers (`rdEnum`); the word of a length that is greater than the number of bytes left
     (`rdText`, `rdName`, `rdList`); a name with a byte outside 0x20 .. 0x7E (`rdName`). In `rdList`
     the length counts values, each of at least one byte, so the same test holds (the page's own
     word; not held against the page that ships);
     there it is made before a value is read.
   This library's own, not the page's (this section is silent): a reader of a kind of fixed length
     (word, element, digest) refuses if the bytes end too early. The writer's side never refuses:
     `elt` and `ext` spell any words, also words not below p; `ascii` spells any Lean string by its
     UTF-8 bytes, also one that is no name; `rdText` takes all bytes. A text is a string of bytes;
     only a name is held to the range.
   Two different maps from a word to an element, side by side so that nobody takes one for the
     other:
      `rdElt` / `Fld.ok`. Reading a spelling: the word itself, refused if not below p.
      `Fld.tryWord`. A try in a draw (R6.3, the section on drawing): field 1 takes the low 61 bits
        and fails if they are p; field 2 takes the word and fails if it is not below p. A word is
        never reduced modulo p. In field 1 the word 2^61 is no spelling, and as a try it is the
        element 0.
   `readF`, `readE`, `slice`. The same readers (`rdElt`, `rdExt`, `rdBytes`; `Rd`) for callers that
     keep the place themselves.
   `pattern`. The test strings of the page's known answers.
   Helpers for all sections' definitions and tests (no rule of the page): `hex`, `unhex`,
     `zeroBytes`, `zero32`, `fit`, `ascii`, `cat`.
   `byteAt` reads the byte in place (in the evaluator the time of a read by b.data grows with the
     string's length).

2. What is checked when the file compiles. 65 tests (#guard). Among them the page's ten known
answers on tries (its section on drawing) and its nine on eight bytes as a spelling (this section).

3. Theorems. One: `byteAt_eq` (`byteAt` is b.data.getD i 0 by definition).

4. What is not claimed, or stands elsewhere. That readers and spellings are inverse to each other,
on the values that those theorems call ok, under their hypotheses: Fmt/Rules1Laws.lean,
Fmt/Rules1Only.lean. The order of bits against words (for k < 64, `bitAt b k` is bit k of the word
at the place 0): Fmt/Rules5Laws.lean. Arithmetic of the fields: Fmt/FieldE.lean. Which of these
rules hold for files and which only for what enters a hash.

Terms: lean/GLOSSARY.md.
-/

namespace Fmt

/-! ## Words -/

/-- a word, spelled: 8 bytes, the lowest first -/
def u64 (x : UInt64) : ByteArray :=
  ⟨#[x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8, (x >>> 32).toUInt8,
    (x >>> 40).toUInt8, (x >>> 48).toUInt8, (x >>> 56).toUInt8]⟩

/-- the same of a natural number, taken modulo 2^64 -/
def u64n (x : Nat) : ByteArray := u64 (UInt64.ofNat x)

/-- the byte at a place; 0 beyond the end -/
def byteAt (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

/-- the same by the array of the bytes -/
theorem byteAt_eq (b : ByteArray) (i : Nat) : byteAt b i = b.data.getD i 0 := rfl

/-- the word at the bytes i .. i + 7, the lowest first -/
def wordAt (b : ByteArray) (i : Nat) : UInt64 :=
  (byteAt b i).toUInt64 ||| ((byteAt b (i + 1)).toUInt64 <<< 8) |||
    ((byteAt b (i + 2)).toUInt64 <<< 16) ||| ((byteAt b (i + 3)).toUInt64 <<< 24) |||
    ((byteAt b (i + 4)).toUInt64 <<< 32) ||| ((byteAt b (i + 5)).toUInt64 <<< 40) |||
    ((byteAt b (i + 6)).toUInt64 <<< 48) ||| ((byteAt b (i + 7)).toUInt64 <<< 56)

/-- Bit i of a string of bytes: bit (i mod 8), counted from the lowest, of byte (i div 8); false
beyond the end. So the first 64 bits of a string are the bits of its first word, the lowest first.
-/
def bitAt (b : ByteArray) (i : Nat) : Bool :=
  ((byteAt b (i / 8)) >>> (UInt8.ofNat (i % 8))) &&& 1 == 1

/-- the test strings of the known answers -/
def pattern (n : Nat) (a : Nat := 7) (b : Nat := 3) : ByteArray :=
  ⟨Array.ofFn (n := n) fun i => UInt8.ofNat ((a * i.val + b) % 251)⟩

/-- n zero bytes -/
def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- 32 zero bytes -/
def zero32 : ByteArray := zeroBytes 32

/-- cut to n bytes, or filled up with zero bytes -/
def fit (n : Nat) (b : ByteArray) : ByteArray :=
  if n ≤ b.size then b.extract 0 n else b ++ zeroBytes (n - b.size)

/-- n bytes from a place; refused beyond the end -/
def slice (b : ByteArray) (i n : Nat) : Option ByteArray :=
  if i + n ≤ b.size then some (b.extract i (i + n)) else none

/-- a digit of base 16, lower case -/
def hexDigit (x : UInt8) : Char :=
  if x < 10 then Char.ofNat (48 + x.toNat) else Char.ofNat (87 + x.toNat)

/-- bytes as a string of base 16: lower case, two digits a byte -/
def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun (x : UInt8) => [hexDigit (x >>> 4), hexDigit (x &&& 15)])

/-- the value of a digit of base 16; whatever is no digit counts 0 -/
def unhexDigit (c : Char) : UInt8 :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then UInt8.ofNat (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then UInt8.ofNat (n - 87)
  else if 65 ≤ n ∧ n ≤ 70 then UInt8.ofNat (n - 55)
  else 0

def unhexL : List Char → List UInt8
  | a :: b :: l => ((unhexDigit a <<< 4) ||| unhexDigit b) :: unhexL l
  | _ => []

/-- a string of base 16 as bytes; a last digit without a partner is dropped -/
def unhex (s : String) : ByteArray := ⟨(unhexL s.toList).toArray⟩

/-- the bytes of a name -/
def ascii (s : String) : ByteArray := s.toUTF8

/-- all strings of a list, one after the other -/
def cat (l : List ByteArray) : ByteArray := l.foldl (· ++ ·) ByteArray.empty

/-! ## The two fields -/

inductive Fld where
  | one
  | two
  deriving DecidableEq, Repr

def Fld.p : Fld → Nat
  | .one => 2305843009213693951
  | .two => 18446744069414584321

def Fld.c : Fld → Nat
  | .one => 5
  | .two => 2

/-- the word is the spelling of an element -/
def Fld.ok (f : Fld) (w : UInt64) : Bool := decide (w.toNat < f.p)

/-- A try in a draw (not a reader) -/
def Fld.tryWord : Fld → UInt64 → Option UInt64
  | .one, w => let x := w &&& 0x1FFFFFFFFFFFFFFF; if x.toNat < Fld.one.p then some x else none
  | .two, w => if w.toNat < Fld.two.p then some w else none

/-- b^e modulo m -/
def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 % m
  else
    let r := powMod (b * b % m) (e / 2) m
    if e % 2 = 1 then b * r % m else r
termination_by e

/-! ## Spellings -/

/-- an element of F -/
def elt (x : UInt64) : ByteArray := u64 x

/-- an element of E -/
def ext (e : UInt64 × UInt64 × UInt64) : ByteArray := u64 e.1 ++ u64 e.2.1 ++ u64 e.2.2

/-- word i of a digest -/
def digestWord (d : ByteArray) (i : Nat) : UInt64 := wordAt d (8 * i)

/-- a text -/
def text (b : ByteArray) : ByteArray := u64n b.size ++ b

/-- a name -/
def textS (s : String) : ByteArray := text (ascii s)

/-- a list of values of one kind -/
def list {α : Type} (sp : α → ByteArray) (l : List α) : ByteArray := u64n l.length ++ cat (l.map sp)

/-- a pair -/
def pair {α β : Type} (sa : α → ByteArray) (sb : β → ByteArray) (x : α × β) : ByteArray :=
  sa x.1 ++ sb x.2

/-- a truth value -/
def bool (b : Bool) : ByteArray := u64 (if b then 1 else 0)

/-- a member of an enumeration, by its number -/
def enum {α : Type} (num : α → Nat) (x : α) : ByteArray := u64n (num x)

/-- all bytes lie in 0x20 .. 0x7E -/
def isName (b : ByteArray) : Bool := b.data.all fun x => 0x20 ≤ x && x ≤ 0x7E

/-! ## Readers -/

/-- a reader: bytes, a place; a value and the place behind it, or a refusal -/
abbrev Rd (α : Type) : Type := ByteArray → Nat → Option (α × Nat)

def rdWord : Rd UInt64 := fun b i => if i + 8 ≤ b.size then some (wordAt b i, i + 8) else none

def rdElt (f : Fld) : Rd UInt64 := fun b i =>
  match rdWord b i with
  | some (w, j) => if f.ok w then some (w, j) else none
  | none => none

def rdPair {α β : Type} (ra : Rd α) (rb : Rd β) : Rd (α × β) := fun b i =>
  match ra b i with
  | some (x, j) =>
    match rb b j with
    | some (y, k) => some ((x, y), k)
    | none => none
  | none => none

def rdExt (f : Fld) : Rd (UInt64 × UInt64 × UInt64) := rdPair (rdElt f) (rdPair (rdElt f) (rdElt f))

/-- n bytes -/
def rdBytes (n : Nat) : Rd ByteArray := fun b i => (slice b i n).map fun x => (x, i + n)

def rdDigest : Rd ByteArray := rdBytes 32

def rdText : Rd ByteArray := fun b i =>
  match rdWord b i with
  | some (n, j) => rdBytes n.toNat b j
  | none => none

/-- n values, one after the other -/
def rdMany {α : Type} (r : Rd α) : Nat → Rd (List α)
  | 0 => fun _ i => some ([], i)
  | n + 1 => fun b i =>
    match r b i with
    | some (x, j) =>
      match rdMany r n b j with
      | some (l, k) => some (x :: l, k)
      | none => none
    | none => none

/-- a name: a text, refused if a byte lies outside the range -/
def rdName : Rd ByteArray := fun b i =>
  match rdText b i with
  | some (x, j) => if isName x then some (x, j) else none
  | none => none

def rdList {α : Type} (r : Rd α) : Rd (List α) := fun b i =>
  match rdWord b i with
  | some (n, j) => if j + n.toNat ≤ b.size then rdMany r n.toNat b j else none
  | none => none

def rdBool : Rd Bool := fun b i =>
  match rdWord b i with
  | some (w, j) => if w = 0 then some (false, j) else if w = 1 then some (true, j) else none
  | none => none

/-- a member of an enumeration: dec gives the member with a number, if there is one -/
def rdEnum {α : Type} (dec : Nat → Option α) : Rd α := fun b i =>
  match rdWord b i with
  | some (w, j) => (dec w.toNat).map fun x => (x, j)
  | none => none

/-- an element of F at a place: refused beyond the end and at a word not below p -/
def readF (f : Fld) (b : ByteArray) (i : Nat) : Option UInt64 := (rdElt f b i).map (·.1)

/-- an element of E at a place (24 bytes) -/
def readE (f : Fld) (b : ByteArray) (i : Nat) : Option (UInt64 × UInt64 × UInt64) :=
  (rdExt f b i).map (·.1)

/-- a reader on a whole string: refused if bytes are left -/
def whole {α : Type} (r : Rd α) (b : ByteArray) : Option α :=
  match r b 0 with
  | some (x, j) => if j = b.size then some x else none
  | none => none

/-! ## Tests -/

-- a word: the lowest byte first
#guard (u64 0x0102030405060708).data = #[8, 7, 6, 5, 4, 3, 2, 1]
#guard (u64n (2 ^ 64 + 5)).data = #[5, 0, 0, 0, 0, 0, 0, 0]
#guard wordAt (u64 0xFEDCBA9876543210) 0 = 0xFEDCBA9876543210
#guard wordAt (u64 0xFFFFFFFFFFFFFFFF) 4 = 0x00000000FFFFFFFF
#guard (List.range 10).map (bitAt (unhex "0502")) = [true, false, true, false, false, false, false, false, false, true]
#guard (List.range 64).all fun i => bitAt (u64 0xFEDCBA9876543210) i == (((0xFEDCBA9876543210 : UInt64) >>> (UInt64.ofNat i)) &&& 1 == 1)
#guard bitAt (u64 0xFFFFFFFFFFFFFFFF) 64 = false
#guard (pattern 4).data = #[3, 10, 17, 24]
#guard (pattern 3 250 1).data = #[1, 0, 250]
#guard byteAt (pattern 40) 36 = 4

#guard hex (u64 0x0102030405060708) = "0807060504030201" && hex (pattern 3 250 1) = "0100fa"
#guard unhex "0100fa" = pattern 3 250 1 && unhex "0100FA7" = pattern 3 250 1 && (unhex "").size = 0
#guard unhex (hex (pattern 300)) = pattern 300
#guard (zeroBytes 5).data = #[0, 0, 0, 0, 0] && zero32.size = 32
#guard fit 2 (pattern 4) = pattern 2 && hex (fit 6 (pattern 4)) = "030a11180000" && fit 4 (pattern 4) = pattern 4
#guard slice (pattern 4) 1 2 = some (unhex "0a11") && slice (pattern 4) 3 2 = none && slice (pattern 4) 4 0 = some ByteArray.empty

-- the two fields
#guard Fld.one.p = 2 ^ 61 - 1
#guard Fld.two.p = 2 ^ 64 - 2 ^ 32 + 1
#guard (Fld.one.p - 1) % 3 = 0 && powMod Fld.one.c ((Fld.one.p - 1) / 3) Fld.one.p != 1
#guard (Fld.two.p - 1) % 3 = 0 && powMod Fld.two.c ((Fld.two.p - 1) / 3) Fld.two.p != 1
#guard powMod Fld.one.c (Fld.one.p - 1) Fld.one.p = 1 && powMod Fld.two.c (Fld.two.p - 1) Fld.two.p = 1

-- the page's known answers: a word and its try
#guard Fld.two.tryWord 0 = some 0
#guard Fld.two.tryWord 18446744069414584320 = some 18446744069414584320
#guard Fld.two.tryWord 18446744069414584321 = none
#guard Fld.two.tryWord 18446744073709551615 = none
#guard Fld.one.tryWord 0 = some 0
#guard Fld.one.tryWord 2305843009213693950 = some 2305843009213693950
#guard Fld.one.tryWord 2305843009213693951 = none
#guard Fld.one.tryWord 2305843009213693952 = some 0
#guard Fld.one.tryWord 18446744073709551615 = none
#guard Fld.one.tryWord 18446744073709551614 = some 2305843009213693950

-- the page's known answers: eight bytes as the spelling of an element of F (R1.3)
#guard whole (rdElt .two) (unhex "0000000000000000") = some 0
#guard whole (rdElt .two) (unhex "00000000ffffffff") = some 18446744069414584320
#guard whole (rdElt .two) (unhex "01000000ffffffff") = none
#guard whole (rdElt .two) (unhex "ffffffffffffffff") = none
#guard whole (rdElt .one) (unhex "0000000000000000") = some 0
#guard whole (rdElt .one) (unhex "feffffffffffff1f") = some 2305843009213693950
#guard whole (rdElt .one) (unhex "ffffffffffffff1f") = none
#guard whole (rdElt .one) (unhex "0000000000000020") = none
#guard whole (rdElt .one) (unhex "ffffffffffffffff") = none

-- the same words as spellings: the reader is another map
#guard whole (rdElt .two) (u64 18446744069414584320) = some 18446744069414584320
#guard whole (rdElt .two) (u64 18446744069414584321) = none
#guard whole (rdElt .one) (u64 2305843009213693950) = some 2305843009213693950
#guard whole (rdElt .one) (u64 2305843009213693951) = none
#guard whole (rdElt .one) (u64 2305843009213693952) = none
#guard whole (rdElt .one) (u64 18446744073709551614) = none

-- spellings and their readers
#guard (ext (1, 2, 3)).size = 24 && whole (rdExt .one) (ext (1, 2, 3)) = some (1, 2, 3)
#guard whole (rdExt .one) (ext (1, 2305843009213693951, 3)) = none
#guard (textS "abc").data = #[3, 0, 0, 0, 0, 0, 0, 0, 97, 98, 99]
#guard (whole rdText (textS "abc")).map (·.data) = some #[97, 98, 99]
#guard whole rdText ((textS "abc").extract 0 10) = none
#guard (whole rdText (textS "abc" ++ u64 0)).isNone
#guard (list u64 [1, 2]).size = 24 && whole (rdList rdWord) (list u64 [1, 2]) = some [1, 2]
#guard whole (rdList rdWord) (u64 0xFFFFFFFFFFFFFFFF ++ u64 1) = none
#guard whole (rdList rdWord) (u64 9 ++ u64 1) = none && whole (rdList rdWord) (u64 0) = some []
#guard (whole rdName (textS "toy: claim")).isSome && (whole rdName (text (unhex "411f"))).isNone && (whole rdName (text (unhex "417f"))).isNone && (whole rdName (text (unhex "207e"))).isSome
#guard (whole rdText (text (unhex "411f"))).isSome && whole rdName (u64 4 ++ ascii "abc") = none
#guard whole (rdEnum fun n => if n = 1 then some true else if n = 2 then some false else none) (enum (fun b : Bool => if b then 1 else 2) false) = some false
#guard whole (rdEnum fun n => if n = 1 then some true else if n = 2 then some false else none) (u64 3) = none
#guard whole (rdPair rdText rdWord) (pair text u64 (pattern 5, 9)) = some (pattern 5, 9)
#guard whole rdBool (bool true) = some true && whole rdBool (bool false) = some false && whole rdBool (u64 2) = none
#guard (whole rdDigest (pattern 32)).isSome && (whole rdDigest (pattern 31)).isNone && (whole rdDigest (pattern 33)).isNone
#guard digestWord (u64 1 ++ u64 2 ++ u64 3 ++ u64 4) 2 = 3
#guard readF .two (u64 7 ++ u64 9) 8 = some 9 && readF .two (u64 7 ++ u64 9) 9 = none && readF .one (u64 2305843009213693951) 0 = none
#guard readE .two (u64 0 ++ ext (1, 2, 3)) 8 = some (1, 2, 3) && readE .two (ext (1, 2, 3)) 8 = none

end Fmt
