-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Codes.lean: the Reed-Solomon codes of the first toy (a product test), as functions that
compute: the point of a position, the symbol of a codeword at a position, the generator's row at a
position, and the spelling of the parameter item "codes".

The first toy (a product test) of the programs (the C++ implementation that comes with this Lean
code) encodes its rows with Reed-Solomon codes on cosets in field 2. This file gives these codes as
functions that compute, generic in the sizes: a code is data. Definitions and tests. No Mathlib; it
imports Fmt/FieldE.lean alone.

The words. What the first toy is: the head of Fmt/M1Types.lean; its rounds in order: the head of
Fmt/M1Dec.lean. F is field 2 (`Fld.two`, Fmt/Rules1.lean) and E its cubic extension (`Ext3`,
Fmt/FieldE.lean). A word is 64 bits (`UInt64`); an element of F is a word below p (`Fld.p`,
Fmt/Rules1.lean). Stages, with their main codes and mask codes: `Stage`, Fmt/M1Types.lean.

Sources.
   The description.
      Written from the programs' description of the toy (its title: "the toy of milestone (1): which
        protocol it runs, and the verifier's decision"), section 4 (codes), with the conventions at
        the heads of its parts 3 and 4, which use the same formula under the names Enc, symbol,
        generator row and short position.
      By its own word that description has one writer and no second reading.

   The programs' answers.
      Beside it stand the programs' answers to questions (their section 2
        and annex A; one writer's too; marked there as read off a run's files, or found by a small
        program that calls the programs' own routines for points and symbols).
      What they confirm is marked below, and in the comments on the tests, as "the programs' word".
      They also confirm that a mask code takes its points by the same rule, with its own a; there is
        no test for that here, since mask codes and main codes are one type in this file.
   The format page (docs/format/FORMAT.md, which comes with the programs).
      `Code.bytes` and `codesBytes` are its rules R12.1 and R12.2; they were written here from
      program lines of the page, which may differ from the page as it ships;
      their sources do not include the rules' words.
      The rule that equal triples stand once (R12.2) comes from the programs' answer.
      This file has not been held against the page as it ships,
      and may differ from it.
      The page, as read here, has a rule on a code's points and symbols in field 2
      (R12.11).
      By a reading its formulas are those of `point` and `symF`, `symE` here,
        and its known answers (the constant, three points, and all sixteen
        points and symbols of the
        code (4, 8, 3)) are the numbers in this file's tests that are marked "the programs' word"
        or, for the constant, "the text's one number" (compared by a program).
   Proof files.
      Proof files made by the programs are read and judged by the decision that uses these
        codes: those tests are gathered in Fmt/M1FullProg.lean (the verdict on each file; nineteen
        values that the decision computes on its way, compared with the programs' own list).
        (Exactly: the values of `targets`; see Limits in the head of Fmt/M1Targets.lean.)

1. What the file contains.
   `Code`: A code is a triple (a, l, r): codewords of length n = 2^a, messages of l entries, a
      random tail of r entries.
   `w32`, `rootOf2 j`: The root of unity of order 2^32 that the description names, 7^(5 (2^32 - 1));
      the one of order 2^j.
   `point a x`: The point of the position x: 7 times the product, over the set bits i < a of x, of
      `rootOf2 (i + 1)`. Bit 0 is the sign: the positions 2 m and 2 m + 1 have the points z and -z.
   `symF`, `symE C x m rho`: The symbol at x of the codeword of the message m with the tail rho: the
      sum over j < r of rho_j z^j plus the sum over j < l of m_j z^(r + j), with z = `point a x`.
      Over E the formula is the same (z lies in F), coordinate by coordinate. This is the encoding
      that the decision's checks at the positions evaluate on what the prover has shown in the
      clear.
   `genT`, `genM C x`: The generator's row at x: z^j for j < r (on the tail), z^(r + j) for j < l
      (on the message).
   `encE`, `genTE`, `genME`: No other file of Fmt/ or Run/ calls them.
   `cp Z x`: The position of a mask code Z that goes with the position x of a main code: x modulo
      Z's length.
   `wordF`, `wordE`: A whole codeword, for a prover of this library's own at tiny sizes. No
   verifier of Fmt/ or
      Run/ calls them, and no other file of these folders.
   `Code.bytes`, `codesBytes`: Two lists of codes as bytes: the number of main codes, each as three
      words (a, l, r); the number of mask codes, each likewise (FORMAT.md, R12.1 and R12.2). The
      page's known answer is a test here.
   `onceL`, `noIn`, `codesItem mains masks`: The value of the parameter item "codes" of a run, from
      the stages' main codes and mask codes in the order of the stages. A code enters its list when
      the first stage that uses it is entered, and a triple that is in the list already is not
      entered again (FORMAT.md, R12.2). `noIn l c` is the number under which a stage names its code:
      its place in that list.
   `Full`: The six triples of the toy at the full parameters. They are the programs' word, by
      their answer ("yes to all six": read off a run's files).

   `ProgTiny`: The six triples at the programs' tiny parameters (rows of 2^4 entries; 3, 3, 5
      positions).
   This library's own choices where the description is silent, which make the functions total. Of a
      position only the bits below a are read, so x counts modulo n. A message or a tail that is too
      short counts as filled with 0; one that is too long is cut. A word that is not below p counts
      modulo p (Fmt/FieldE.lean). For j above 32, `rootOf2 j` is `w32`.
   How the six triples of `Full` were inferred from the description, not from the programs' answer.
      The description gives: lengths 2^15, 2^14, 2^14 for main and mask codes alike; l = 2^12 and 32
        at the first stage; 3,220 elements in the clear at the last, which it reads as
        2,048 + 1,024 + 74 + 74.
      The inferences were: each tail as long as the number of draws at which its stage's tree is
      opened
        (73, 74, 74); the second stage's message lengths from the two conditions on sizes in part 4
        (2^k' l' = l; what is carried over fits the next mask table), the mask's as the least power
        of two that fits.
      The tests of these conditions are in the namespace `Full`.

2. What is checked when the file compiles (#guard).
   `w32` is the power that the description names, and has order exactly 2^32.
   The programs' word (their annex A): three points (at 12345 and 2 of length 2^15, at 9999 of
      length 2^14); all sixteen positions of the code (4, 8, 3), point and symbol, at the message
      m_j = 1000003 j + 17 and the tail rho_j = p - 1 - 5 j; the values of the item "codes" in the
      parameters' bytes at the full and at the tiny parameters (136 and 160 bytes).
      These two values are of one state of the programs, in front of a change of theirs. By their
      word no change in progress at that state touches these
      bytes.
   Beside them: points, roots and symbols at chosen places. These are answers of a short
      Python program of this library's own, by other formulas (the point as 7 times the root of
      order 2^a to
      the power "the a bits of x in reverse order"; the symbol as the plain sum with built-in
      powers), whose sources include no answer of the programs.
   In Lean itself: the same other formula at all positions of four lengths; z and -z, at length 2^7;
      the points of a code are different, and their n-th powers are one value (a coset), at length
      2^6; the symbol is the generator's row times (tail, message), at two codes with one message
      each; encoding is linear, tried at one doubling; short and long inputs; the forms on arrays.
   The page's known answer for the item "codes" of two main codes and one mask code (not held
      against the page as it ships).

3. Theorems. None.

Notation: field 1: `Fld.one`, the other of the format's two fields (`Fld`, Fmt/Rules1.lean).

4. What is not claimed.
   It is not claimed that the programs' answers are right of the programs. They have one writer
      and, by their own word, no second reading.
   Nothing is claimed on the codes' distance or rate.
   Which code belongs to which stage and row is not in this file (the parameters' record: another
      file), but for the stages' codes at two sets of parameters: the lists `mains`, `masks` in
      `Full` and in `ProgTiny`.
   Field 1 is not covered: the description's codes are for field 2.
   No statement on soundness follows from this file.

Terms: lean/GLOSSARY.md.
-/
import Fmt.FieldE

namespace Fmt
namespace M1

/-- A code: codewords of length 2^a, messages of l entries, a random tail of r entries. -/
structure Code where
  a : Nat
  l : Nat
  r : Nat
  deriving DecidableEq, Repr, Inhabited

/-- the length of a codeword -/
def Code.n (C : Code) : Nat := 2 ^ C.a

/-- the root of unity of order 2^32 -/
def w32 : UInt64 := 0xE2AF70635744FD26

/-- x squared k times -/
def sqN (x : UInt64) : Nat → UInt64
  | 0 => x
  | k + 1 => sqN (Fld.two.mul x x) k

/-- the root of unity of order 2^j, for j up to 32; for j above 32 it is `w32` -/
def rootOf2 (j : Nat) : UInt64 := sqN w32 (32 - j)

/-- Arguments x, n, i, acc. The result is acc times `rootOf2 (j + 1)` for every set bit j of x among
the n bits i, i + 1, .. -/
def pointFrom (x : Nat) : Nat → Nat → UInt64 → UInt64
  | 0, _, acc => acc
  | n + 1, i, acc =>
    pointFrom x n (i + 1) (if x.testBit i then Fld.two.mul acc (rootOf2 (i + 1)) else acc)

/-- The point of the position x in a code of length 2^a. -/
def point (a x : Nat) : UInt64 := pointFrom x a 0 7

/-- a list cut, or filled with z, to n members -/
def fitL {α : Type} (z : α) (n : Nat) (l : List α) : List α :=
  l.take n ++ List.replicate (n - l.length) z

/-- c_0 + c_1 z + c_2 z^2 + .. over F -/
def hornerF (z : UInt64) (cs : List UInt64) : UInt64 :=
  cs.foldr (fun c acc => Fld.two.add c (Fld.two.mul z acc)) 0

/-- the same with coefficients in E -/
def hornerE (z : UInt64) (cs : List Ext3) : Ext3 :=
  cs.foldr (fun c acc => Fld.two.addE c (Fld.two.scaleE z acc)) Fld.zeroE

/-- The symbol at x, over F. -/
def symF (C : Code) (x : Nat) (m rho : List UInt64) : UInt64 :=
  hornerF (point C.a x) (fitL 0 C.r rho ++ fitL 0 C.l m)

/-- The symbol at x, over E. -/
def symE (C : Code) (x : Nat) (m rho : List Ext3) : Ext3 :=
  hornerE (point C.a x) (fitL Fld.zeroE C.r rho ++ fitL Fld.zeroE C.l m)

/-- s, s z, s z^2, ..: n members -/
def powers (z : UInt64) : Nat → UInt64 → List UInt64
  | 0, _ => []
  | n + 1, s => s :: powers z n (Fld.two.mul s z)

/-- the generator's row at x, on the tail -/
def genT (C : Code) (x : Nat) : List UInt64 := powers (point C.a x) C.r 1

/-- the generator's row at x, on the message -/
def genM (C : Code) (x : Nat) : List UInt64 :=
  powers (point C.a x) C.l (Fld.two.pow (point C.a x) C.r)

/-- the sum of the products, as far as both lists reach -/
def dotF : List UInt64 → List UInt64 → UInt64
  | c :: cs, v :: vs => Fld.two.add (Fld.two.mul c v) (dotF cs vs)
  | _, _ => 0

/-- the same: coefficients in F, entries in E -/
def dotFE : List UInt64 → List Ext3 → Ext3
  | c :: cs, v :: vs => Fld.two.addE (Fld.two.scaleE c v) (dotFE cs vs)
  | _, _ => Fld.zeroE

/-- The position of the mask code Z that goes with x. -/
def cp (Z : Code) (x : Nat) : Nat := x % Z.n

/-- a whole codeword -/
def wordF (C : Code) (m rho : List UInt64) : List UInt64 :=
  (List.range C.n).map fun x => symF C x m rho
def wordE (C : Code) (m rho : List Ext3) : List Ext3 := (List.range C.n).map fun x => symE C x m rho

/-- the symbol over E on arrays, in the order (message, tail, position) -/
def encE (C : Code) (m rho : Array Ext3) (x : Nat) : Ext3 := symE C x m.toList rho.toList

/-- the generator's row at x as vectors over E -/
def genTE (C : Code) (x : Nat) : Array Ext3 := ((genT C x).map Fld.ofF).toArray
def genME (C : Code) (x : Nat) : Array Ext3 := ((genM C x).map Fld.ofF).toArray

/-- a code as three words -/
def Code.bytes (C : Code) : ByteArray := u64n C.a ++ u64n C.l ++ u64n C.r

/-- two lists of codes as bytes -/
def codesBytes (main mask : List Code) : ByteArray :=
  u64n main.length ++ cat (main.map Code.bytes) ++ u64n mask.length ++ cat (mask.map Code.bytes)

/-- a list of codes, each at its first place alone -/
def onceL : List Code → List Code
  | [] => []
  | c :: l => c :: (onceL l).filter (· != c)

/-- the place of a code in a list; the list's length if it is not there -/
def noIn (l : List Code) (c : Code) : Nat := l.idxOf c

/-- The value of the item "codes", from the stages' main codes and mask codes in the order of the
stages. -/
def codesItem (mains masks : List Code) : ByteArray := codesBytes (onceL mains) (onceL masks)

/-! ## Tests -/

/-- the a low bits of x in reverse order -/
def revBits (a x : Nat) : Nat :=
  (List.range a).foldl (fun acc i => 2 * acc + (if x.testBit i then 1 else 0)) 0

-- the text's one number: w32 is 7 to the power 5 (2^32 - 1); its order is exactly 2^32
#guard Fld.two.pow 7 (5 * (2 ^ 32 - 1)) = w32
#guard sqN w32 31 = 18446744069414584320 && sqN w32 32 = 1
#guard rootOf2 32 = w32 && rootOf2 1 = 18446744069414584320 && rootOf2 0 = 1
-- roots and points: the Python program's answers
#guard [1, 2, 3, 14, 15, 32].map rootOf2 = [18446744069414584320, 281474976710656, 16777216, 10930245224889659871, 3333600369887534767, 16334397945464290598]
#guard [0, 1, 2, 3, 12345, 32767].map (point 15) = [7, 18446744069414584314, 1970324836974592, 18444773744577609729, 4649013750641269600, 1496847738072033982]
#guard point 14 1 = 18446744069414584314 && point 14 9999 = 9335015899764920215 && point 3 5 = 18446744069297143809
-- the other formula, at all positions of four lengths
#guard [0, 1, 4, 7].all fun a => (List.range (2 ^ a)).all fun x => point a x = Fld.two.mul 7 (Fld.two.pow (rootOf2 a) (revBits a x))
-- bit 0 is the sign
#guard (List.range 64).all fun m => point 7 (2 * m + 1) = Fld.two.neg (point 7 (2 * m))
-- a position with one set bit
#guard (List.range 15).all fun i => point 15 (2 ^ i) = Fld.two.mul 7 (rootOf2 (i + 1))
-- the points of a code are different; their n-th powers are one value: a coset of the roots of
-- unity of order n
#guard ((List.range 64).map (point 6)).eraseDups.length = 64
#guard (List.range 64).all fun x => Fld.two.pow (point 6 x) 64 = Fld.two.pow 7 64
-- of a position the bits below a are read
#guard point 4 (16 + 5) = point 4 5 && point 0 9 = 7

/-- a message and a tail over F, for the tests -/
def gM : List UInt64 := (List.range 8).map fun j => UInt64.ofNat (1000003 * j + 17)
def gR : List UInt64 := (List.range 3).map fun j => UInt64.ofNat (18446744069414584320 - 5 * j)
/-- the same over E -/
def gME : List Ext3 :=
  (List.range 4).map fun j =>
    (UInt64.ofNat (j * j + 1), UInt64.ofNat (j * j + 4), UInt64.ofNat (j * j + 7))
def gRE : List Ext3 :=
  (List.range 2).map fun j =>
    (UInt64.ofNat (18446744069414584319 - j),
      UInt64.ofNat (18446744069414584312 - j),
      UInt64.ofNat (18446744069414584305 - j))

-- the programs' word: three points
#guard point 15 12345 = 4649013750641269600 && point 15 2 = 1970324836974592 && point 14 9999 = 9335015899764920215
-- the programs' word: all sixteen positions of the code (4, 8, 3): the points; the symbols at the
-- message gM and the tail gR
#guard (List.range 16).map (point 4) = [7, 18446744069414584314, 1970324836974592, 18444773744577609729, 117440512, 18446744069297143809, 7696581392640, 18446736372833191681,
  28672, 18446744069414555649, 8070450532247928832, 10376293537166655489, 481036337152, 18446743588378247169, 31525197384253440, 18415218872030330881]
#guard wordF ⟨4, 8, 3⟩ gM gR = [2251967882290790, 1761066152988106, 7062088817545533301, 11380757524195858728, 2725397505791400752, 9956560198768277230, 13552087439267912244, 10659558282155280860,
  6537321372891063553, 18188557764674685878, 2233206876800962260, 16226444926008292991, 17139878364151154727, 12909924323945411286, 15510620354141475440, 3487535770944086406]
-- symbols: the Python program's answers (plain sums)
#guard [0, 1, 6, 15].map (fun x => symF ⟨4, 8, 3⟩ x gM gR) = [2251967882290790, 1761066152988106, 13552087439267912244, 3487535770944086406]
#guard [0, 5, 7].map (fun x => symE ⟨3, 4, 2⟩ x gME gRE) =
  [(180787, 239531, 298275), (13040828981346073, 53287099839178735, 93533370697011397), (171025723613459993, 185141236614165487, 199256749614870981)]
-- over E the symbol is the symbol of each coordinate
#guard (List.range 8).all fun x => symE ⟨3, 4, 2⟩ x gME gRE =
  (symF ⟨3, 4, 2⟩ x (gME.map (·.1)) (gRE.map (·.1)), symF ⟨3, 4, 2⟩ x (gME.map (·.2.1)) (gRE.map (·.2.1)), symF ⟨3, 4, 2⟩ x (gME.map (·.2.2)) (gRE.map (·.2.2)))
-- the symbol is the generator's row times (tail, message)
#guard (List.range 16).all fun x => symF ⟨4, 8, 3⟩ x gM gR = Fld.two.add (dotF (genT ⟨4, 8, 3⟩ x) gR) (dotF (genM ⟨4, 8, 3⟩ x) gM)
#guard (List.range 8).all fun x => symE ⟨3, 4, 2⟩ x gME gRE = Fld.two.addE (dotFE (genT ⟨3, 4, 2⟩ x) gRE) (dotFE (genM ⟨3, 4, 2⟩ x) gME)
#guard (genT ⟨4, 8, 3⟩ 5).length = 3 && (genM ⟨4, 8, 3⟩ 5).length = 8 && (genT ⟨4, 8, 3⟩ 5).head? = some 1
-- encoding is linear, tried at one doubling: message and tail added to themselves
#guard (List.range 16).all fun x => symF ⟨4, 8, 3⟩ x (gM.map fun v => Fld.two.add v v) (gR.map fun v => Fld.two.add v v) = Fld.two.add (symF ⟨4, 8, 3⟩ x gM gR) (symF ⟨4, 8, 3⟩ x gM gR)
-- too short: filled with 0; too long: cut
#guard symF ⟨4, 8, 3⟩ 6 (gM.take 5) gR = symF ⟨4, 8, 3⟩ 6 (gM.take 5 ++ [0, 0, 0]) gR && symF ⟨4, 8, 3⟩ 6 (gM ++ [9]) (gR ++ [9]) = symF ⟨4, 8, 3⟩ 6 gM gR
#guard symF ⟨4, 8, 3⟩ 6 gM (gR.take 1) = symF ⟨4, 8, 3⟩ 6 gM (gR.take 1 ++ [0, 0])
-- on arrays
#guard (List.range 8).all fun x => encE ⟨3, 4, 2⟩ gME.toArray gRE.toArray x = symE ⟨3, 4, 2⟩ x gME gRE
#guard (genME ⟨3, 4, 2⟩ 5).toList = (genM ⟨3, 4, 2⟩ 5).map (fun z => (z, 0, 0)) && (genTE ⟨3, 4, 2⟩ 5).size = 2
-- a whole codeword; the short position
#guard (wordF ⟨4, 8, 3⟩ gM gR).length = 16 && (wordE ⟨3, 4, 2⟩ gME gRE).length = 8
#guard cp ⟨3, 4, 2⟩ 13 = 5 && cp ⟨4, 8, 3⟩ 13 = 13
-- the page's known answer (in two editions that are not the one that
-- ships, the first types): the item "codes" of two main codes and one mask
-- code
#guard hex (codesBytes [⟨10, 512, 40⟩, ⟨6, 16, 40⟩] [⟨10, 64, 40⟩]) = "02000000000000000a000000000000000002000000000000280000000000000006000000000000001000000000000000280000000000000001000000000000000a0000000000000040000000000000002800000000000000"

-- each at its first place alone
#guard onceL [⟨1, 1, 1⟩, ⟨2, 2, 2⟩, ⟨1, 1, 1⟩, ⟨3, 3, 3⟩, ⟨2, 2, 2⟩] = [⟨1, 1, 1⟩, ⟨2, 2, 2⟩, ⟨3, 3, 3⟩] && onceL [] = []

/-! ## The six triples of the toy: the programs' word -/

namespace Full

def main1 : Code := ⟨15, 4096, 73⟩
def mask1 : Code := ⟨15, 32, 73⟩
def main2 : Code := ⟨14, 2048, 74⟩
def mask2 : Code := ⟨14, 256, 74⟩
def main3 : Code := ⟨14, 2048, 74⟩
def mask3 : Code := ⟨14, 1024, 74⟩

-- what the text gives: the number of elements in the clear at the last stage
#guard main3.l + mask3.l + main3.r + mask3.r = 3220
-- part 4's two conditions on sizes, from stage 1 (k' = 1, h' = 1) and from stage 2 (k' = 0, h' =
-- 0); the + 1 is for one answer to a sample
#guard 2 ^ 1 * main2.l = main1.l && 2 ^ 0 * main3.l = main2.l
#guard 2 * mask1.l + main1.r + 2 * mask1.r + 1 ≤ 2 ^ 1 * mask2.l && 2 * mask2.l + main2.r + 2 * mask2.r + 1 ≤ 2 ^ 0 * mask3.l
-- and the mask's message lengths are the least powers of two that fit
#guard ¬ (2 * mask1.l + main1.r + 2 * mask1.r + 1 ≤ 2 ^ 1 * (mask2.l / 2)) && ¬ (2 * mask2.l + main2.r + 2 * mask2.r + 1 ≤ 2 ^ 0 * (mask3.l / 2))

/-- the stages' codes, in the order of the stages -/
def mains : List Code := [main1, main2, main3]
def masks : List Code := [mask1, mask2, mask3]

-- the programs' word: in the item "codes" equal triples stand once: two main codes, three mask
-- codes; stage 3 names the main code number 1, like stage 2
#guard onceL mains = [main1, main2] && onceL masks = masks
#guard mains.map (noIn (onceL mains)) = [0, 1, 1] && masks.map (noIn (onceL masks)) = [0, 1, 2]
-- the programs' bytes: the item's value in the parameters' bytes at the full parameters: 136 bytes
#guard hex (codesItem mains masks) = "02000000000000000f00000000000000001000000000000049000000000000000e0000000000000000080000000000004a0000000000000003000000000000000f00000000000000200000000000000049000000000000000e0000000000000000010000000000004a000000000000000e0000000000000000040000000000004a00000000000000"

end Full

/-! ## The six triples at the programs' own tiny parameters -/

namespace ProgTiny

def mains : List Code := [⟨7, 16, 3⟩, ⟨8, 8, 3⟩, ⟨9, 8, 5⟩]
def masks : List Code := [⟨7, 16, 3⟩, ⟨8, 32, 3⟩, ⟨9, 128, 5⟩]

-- the programs' bytes: the item's value in the parameters' bytes at the tiny parameters: 160 bytes:
-- all six differ within their lists
#guard hex (codesItem mains masks) = "03000000000000000700000000000000100000000000000003000000000000000800000000000000080000000000000003000000000000000900000000000000080000000000000005000000000000000300000000000000070000000000000010000000000000000300000000000000080000000000000020000000000000000300000000000000090000000000000080000000000000000500000000000000"

end ProgTiny

end M1
end Fmt
