-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules6.lean: drawing: how a verifier's message is made from the answer to a round's query, as
total functions of a row of words.

In standard terms: how a round's Fiat-Shamir challenges (field elements, positions, entries of a
matrix over {-1, 0, 1}, a digest) are derived from the 64-bit words of those blocks of the answer to
the round's hash query that are the verifier's message, with a bounded number of tries in place of
open-ended rejection sampling. These are rules on bytes; no protocol is given. The programs are the
C++ implementation that comes with this Lean code.

Sources. Section 6 of the format page (docs/format/FORMAT.md), rules R6.1 to R6.11;
this file has not been held against the page as it ships,
and may differ from it.

The tests hold every known answer that the page prints under this section: ten tries, ten elements
with the words used, six counts. The file imports Fmt/Rules1.lean alone.

1. What the file contains. Definitions that can be evaluated.
   The row (`Row`, `rowOfBlocks`). Each draw takes the next words; no word is used twice and none is
     skipped (a position and the last word of matrix entries leave bits of a word unread; so does a
     try in field 1, which reads the low 61 bits of the word); what is left at the end is dropped
     (R6.1).
   A draw (`Dr α`) takes the row and a place in it (the cursor). Every draw here is built from three
     primitives: `Dr.pure`, `Dr.bind`, `Dr.word`. No other draw touches the row or the cursor.
   The try. `Fld.tryWord` of Fmt/Rules1.lean. No word is reduced modulo p.
   `drawF`, `drawE`, `drawNZ`, `drawTrits`, `drawSeal`, `drawSeed`, `mostWords`, `blocksFor`.
   `drawPoss k n`: n positions (`drawPos k`), one after the other (a position can come twice). Two
     things are handed on: the draws (the value of `drawPoss`: the positions in the order drawn,
     repeats kept) and the list (`listOf` of it: the set of the drawn positions, increasing). An
     opening goes by the list: a position that is drawn twice is opened once. Every row that stands
     for a read goes by the draws: a position that is drawn twice gives its rows twice, so the
     number of rows does not depend on the draw.
   `Draw`, `d.most`, `d.read f`; `readAll f ds`, `mostAll ds`. One draw of a round as data; the most
     words that it uses (18, 36, 1, n / 32 rounded up, 4); a round's draws in a given order.

2. What is checked when the file compiles. 57 tests (#guard), the page's known answers named under
Sources among them. A test is an evaluation made while the file compiles; it leaves no declaration.

3. Theorems.
   `draw_most`. Every draw, from every place of every row, ends at most d.most words further on, and
     never before its start.
   `draw_reads`. Its value and its end read no word of the row but the d.most words from its start.
   `all_most`, `all_reads`. The same for a list of draws, with the sum. So a verifier's message is a
     total function of a fixed number of blocks.
   `try_one`, `try_two`. A count of the words at which a try succeeds or fails can rest on these.

4. What is not claimed. The laws of these draws on a uniform row (how far from uniform they are).
The order of a round's draws (R6.2): `readAll` takes the order as data; how kind and entry give that
list is in Fmt/Rules6Round.lean and Fmt/Rules6Draws.lean. The prover's private coins are no part of
the format.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules1

namespace Fmt

/-- the row of words from which a verifier's message is drawn -/
abbrev Row : Type := Nat → UInt64

/-- a row given as a list; 0 beyond its end -/
def rowOfList (l : List UInt64) : Row := fun t => l.getD t 0

/-- The row of a message's blocks: word t is word t mod 4 of block t div 4; 0 beyond the last block.
-/
def rowOfBlocks (bs : Array ByteArray) : Row := fun t =>
  digestWord (bs.getD (t / 4) ByteArray.empty) (t % 4)

/-- A draw: the row, a place in it; a value, and the place behind the words used. -/
abbrev Dr (α : Type) : Type := Row → Nat → α × Nat

/-- a value; no word is used -/
def Dr.pure {α : Type} (a : α) : Dr α := fun _ c => (a, c)

/-- one draw, then another on what follows -/
def Dr.bind {α β : Type} (x : Dr α) (k : α → Dr β) : Dr β := fun r c => k (x r c).1 r (x r c).2

/-- the next word -/
def Dr.word : Dr UInt64 := fun r c => (r c, c + 1)

/-- a draw, n times -/
def Dr.times {α : Type} (x : Dr α) : Nat → Dr (List α)
  | 0 => Dr.pure []
  | n + 1 => x.bind fun a => (Dr.times x n).bind fun l => Dr.pure (a :: l)

/-- an element of the extension field, as its three coordinates -/
abbrev Ext : Type := UInt64 × UInt64 × UInt64

/-- an element of the base field, with at most n tries -/
def drawFN (f : Fld) : Nat → Dr UInt64
  | 0 => Dr.pure 0
  | n + 1 => Dr.word.bind fun w => match f.tryWord w with
    | some x => Dr.pure x
    | none => drawFN f n

/-- An element of the base field: at most six tries, then 0. -/
def drawF (f : Fld) : Dr UInt64 := drawFN f 6

/-- An element of the extension field. -/
def drawE (f : Fld) : Dr Ext :=
  (drawF f).bind fun a => (drawF f).bind fun b => (drawF f).bind fun c => Dr.pure (a, b, c)

/-- An element of the extension field that is not 0: at most two, then 1. -/
def drawNZ (f : Fld) : Dr Ext :=
  (drawE f).bind fun e =>
    if e = (0, 0, 0) then
      (drawE f).bind fun e' => Dr.pure (if e' = (0, 0, 0) then (1, 0, 0) else e') else Dr.pure e

/-- A position below 2^k: the low k bits of the next word. -/
def drawPos (k : Nat) : Dr Nat := Dr.word.bind fun w => Dr.pure (w.toNat % 2 ^ k)

/-- the positions of a round, as they are drawn -/
def drawPoss (k n : Nat) : Dr (List Nat) := (drawPos k).times n

/-- put a number into an increasing list without repeats -/
def insertIntoIncreasingList (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => if x < y then x :: y :: l else if x = y then y :: l else y :: insertIntoIncreasingList x l

/-- The list of the drawn positions: their set, increasing. (Openings go by it; rows go by the draws
themselves.) -/
def listOf (l : List Nat) : List Nat := l.foldr insertIntoIncreasingList []

/-- the next n words -/
def drawWords (n : Nat) : Dr (List UInt64) := Dr.word.times n

/-- entry j of a word -/
def tritAt (w : UInt64) (j : Nat) : Int :=
  if w.toNat.testBit (2 * j) then (if w.toNat.testBit (2 * j + 1) then -1 else 1) else 0

/-- n entries from a list of words, 32 a word -/
def tritsOf : List UInt64 → Nat → List Int
  | [], _ => []
  | w :: ws, n => (List.range (min n 32)).map (tritAt w) ++ tritsOf ws (n - 32)

/-- n entries of a matrix over {-1, 0, 1}. -/
def drawTrits (n : Nat) : Dr (List Int) :=
  (drawWords ((n + 31) / 32)).bind fun ws => Dr.pure (tritsOf ws n)

/-- A seal: the next four words as a digest. -/
def drawSeal : Dr ByteArray := (drawWords 4).bind fun ws => Dr.pure (cat (ws.map u64))

/-- The seed of an out-of-domain sample with a point of v coordinates. -/
def drawSeed (f : Fld) (v : Nat) : Dr (List Ext × Ext) :=
  ((drawE f).times v).bind fun pt => (drawNZ f).bind fun s => Dr.pure (pt, s)

/-- One draw of a round, as data. -/
inductive Draw where
  | elem
  | elemNZ
  | pos (k : Nat)
  | trits (n : Nat)
  | sealed
  deriving DecidableEq, Repr

/-- the most words that a draw uses -/
def Draw.most : Draw → Nat
  | .elem => 18
  | .elemNZ => 36
  | .pos _ => 1
  | .trits n => (n + 31) / 32
  | .sealed => 4

/-- what a draw gives -/
inductive Val where
  | ext (e : Ext)
  | pos (x : Nat)
  | trits (l : List Int)
  | sealed (d : ByteArray)
  deriving DecidableEq

def Draw.read (f : Fld) : Draw → Dr Val
  | .elem => (drawE f).bind fun e => Dr.pure (.ext e)
  | .elemNZ => (drawNZ f).bind fun e => Dr.pure (.ext e)
  | .pos k => (drawPos k).bind fun x => Dr.pure (.pos x)
  | .trits n => (drawTrits n).bind fun l => Dr.pure (.trits l)
  | .sealed => drawSeal.bind fun d => Dr.pure (.sealed d)

/-- A round's draws, in a given order. -/
def readAll (f : Fld) : List Draw → Dr (List Val)
  | [] => Dr.pure []
  | d :: ds => (d.read f).bind fun v => (readAll f ds).bind fun l => Dr.pure (v :: l)

/-- the most words of a list of draws -/
def mostAll : List Draw → Nat
  | [] => 0
  | d :: ds => d.most + mostAll ds

/-- The most words of a round, in the page's letters: drawE counts all elements of the extension
field, drawNZ those among them that must not be 0; a portion is a number of matrix entries. -/
def mostWords (drawE drawNZ positions : Nat) (portions : List Nat) (isSeal : Bool) : Nat :=
  18 * (drawE - drawNZ) + 36 * drawNZ + positions +
    (portions.map fun n => (n + 31) / 32).sum + (if isSeal then 4 else 0)

/-- the blocks of 32 bytes that hold K words -/
def blocksFor (K : Nat) : Nat := (K + 3) / 4

/-! ## The page's known answers -/

/-- a word at which the try fails, in both fields -/
def failW : UInt64 := 18446744073709551615

/-- m words that fail, then the word 5 -/
def failRow (m : Nat) : Row := rowOfList (List.replicate m failW ++ [5])

-- a word and its try (the ten lines stand as tests in Fmt/Rules1.lean too)
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

-- an element of the base field from a given row of words: the element; words used
#guard drawF .two (failRow 0) 0 = (5, 1)
#guard drawF .two (failRow 1) 0 = (5, 2)
#guard drawF .two (failRow 5) 0 = (5, 6)
#guard drawF .two (failRow 6) 0 = (0, 6)
#guard drawF .two (failRow 7) 0 = (0, 6)
#guard drawF .one (failRow 0) 0 = (5, 1)
#guard drawF .one (failRow 1) 0 = (5, 2)
#guard drawF .one (failRow 5) 0 = (5, 6)
#guard drawF .one (failRow 6) 0 = (0, 6)
#guard drawF .one (failRow 7) 0 = (0, 6)

-- the most words of a verifier's message: one element; one that is not 0; a seed with two
-- coordinates; five positions and an element; forty entries; a seal
#guard mostWords 1 0 0 [] false = 18
#guard mostWords 1 1 0 [] false = 36
#guard mostWords 3 1 0 [] false = 72
#guard mostWords 1 0 5 [] false = 23
#guard mostWords 0 0 0 [40] false = 2
#guard mostWords 0 0 0 [] true = 4
-- the same six by the draws as data
#guard mostAll [.elem] = 18
#guard mostAll [.elemNZ] = 36
#guard mostAll [.elem, .elem, .elemNZ] = 72
#guard mostAll [.pos 10, .pos 10, .pos 10, .pos 10, .pos 10, .elem] = 23
#guard mostAll [.trits 40] = 2
#guard mostAll [.sealed] = 4

/-! ## Tests of this library's own (no known answer of the page; each follows from a rule's text) -/

-- "not 0": two elements that are 0 give 1, and six words are used (the word 0 is no failing try)
#guard drawNZ .two (rowOfList [0, 0, 0, 0, 0, 0, 9]) 0 = ((1, 0, 0), 6)
#guard drawNZ .two (rowOfList [0, 0, 0, 0, 7, 0, 9]) 0 = ((0, 7, 0), 6)
#guard drawNZ .two (rowOfList [4, 0, 0, 0, 7, 0, 9]) 0 = ((4, 0, 0), 3)
-- all words fail: 1, and 36 words are used up;  an element: 0, and 18
#guard drawNZ .one (fun _ => failW) 0 = ((1, 0, 0), 36)
#guard drawNZ .two (fun _ => failW) 0 = ((1, 0, 0), 36)
#guard drawE .one (fun _ => failW) 0 = ((0, 0, 0), 18)
-- a failing try shifts the later draws
#guard drawE .two (rowOfList [failW, 1, 2, failW, failW, 3, 4]) 0 = ((1, 2, 3), 6)
-- a draw from a later place
#guard drawF .two (rowOfList [9, 9, failW, 8]) 2 = (8, 4)
-- positions: the low k bits; repeats; the list that is handed on
#guard drawPoss 4 5 (rowOfList [0x13, 0x25, 0xf3, 0x01, 0x25, 77]) 0 = ([3, 5, 3, 1, 5], 5)
#guard listOf [3, 5, 3, 1, 5] = [1, 3, 5]
#guard listOf [] = []
#guard drawPos 0 (rowOfList [12345]) 0 = (0, 1)
#guard drawPos 63 (rowOfList [18446744073709551615]) 0 = (9223372036854775807, 1)
-- matrix entries: from the lowest bit, the pairs (0, 0) and (0, 1) give 0, (1, 0) gives 1, (1, 1)
-- gives -1
#guard drawTrits 4 (rowOfList [0b10110100]) 0 = ([0, 1, -1, 0], 1)
#guard ((drawTrits 40 (rowOfList [0, 0b0111, 9]) 0).1.drop 32, (drawTrits 40 (rowOfList [0, 0b0111, 9]) 0).2) = ([-1, 1, 0, 0, 0, 0, 0, 0], 2)
#guard (drawTrits 40 (rowOfList [0, 0b0111, 9]) 0).1.length = 40
#guard (drawTrits 32 (rowOfList [1, 2]) 0).2 = 1
#guard (drawTrits 33 (rowOfList [1, 2]) 0).2 = 2
#guard drawTrits 0 (rowOfList [1, 2]) 0 = ([], 0)
-- a seal: four words, lowest byte first
#guard hex (drawSeal (rowOfList [0x0807060504030201, 0, 0, 0xff00000000000000, 5]) 0).1 = "01020304050607080000000000000000000000000000000000000000000000ff"
#guard (drawSeal (rowOfList [1, 2, 3, 4, 5]) 0).2 = 4
-- a block's words: the row of blocks undoes the spelling
#guard (List.range 9).map (rowOfBlocks #[(drawSeal (rowOfList [11, 22, 33, 44]) 0).1, (drawSeal (rowOfList [55, 66, 77, 88]) 0).1]) = [11, 22, 33, 44, 55, 66, 77, 88, 0]
#guard (blocksFor 18, blocksFor 36, blocksFor 72, blocksFor 23, blocksFor 2, blocksFor 4, blocksFor 0) = (5, 9, 18, 6, 1, 1, 0)
-- a seed with a point of two coordinates
#guard drawSeed .two 2 (rowOfList [1, 2, 3, 4, 5, 6, 0, 0, 0, 7, 8, 9]) 0 = (([(1, 2, 3), (4, 5, 6)], (7, 8, 9)), 12)
-- a round's draws as data: two positions, then an element
#guard readAll .two [.pos 4, .pos 4, .elem] (rowOfList [0x13, 0x25, 6, failW, 7, 8]) 0 = ([.pos 3, .pos 5, .ext (6, 7, 8)], 6)


/-! ## A total function of a fixed number of words -/

/-- a draw ends at most K words after its start, never before it, and reads no word of the row but
these K -/
structure Dr.Within {α : Type} (x : Dr α) (K : Nat) : Prop where
  lo : ∀ r c, c ≤ (x r c).2
  hi : ∀ r c, (x r c).2 ≤ c + K
  reads : ∀ (r r' : Row) c, (∀ t, c ≤ t → t < c + K → r t = r' t) → x r c = x r' c

theorem Dr.within_pure {α : Type} (a : α) : (Dr.pure a).Within 0 :=
  ⟨fun _ _ => Nat.le_refl _, fun _ _ => Nat.le_refl _, fun _ _ _ _ => rfl⟩

theorem Dr.within_word : Dr.word.Within 1 :=
  ⟨fun _ c => Nat.le_succ c, fun _ _ => Nat.le_refl _, fun r r' c h => by
    show (r c, c + 1) = (r' c, c + 1)
    rw [h c (Nat.le_refl c) (Nat.lt_succ_self c)]⟩

theorem Dr.within_mono {α : Type} {x : Dr α} {K L : Nat} (h : x.Within K) (hKL : K ≤ L) :
    x.Within L :=
  ⟨h.lo, fun r c => Nat.le_trans (h.hi r c) (Nat.add_le_add_left hKL c),
    fun r r' c hr =>
      h.reads r r' c fun t h1 h2 => hr t h1 (Nat.lt_of_lt_of_le h2 (Nat.add_le_add_left hKL c))⟩

theorem Dr.within_bind {α β : Type} {x : Dr α} {k : α → Dr β} {K L : Nat}
    (hx : x.Within K) (hk : ∀ a, (k a).Within L) : (x.bind k).Within (K + L) := by
  refine ⟨fun r c => ?_, fun r c => ?_, fun r r' c hr => ?_⟩
  · exact Nat.le_trans (hx.lo r c) ((hk _).lo r _)
  · have h1 := hx.hi r c
    have h2 := (hk (x r c).1).hi r (x r c).2
    show (k (x r c).1 r (x r c).2).2 ≤ c + (K + L)
    omega
  · have e : x r c = x r' c := hx.reads r r' c fun t h1 h2 => hr t h1 (by omega)
    show k (x r c).1 r (x r c).2 = k (x r' c).1 r' (x r' c).2
    rw [← e]
    have h1 := hx.lo r c
    have h2 := hx.hi r c
    exact (hk _).reads r r' _ fun t h3 h4 => hr t (by omega) (by omega)

theorem Dr.within_times {α : Type} {x : Dr α} {K : Nat} (hx : x.Within K) :
    ∀ n, (x.times n).Within (n * K)
  | 0 => by
    rw [Nat.zero_mul]
    exact Dr.within_pure _
  | n + 1 => by
    have h := Dr.within_bind hx fun a =>
      Dr.within_bind (Dr.within_times hx n) fun l => Dr.within_pure (a :: l)
    exact Dr.within_mono h (by rw [Nat.succ_mul]; omega)

theorem within_drawFN (f : Fld) : ∀ n, (drawFN f n).Within n
  | 0 => Dr.within_pure _
  | n + 1 => by
    have h : (drawFN f (n + 1)).Within (1 + n) := Dr.within_bind Dr.within_word fun w => by
      cases f.tryWord w with
      | some x => exact Dr.within_mono (Dr.within_pure x) (Nat.zero_le n)
      | none => exact within_drawFN f n
    exact Dr.within_mono h (by omega)

theorem within_drawF (f : Fld) : (drawF f).Within 6 := within_drawFN f 6

theorem within_drawE (f : Fld) : (drawE f).Within 18 :=
  Dr.within_bind (K := 6) (L := 12) (within_drawF f) fun a =>
    Dr.within_bind (K := 6) (L := 6) (within_drawF f) fun b =>
      Dr.within_bind (K := 6) (L := 0) (within_drawF f) fun c => Dr.within_pure (a, b, c)

theorem within_drawNZ (f : Fld) : (drawNZ f).Within 36 :=
  Dr.within_bind (K := 18) (L := 18) (within_drawE f) fun e => by
    by_cases h : e = (0, 0, 0)
    · rw [if_pos h]
      exact Dr.within_bind (K := 18) (L := 0) (within_drawE f) fun e' => Dr.within_pure _
    · rw [if_neg h]
      exact Dr.within_mono (Dr.within_pure e) (Nat.zero_le 18)

theorem within_drawPos (k : Nat) : (drawPos k).Within 1 :=
  Dr.within_bind (K := 1) (L := 0) Dr.within_word fun _ => Dr.within_pure _

theorem within_drawPoss (k n : Nat) : (drawPoss k n).Within n :=
  Dr.within_mono (Dr.within_times (within_drawPos k) n) (by omega)

theorem within_drawWords (n : Nat) : (drawWords n).Within n :=
  Dr.within_mono (Dr.within_times Dr.within_word n) (by omega)

theorem within_drawTrits (n : Nat) : (drawTrits n).Within ((n + 31) / 32) :=
  Dr.within_bind (L := 0) (within_drawWords _) fun _ => Dr.within_pure _

theorem within_drawSeal : drawSeal.Within 4 :=
  Dr.within_bind (K := 4) (L := 0) (within_drawWords 4) fun _ => Dr.within_pure _

theorem within_drawSeed (f : Fld) (v : Nat) : (drawSeed f v).Within (v * 18 + 36) :=
  Dr.within_bind (Dr.within_times (within_drawE f) v) fun _ =>
    Dr.within_bind (K := 36) (L := 0) (within_drawNZ f) fun _ => Dr.within_pure _

theorem within_read (f : Fld) : ∀ d : Draw, (d.read f).Within d.most
  | .elem => Dr.within_bind (K := 18) (L := 0) (within_drawE f) fun _ => Dr.within_pure _
  | .elemNZ => Dr.within_bind (K := 36) (L := 0) (within_drawNZ f) fun _ => Dr.within_pure _
  | .pos k => Dr.within_bind (K := 1) (L := 0) (within_drawPos k) fun _ => Dr.within_pure _
  | .trits n => Dr.within_bind (L := 0) (within_drawTrits n) fun _ => Dr.within_pure _
  | .sealed => Dr.within_bind (K := 4) (L := 0) within_drawSeal fun _ => Dr.within_pure _

theorem within_readAll (f : Fld) : ∀ ds : List Draw, (readAll f ds).Within (mostAll ds)
  | [] => Dr.within_pure _
  | d :: ds =>
    Dr.within_bind (within_read f d) fun _ =>
      Dr.within_bind (L := 0) (within_readAll f ds) fun _ => Dr.within_pure _

/-- Every draw ends at most d.most words after its start, and never before it. -/
def Spec.draw_most : Prop :=
  ∀ (f : Fld) (d : Draw) (r : Row) (c : Nat), c ≤ (d.read f r c).2 ∧ (d.read f r c).2 ≤ c + d.most

/-- Every draw reads the d.most words from its start alone. -/
def Spec.draw_reads : Prop :=
  ∀ (f : Fld) (d : Draw) (r r' : Row) (c : Nat),
    (∀ t, c ≤ t → t < c + d.most → r t = r' t) → d.read f r c = d.read f r' c

def Spec.all_most : Prop :=
  ∀ (f : Fld) (ds : List Draw) (r : Row) (c : Nat),
    c ≤ (readAll f ds r c).2 ∧ (readAll f ds r c).2 ≤ c + mostAll ds

/-- A round's message is a function of the mostAll ds words from its start. -/
def Spec.all_reads : Prop :=
  ∀ (f : Fld) (ds : List Draw) (r r' : Row) (c : Nat),
    (∀ t, c ≤ t → t < c + mostAll ds → r t = r' t) → readAll f ds r c = readAll f ds r' c

/-- The try in field 2, in numbers. -/
def Spec.try_two : Prop :=
  ∀ w : UInt64, Fld.two.tryWord w = if w.toNat < 18446744069414584321 then some w else none

/-- The try in field 1, in numbers: the word modulo 2^61; it fails at 2^61 - 1 alone. -/
def Spec.try_one : Prop :=
  ∀ w : UInt64, (Fld.one.tryWord w).map UInt64.toNat =
    if w.toNat % 2 ^ 61 = 2 ^ 61 - 1 then none else some (w.toNat % 2 ^ 61)

theorem draw_most : Spec.draw_most := fun f d r c =>
  ⟨(within_read f d).lo r c, (within_read f d).hi r c⟩
theorem draw_reads : Spec.draw_reads := fun f d => (within_read f d).reads
theorem all_most : Spec.all_most := fun f ds r c =>
  ⟨(within_readAll f ds).lo r c, (within_readAll f ds).hi r c⟩
theorem all_reads : Spec.all_reads := fun f ds => (within_readAll f ds).reads
theorem try_two : Spec.try_two := fun _ => rfl

theorem try_one : Spec.try_one := by
  intro w
  have e : (w &&& 0x1FFFFFFFFFFFFFFF).toNat = w.toNat % 2 ^ 61 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod w.toNat 61
  have hlt : w.toNat % 2 ^ 61 < 2 ^ 61 := Nat.mod_lt _ (by decide)
  show (if (w &&& 0x1FFFFFFFFFFFFFFF).toNat < Fld.one.p then some (w &&& 0x1FFFFFFFFFFFFFFF)
        else none).map UInt64.toNat = _
  rw [e]
  by_cases h : w.toNat % 2 ^ 61 = 2 ^ 61 - 1
  · rw [if_pos h, if_neg (by rw [h]; decide)]
    rfl
  · rw [if_neg h, if_pos (by show w.toNat % 2 ^ 61 < 2305843009213693951; omega)]
    show some (w &&& 0x1FFFFFFFFFFFFFFF).toNat = _
    rw [e]

end Fmt
