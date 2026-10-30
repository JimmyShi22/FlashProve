-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParsedRead.lean: a reader of a chain by the numbers: from a setting, a declared chain and the
numbers that hang on the draws to the record of what stands in the file. Definitions only.

A chain in a file has no lengths in it (Fmt/ParsedTypes.lean, 4). How many positions a round lists,
and how many columns and given digests each of its openings has, follows from the draws, and the
draws need the hash. These numbers are `ChainParsed.counts` (Fmt/Parsed.lean). The reader here is
told them. Then its bodies call no hash: it cuts the bytes by the declared chain and the numbers, in
the writers' order. It is the other side of the writer `ChainParsed.bytes`, and it is here so that
laws can say how a chain's record and a chain's bytes stand to each other once the numbers are given
(Fmt/ParsedReadLaws.lean).

Sources. The format page that ships: docs/format/FORMAT.md (6.3, R7.8; 7.2, R8.1, R8.2; 7.4, R8.7;
4.1, R4.5). Rule numbers are that page's. No Mathlib, neither directly nor through the imports.

1. What the file contains.
   Readers that are of no one type.
    `rdMap`: a reader's value, turned by a function.
    `rdGive`: the reader that reads no byte.
    `rdFit`: a reader, refused unless its value passes a test.
    `rdLow`: n bytes, the lowest first, as a word: the reader of `lowBytes` (Fmt/Rules8Own.lean).
    `rdZip`: a list of values, each by its own reader: the reader of member number i is made of
      member number i of two lists. It refuses if the two lists are not of one length.
    `zipLoop`, `rdZipL`: the same as a loop, which collects the values in an array and calls itself
      last. The readers of a round and of a chain call this one; that it is `rdZip` is proved
      (`rdZipL_eq`, Fmt/ParsedReadLaws.lean).
   The parts of a chain.
    `rdColumn`: a column of W elements and its leaf's salt (R7.8).
    `OpenParsed.read`: an opening (R7.8), told its two numbers.
    `rdNonceAt`: a round's nonce: no byte where the entry has no proof-of-work bits (R8.2).
    `RoundParsed.read`: a round (R8.7), told its numbers: the message by the declared items; the
      nonce; the listed positions; the openings in the order of `wantOpens`.
    `rdRand`: a chain's 32 random bytes: in case (a) of R4.5 alone.
    `ChainParsed.read`: a chain (R8.1), told its numbers.
    `ChainParsed.readFit`: the same, refused unless the record fits the declared chain
      (`ChainParsed.fits`).

   The same cuts in this library's readers that hash (`roundX`, Fmt/Rules8X.lean; `cutStepX`,
   Run/ParseLaxX.lean). An opening: `rdOpening` (Fmt/Rules7.lean), which takes the list of positions
   and computes the two numbers from it; `OpenParsed.read` at these two numbers is `rdOpening` with
   its value laid into the record. A nonce: `readNonce` (Fmt/Rules8.lean), which gives the number 0
   where there is none. The listed positions: `readList` (Fmt/Rules8.lean), which reads as many as
   the derived list has and compares. The three ties are stated and proved in
   Fmt/ParsedReadCut.lean. A message: both readers slice off as many bytes as the entry says
   (`Entry.msg`) and ask that `readItems` uses them up; `RoundParsed.read` calls `readItems` at the
   place, by the declared round's cut (`DeclaredRound.items`, Decl/Declared.lean), and does not hold the
   number of bytes that were read against that word.

2. What is checked when the file compiles. Only the types. Tests: Fmt/ParsedReadKnown.lean
[not in this library]; so here read: not tested in this library.

3. Theorems. None.

4. What is not claimed.
   The reader is no verifier and no cut of a file: whoever calls it must have the numbers, and the
   right numbers follow from the draws alone (Fmt/Rules8X.lean; Run/ParseLaxX.lean). At other
   numbers it cuts the same bytes in another way, or refuses.
   `ChainParsed.read` tests what the library's readers of the parts test: an element is below p
   (R1.3), the bytes do not end too early. It does not test all of `ChainParsed.fits`: not that an
   opening has at least one column and at most one for each draw; not that the listed positions
   increase, are below 2 ^ logN and are no more than the draws; not that there is at least one
   where the plan lists positions, and none where it lists none (told the number 3 at a width of 0
   bytes it gives three times the word 0, from no byte). `ChainParsed.readFit` tests these behind
   the cut. Both refuse numbers that have not one member for each declared round and, in it, for
   each declared opening.
   Stack. A chain's rounds and a round's openings are read by a loop (`rdZipL`). The library's
   `rdMany` (Fmt/Rules1.lean) and `readItems` (Fmt/Rules8.lean), by which the columns, a column's
   elements, the given digests, the listed positions and a message's items are read, call
   themselves and then lay a member in front: a program needs stack in proportion to these
   numbers. The port has both as loops, proved equal (OnBytes/Chain/Loops.lean: `rdManyT`,
   `readItemsT`, `rdOpeningT`); files of Fmt/ import no file of OnBytes/. (The port's `zipLoop`,
   OnBytes/Chain/Lists.lean, is another thing: `List.zip` as a loop.) The longest chain that these
   readers have met in a test: Fmt/ParsedReadKnown.lean [not in this library]; no compiled program
   has run them.
   Neither reader refuses a byte behind the chain: it returns the place, and the caller compares.
   A nonce or a listed position of more than eight bytes is read modulo 2 ^ 64.
   The bodies call no hash; below the module the library's hash lies all the same, through
   Fmt/Parsed.lean.
   The numbers tell some things twice (a tree as deep as the round's positions are long has as many
   columns as positions are listed; the number of given digests follows from the depth and the
   list). They are taken as `ChainParsed.counts` gives them; nothing compares them with each other.

Terms: lean/GLOSSARY.md.

-/
import Fmt.Parsed

namespace Fmt

/-! ## Readers of no one type -/

/-- A reader's value, turned by a function. The place behind it stays. -/
def rdMap {α β : Type} (f : α → β) (r : Rd α) : Rd β := fun b i =>
  (r b i).map fun x => (f x.1, x.2)

/-- The reader that reads no byte and gives x. -/
def rdGive {α : Type} (x : α) : Rd α := fun _ i => some (x, i)

/-- A reader, refused unless its value passes the test. -/
def rdFit {α : Type} (fit : α → Bool) (r : Rd α) : Rd α := fun b i =>
  match r b i with
  | some (x, j) => if fit x then some (x, j) else none
  | none => none

/-- n bytes as a word, the lowest first. -/
def rdLow (n : Nat) : Rd UInt64 := rdMap UInt64.ofNat (readLE n)

/-- A list of values, one after the other, each by its own reader: that of the members of the same
number in two lists. Refused if the two lists are not of one length. -/
def rdZip {δ ν α : Type} (R : δ → ν → Rd α) : List δ → List ν → Rd (List α)
  | [], [] => fun _ i => some ([], i)
  | d :: ds, n :: ns => fun b i =>
    match R d n b i with
    | some (x, j) =>
      match rdZip R ds ns b j with
      | some (l, k) => some (x :: l, k)
      | none => none
    | none => none
  | _, _ => fun _ _ => none

/-- The loop of `rdZipL`: what is read is laid behind acc. -/
def zipLoop {δ ν α : Type} (R : δ → ν → Rd α) (b : ByteArray) :
    List δ → List ν → Nat → Array α → Option (List α × Nat)
  | [], [], i, acc => some (acc.toList, i)
  | d :: ds, n :: ns, i, acc =>
    match R d n b i with
    | some (x, j) => zipLoop R b ds ns j (acc.push x)
    | none => none
  | _, _, _, _ => none

/-- `rdZip` as a loop: it calls itself last, so that a compiled program can run it in constant
stack. (No compiled program has been measured.) -/
def rdZipL {δ ν α : Type} (R : δ → ν → Rd α) (ds : List δ) (ns : List ν) : Rd (List α) :=
  fun b i => zipLoop R b ds ns i #[]

/-! ## The parts of a chain -/

/-- A column of W elements of F, then its leaf's salt (R7.8). -/
def rdColumn (f : Fld) (W salt : Nat) : Rd (List UInt64 × ByteArray) :=
  rdPair (rdMany (rdElt f) W) (rdBytes salt)

/-- An opening (R7.8) of a tree with columns of W elements and salts of salt bytes. n: its two
numbers, of columns and of given digests (`OpenParsed.counts`). -/
def OpenParsed.read (f : Fld) (W salt : Nat) (n : Nat × Nat) : Rd OpenParsed :=
  rdMap (fun x => ⟨x.1, x.2⟩) (rdPair (rdMany (rdColumn f W salt) n.1) (rdMany rdDigest n.2))

/-- A round's nonce, of n bytes: there is one exactly where the entry has proof-of-work bits
(R8.2). -/
def rdNonceAt (n work : Nat) : Rd (Option UInt64) :=
  if work == 0 then rdGive none else rdMap some (rdLow n)

/-- A round (R8.7) by its declared round r, under the setting S. n: its numbers, of listed positions
and of each opening (`RoundParsed.counts`). -/
def RoundParsed.read (S : PlanSetting) (r : DeclaredRound) (n : Nat × List (Nat × Nat)) :
    Rd RoundParsed :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩)
    (rdPair (readItems S.field r.items)
      (rdPair (rdNonceAt S.nonce r.entry.work)
        (rdPair (rdMany (rdLow S.posB) n.1)
          (rdZipL (fun w m => OpenParsed.read S.field w.1 w.2.1 m) (wantOpens S r) n.2))))

/-- A chain's 32 random bytes: they stand in the file in case (a) of R4.5 alone. -/
def rdRand : RandAt → Rd (Option ByteArray)
  | .inFile => rdMap some (rdBytes 32)
  | _ => rdGive none

/-- A chain (R8.1) by its declared chain c, under the setting S. N: its numbers, round by round
(`ChainParsed.counts`). -/
def ChainParsed.read (S : PlanSetting) (c : ChainDecl) (N : List (Nat × List (Nat × Nat))) :
    Rd ChainParsed :=
  rdMap (fun x => ⟨x.1, x.2⟩) (rdPair (rdRand c.rand) (rdZipL (RoundParsed.read S) c.rounds N))

/-- The same, refused unless what was read fits the declared chain. -/
def ChainParsed.readFit (S : PlanSetting) (c : ChainDecl) (N : List (Nat × List (Nat × Nat))) :
    Rd ChainParsed :=
  rdFit (fun X => X.fits S c) (ChainParsed.read S c N)

end Fmt
