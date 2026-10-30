-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParamsRead.lean: a reader of the parameter bytes of a chain: the format's version, the plan, the
configuration's digest, the further items.

What for. The parameter bytes of a chain that another program has made come as one string. With this
reader they are cut, so that every part can be compared with what this library computes: the plan
with a plan of this library, each item with this library's spelling of it. Fmt/Rules4.lean spells
these bytes (`paramsBytes`); here they are read. These are total functions on bytes. A chain is the
non-interactive form of one interactive protocol (the head of Fmt/Rules4.lean); its plan (`Plan`,
Fmt/Plan.lean) has a field, five numbers and a list of entries, each a name and eleven numbers; an
item (`item`, Fmt/Rules4.lean) is a name, the word (8 bytes, the lowest first: `u64n`,
Fmt/Rules1.lean) of the value's length, and the value.

Sources. The format page (docs/format/FORMAT.md, which comes with the programs, the C++
implementation that comes with this Lean code), in an edition that is not the one that ships: R4.1
(an item: a name, the word of the value's length, the
value), R4.3 (the parameter bytes: the item of the version; the plan: eight words, then its entries,
each a name and eleven words; the item "configuration"; the other items), R1.9 (a reader refuses a
length word greater than the bytes left, and a name with a byte outside 0x20 to 0x7E). R4.1 and
R1.9 are the same across two other editions, neither of them the one that ships; R4.3 differs
between editions (as
restated, at second
hand: a pointer for the entry RECORD; nothing on the bytes that paramsRead cuts). No Mathlib.

1. What the file contains.
   `nameOf b` (the bytes are ASCII: the reader of names has tested it).
   `rdPlan`. The plan. Refused: a field's number other than 1, 2; a hash's number other than 1; more
     entries than bytes are left.
   `Params` (a structure). The plan (with its field), the configuration's digest, the further items.
   `paramsRead b : Option Params`. Refused, beside what the parts refuse: a first item that is not
     the version's, or whose value is not the version of the plan's field; a first item behind the
     plan that is not named "configuration", or whose value has not 32 bytes; bytes that are left
     over or lacking.

2. What is checked when the file compiles. 19 tests (#guard). At the page's example plan in both
fields: the bytes are read; what is read, spelled again, is the bytes; the plan's field and entries,
the configuration and the items' names are those from which the bytes were spelled. In the second
field alone: so are the plan's other numbers and the item's value. Refusals: one byte less; one byte
more; the other field's version; a name with a byte outside the range; a hash's number 2; a length
word beyond the end.
   Not tested here: `Plan.ok`, and whether a plan is the plan of a protocol. The seventh word
     ("saved") is read as it stands.

3. Theorems. None in this file. That reading undoes spelling, and that only spellings are read, is
tested at these strings. The first half is a theorem for all parameters within bounds that can be
tested (`Params.fit`): `params_back`, stated in Fmt/ParamsReadLaws.lean and proved in
Fmt/ParamsReadLawsProofs.lean. The second half is only tested and not proved.

4. What is not claimed. See 2 and 3.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules4

namespace Fmt

/-- the bytes of a name as a string -/
def nameOf (b : ByteArray) : String := String.ofList (b.data.toList.map fun x => Char.ofNat x.toNat)

/-- Reads an item. -/
def rdItem : Rd (String × ByteArray) := fun b i =>
  match rdName b i with
  | some (n, j) => (rdText b j).map fun x => ((nameOf n, x.1), x.2)
  | none => none

/-- eleven words as an entry under a name -/
def entryOf (name : String) : List UInt64 → Option Entry
  | [a, b, c, d, e, f, g, h, i, j, k] =>
    some ⟨name, a.toNat, b.toNat, c.toNat, d.toNat, e.toNat, f.toNat, g.toNat, h.toNat,
        i.toNat, j.toNat, k.toNat⟩
  | _ => none

/-- Reads an entry of a plan. -/
def rdEntry : Rd Entry := fun b i =>
  match rdName b i with
  | some (n, j) =>
    match rdMany rdWord 11 b j with
    | some (ws, k) => (entryOf (nameOf n) ws).map fun e => (e, k)
    | none => none
  | none => none

def fldOf : Nat → Option Fld
  | 1 => some .one
  | 2 => some .two
  | _ => none

/-- Reads the plan. -/
def rdPlan : Rd Plan := fun b i =>
  match rdMany rdWord 8 b i with
  | some ([f, hsh, salt, nonce, posB, samples, saved, n], j) =>
    match fldOf f.toNat with
    | some fld =>
      if hsh == 1 && decide (j + n.toNat ≤ b.size) then
        (rdMany rdEntry n.toNat b j).map fun x =>
          (⟨fld, salt.toNat, nonce.toNat, posB.toNat, samples.toNat, saved.toNat, x.1⟩, x.2)
      else none
    | none => none
  | _ => none

/-- items up to the end of the bytes; the fuel: no more items than bytes -/
def rdItems : Nat → Rd (List (String × ByteArray))
  | 0 => fun b i => if i == b.size then some ([], i) else none
  | fuel + 1 => fun b i =>
    if i == b.size then some ([], i)
    else
      match rdItem b i with
      | some (x, j) => (rdItems fuel b j).map fun y => (x :: y.1, y.2)
      | none => none

/-- What the parameters' bytes hold. -/
structure Params where
  plan   : Plan
  cfg    : ByteArray
  others : List (String × ByteArray)

/-- The reader of the parameter bytes. -/
def paramsRead (b : ByteArray) : Option Params :=
  match rdItem b 0 with
  | some ((vn, vv), i) =>
    match rdPlan b i with
    | some (P, j) =>
      if vn == versionName && vv == versionValue P.field then
        match rdItem b j with
        | some ((cn, cv), k) =>
          if cn == configName && cv.size == 32 then
            (rdItems b.size b k).map fun x => ⟨P, cv, x.1⟩ else none
        | none => none
      else none
    | none => none
  | none => none

/-- what was read, spelled again -/
def Params.bytes (p : Params) : ByteArray := paramsBytes p.plan p.cfg p.others

/-- the value of the first further item of a name -/
def Params.valueOf (p : Params) (name : String) : Option ByteArray :=
  (p.others.find? fun x => x.1 == name).map (·.2)

/-! ## Tests -/

namespace ParamsG

/-- read, and spelled again the same bytes -/
def back (b : ByteArray) : Bool := (paramsRead b).any fun p => p.bytes = b

-- the page's toy plan of six rounds: the first two tests in both fields, the last two in field 2
#guard back (Toy4.params .two) && back (Toy4.params .one)
#guard [Fld.one, Fld.two].all fun f => (paramsRead (Toy4.params f)).any fun p => p.plan.entries == (Toy4.plan f).entries && p.plan.field == f && p.cfg = Toy4.cfg && p.others.map (·.1) == ["toy: a table's length"]
#guard ((paramsRead (Toy4.params .two)).bind fun p => p.valueOf "toy: a table's length") = some (u64n 1024)
#guard ((paramsRead (Toy4.params .two)).map fun p => (p.plan.salt, p.plan.nonce, p.plan.posB, p.plan.samples, p.plan.saved, p.plan.entries.length)) = some (40, 8, 0, 1, 1, 6)
-- Refusals.  One byte less; one byte more
#guard (paramsRead ((Toy4.params .two).extract 0 ((Toy4.params .two).size - 1))).isNone
#guard (paramsRead (Toy4.params .two ++ zeroBytes 1)).isNone
#guard (paramsRead ByteArray.empty).isNone
-- the other field's version in front of this field's plan
#guard (paramsRead (item versionName (versionValue .one) ++ (Toy4.plan .two).bytes ++ item configName Toy4.cfg)).isNone
#guard (paramsRead (item versionName (versionValue .two) ++ (Toy4.plan .two).bytes ++ item configName Toy4.cfg)).isSome
-- no configuration; a configuration of 31 bytes; another name in its place
#guard (paramsRead (paramsHead (Toy4.plan .two))).isNone
#guard (paramsRead (paramsHead (Toy4.plan .two) ++ item configName (zeroBytes 31))).isNone
#guard (paramsRead (paramsHead (Toy4.plan .two) ++ item "configuratioN" (zeroBytes 32))).isNone
-- a further item whose name has a byte outside the range; whose length word goes beyond the end
#guard (paramsRead (paramsBytes (Toy4.plan .two) Toy4.cfg [] ++ text ⟨#[0x41, 0x0A]⟩ ++ u64n 0)).isNone
#guard (paramsRead (paramsBytes (Toy4.plan .two) Toy4.cfg [] ++ textS "a" ++ u64n 9 ++ zeroBytes 8)).isNone
#guard (paramsRead (paramsBytes (Toy4.plan .two) Toy4.cfg [] ++ textS "a" ++ u64n 8 ++ zeroBytes 8)).isSome
-- a hash's number 2; a field's number 3
#guard (rdPlan (u64n 2 ++ u64n 2 ++ cat ((List.replicate 6 0).map u64n)) 0).isNone
#guard (rdPlan (u64n 3 ++ u64n 1 ++ cat ((List.replicate 6 0).map u64n)) 0).isNone
#guard (rdPlan (u64n 2 ++ u64n 1 ++ cat ((List.replicate 6 0).map u64n)) 0).isSome
-- more entries than bytes are left
#guard (rdPlan (u64n 2 ++ u64n 1 ++ cat ((List.replicate 5 0).map u64n) ++ u64n (2 ^ 40)) 0).isNone

end ParamsG

end Fmt
