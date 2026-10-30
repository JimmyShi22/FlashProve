-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2ParOf.lean: a parser for the parameter bytes of the second toy: the sizes, and the whole
description for the reader, out of the parameter bytes.

The second toy is a chain of three links. For vectors x_1, b_m, c_m over the base field, link m is
x_(m+1) = c_m = x_m b_m, entry by entry (m = 1, 2, 3). Each link has oracle messages of its own, and
one proximity test closes the chain.
"The programs" are the C++ implementation that comes with this Lean code; "the format page" is
docs/format/FORMAT.md, which comes with the programs. A description is what a verifier knows before
it sees a file; its parameter bytes hold the plan of rounds, the digest of the public files and some
further items. The file is a companion of Fmt/M1ParOf.lean with `specFrom` of Fmt/M1Prog.lean, and
of Fmt/M3ParOf.lean.

Sources. FORMAT.md, R12.2 (the item "codes") and R12.12 to R12.14. A message of a link is six words.
A link is its plain scalars and the list of its messages. The chain of links is:
   the numbers of its two codes;
   the list of its links;
   the list of the notices of the messages that are there at the start;
   the answers to a sample;
   the later stages of the last proximity test;
   the word of choices.
The cut made here (rdLink1, rdChain, with parOf) was compared with these three rules themselves, at
an edition of the format page that is not the one that ships, in a second, independent reading,
before the statements on it were proved. By a comparison of whole rule texts by program, R12.2 is
the same across four editions, and R12.12 to R12.14 across three of them, none of them the one that
ships.

1. What the file contains. Total functions on bytes. No Mathlib.
   `rdChain`: cuts the item "the chain of links". Its parts, in their order:
       two words;
       the list of links, each link a word and the list of its messages, six words each;
       two words;
       the later stages;
       the word of choices (`choicesBytes`, Fmt/M1Plan.lean).
     Of the two words in the middle, the first is the length of a list (the notices of what is there
     at the start). It is read here as a bare word and required to be 0. That is a right cut only
     where that list is empty: so a message at the start is refused, not read. The second is the
     number of answers to a sample.
   `parOf p`: the sizes (`Par`, Fmt/M2Types.lean), from what Fmt/ParamsRead.lean has read.
       The two codes (`C`, `Z`) are found by their numbers in "codes".
       The number of links is the length of the list of links.
       The first stage of the last proximity test has these two codes, the k of the last group, and
         h = 0 (`kOf`, `hOf`: Fmt/M2Types.lean). The last group holds what the last link carries on.
         By R12.14 the stages are listed from the second on, since the first is the group of the
         last carrying message. h = 0 because for L ≥ 1 that group is the one message `memG`, which
         has no mask row; this is tested at L = 1 .. 5.
       The positions at the last test's lists are those of the plan's entries "CS" in their order,
         then "BASE".
       The positions at a list of the frame (`Par.t`) and the bits of work are those of the plan's
         first entry "LOC". The frame is the pass through the rounds of the chain of links (`decBy`,
         `goLinks`, Fmt/M2Dec.lean).
       Field and salt are the plan's.
     Refused: an item that is missing, cut short or too long; a code's number beyond its list; a
     plan that has not as many lists as there are stages; a plan without an entry "LOC". Also
     refused, as a limit of this development and not by the format page: links other than this toy's
     (`linksRead`); a message at the start; answers, or a word of choices, other than 1.
   `fitsPlan p P`: the plan that was read is the plan of these sizes (`planOf`, Fmt/M2Plan.lean).
     The number of answers to a sample stands twice in the bytes: in the item and in the plan's
     sixth word. `parOf` asks that the item's be 1, and `planOf` writes 1. So where the plan fits,
     the two agree.
   `specFrom params`: the sizes and the description (`specOf`, Fmt/M2Plan.lean, at what was read),
     if the plan fits, the description's parameters are the bytes, and `Spec.ok` holds.

2. What is checked when the file compiles. Eight tests (#guard).
   At the two sets of sizes of the programs' description of the toy (`toyPar`, `tinyPar`) the sizes
   come back from the bytes, and `specFrom` gives a description.
   At the programs' own parameter bytes (Fmt/M2Theirs.lean: `Theirs.full`, `Theirs.tiny`) the sizes
   that are read are `toyPar` and `tinyPar`, and `specFrom` gives the parameters of
   `Theirs.specFull` and `Theirs.specTiny` back.
   The last group is one message without a mask row, at L = 1 .. 5.
   These changes to the item's words are refused: another number of messages in a link; another life
   of a message; a message at the start; two answers; a code's number beyond the list; a word too
   many. A message's life is here 1 where the message is kept for one later link, else 0 (`msgsOf`,
   Fmt/M2Items.lean).

3. Theorems. No theorem here; see Fmt/M2ParOfLaws.lean.

4. What is not claimed. It is not claimed that the sizes follow from the public file.

Notation: a message's six words (`msgWords`; the head of Fmt/M2Items.lean, at `linkMsgBytes`): main
rows; 1 if they are over the base field or if there are none, 3 if they are over the extension
field; mask rows; leaf class (0); moment; life.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M2Theirs

namespace Fmt
namespace M2
open Fmt.M1

def rdLink1 : Rd (UInt64 × List (List UInt64)) := rdPair rdWord (rdList (rdMany rdWord 6))

def rdChain :
    Rd (List UInt64 × List (UInt64 × List (List UInt64)) × List UInt64 ×
        List (Nat × Nat × Nat × Nat) × UInt64) :=
  rdPair (rdMany rdWord 2)
    (rdPair (rdList rdLink1) (rdPair (rdMany rdWord 2) (rdPair rdStages rdWord)))

/-- a message's six words -/
def msgWords (m : Mem) (moment life : Nat) : List Nat :=
  [m.rows, if m.overE && m.rows != 0 then 3 else 1, m.masks, 0, moment, life]

/-- the toy's links (`msgsOf`, Fmt/M2Items.lean), as the reader gives them -/
def linksRead (L : Nat) : List (UInt64 × List (List UInt64)) :=
  (List.range L).map fun i =>
    (0, (msgsOf L (i + 1)).map fun x => (msgWords x.1 x.2.1 x.2.2).map UInt64.ofNat)

/-- The sizes, from the parameters that `paramsRead` (Fmt/ParamsRead.lean) has read. -/
def parOf (p : Params) : Option Par :=
  match (p.valueOf nameCodes).bind (whole rdCodes),
    (p.valueOf nameLinks).bind (whole rdChain),
    p.plan.entries.find? (·.name == "LOC") with
  | some cs, some ([c, z], ls, [at0, ans], ss, ride), some loc =>
    match cs.1[c.toNat]?, cs.2[z.toNat]?, possOf p.plan with
    | some C, some Z, t :: tl =>
      if at0 == 0 && ans == 1 && ride == 1 &&
          ls == linksRead ls.length && tl.length == ss.length then
        (allSome ((ss.zip tl).map (stageOf cs))).map fun st =>
          { fld := p.plan.field, C := C, Z := Z, t := loc.poss, links := ls.length,
            stages := ⟨C, Z, kOf (memsOf ls.length (ls.length + 1)), 0, t⟩ :: st,
            work := loc.work, salt := p.plan.salt }
      else none
    | _, _, _ => none
  | _, _, _ => none

/-- The test that the plan that was read is the plan of these sizes. -/
def fitsPlan (p : Params) (P : Par) : Bool := samePlan p.plan (planOf P p.plan.nonce)

/-- The sizes and the description, from the parameters' bytes. -/
def specFrom (params : ByteArray) : Option (Par × Spec) :=
  (paramsRead params).bind fun p => (parOf p).bind fun P =>
    let S := specOf P p.cfg p.others p.plan.nonce
    if fitsPlan p P && decide (S.params = params) && S.ok then some (P, S) else none

def samePar (P Q : Par) : Bool :=
  P.fld == Q.fld && P.C == Q.C && P.Z == Q.Z && P.t == Q.t && P.links == Q.links &&
    P.stages == Q.stages && P.work == Q.work && P.salt == Q.salt

/-! ## Tests -/

namespace ParG2

def bytesOf (P : Par) : ByteArray := (specOf P zero32 (itemsOf P)).params
def back (P : Par) : Bool := ((paramsRead (bytesOf P)).bind parOf).any fun Q => samePar Q P
/-- the bytes with the item "the chain of links" spelled from other words -/
def withChain (P : Par) (f : List Nat → List Nat) : ByteArray :=
  paramsBytes (planOf P) zero32
    [(nameCodes, codesItem (P.stages.map (·.C)) (P.stages.map (·.Z))),
      (nameLinks, cat ((f (wordsOf (chainBytes P))).map u64n))]
def refused (b : ByteArray) : Bool := ((paramsRead b).map fun p => (parOf p).isNone) == some true

end ParG2

open ParG2 in
#guard back toyPar && back tinyPar
open ParG2 in
#guard [toyPar, tinyPar].all fun P => ((specFrom (bytesOf P)).map fun x => (samePar x.1 P, decide (x.2.params = bytesOf P), x.2.ok)) == some (true, true, true)
-- the programs' own bytes
#guard ((paramsRead Theirs.full).bind parOf).any (samePar · toyPar) && ((paramsRead Theirs.tiny).bind parOf).any (samePar · tinyPar)
#guard ((specFrom Theirs.full).map fun x => (samePar x.1 toyPar, decide (x.2.params = Theirs.specFull.params))) == some (true, true) && ((specFrom Theirs.tiny).map fun x => (samePar x.1 tinyPar, decide (x.2.params = Theirs.specTiny.params))) == some (true, true)
-- the last group: one message without a mask row: h = 0, at L = 1 .. 5
#guard [1, 2, 3, 4, 5].all fun L => memsOf L (L + 1) == [memG] && hOf (memsOf L (L + 1)) == 0
-- The item has 57 words at three links; unchanged, `refused` is false of them (it is false also of
-- bytes that `paramsRead` does not read). The places that the tests change: 4, the number of the
-- first link's messages; 16, the life of the first link's second message; 45, the length of the
-- list at the start; 46, the number of answers; 0, the code's number.
open ParG2 in
#guard (wordsOf (chainBytes tinyPar)).length == 57 && !refused (withChain tinyPar id)
open ParG2 in
#guard (wordsOf (chainBytes tinyPar))[4]? == some 2 && (wordsOf (chainBytes tinyPar))[16]? == some 1 && (wordsOf (chainBytes tinyPar))[45]? == some 0 && (wordsOf (chainBytes tinyPar))[46]? == some 1
open ParG2 in
#guard refused (withChain tinyPar fun w => w.set 4 1) && refused (withChain tinyPar fun w => w.set 16 0) && refused (withChain tinyPar fun w => w.set 45 1) && refused (withChain tinyPar fun w => w.set 46 2) && refused (withChain tinyPar fun w => w.set 0 3) && refused (withChain tinyPar fun w => w ++ [0])

end M2
end Fmt
