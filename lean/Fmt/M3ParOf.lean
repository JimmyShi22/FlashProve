-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3ParOf.lean: the entry file: a parser that gets the verifier's sizes out of the parameters.


An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link. "The programs" are the C++ implementation that
comes with this Lean code; "the format page" is docs/format/FORMAT.md, which comes with the
programs. A description is what a verifier knows before it sees a file; its parameter bytes hold the
plan of rounds, the digest of the public files and some further items. The file is the analogue, for
the entry file, of Fmt/M1ParOf.lean.

Sources. The format page (docs/format/FORMAT.md), as this file reads it:
R13.5 (the link's chain has the parameter items "configuration", "codes", "the link"; the tables'
own code does not stand in "codes"), R13.9 (the item "the link"), R13.10 (the first stage is not
written: it is the group, with k = 1 + the logarithm of R, rounded up, and h = 0). The head and the
definitions `rdLink` and `parOf` were compared with these rules
(by reading, not machine-checked). This file has not been held against the page as it ships, and
may differ from it: R13.5 may have one sentence
that points to two rules on the key file's items; R13.10 may say of the answers "as many each as
the plan's setting says", and have a clause on the word "mask ahead", which is named under `parOf`
below.

1. What the file contains. Total functions on bytes. No Mathlib.
   `rdLink`             Cuts the item "the link": fourteen words; the later stages, a list of four
                        words each; the word of choices. The fourteen words are the tables' shape
                        (a; the entries of a row's message; of its tail; v; the stored answers; the
                        bytes of a leaf's salt), nu_0, nu_j, the number of the group's code, the
                        number of its mask code, R, "rows high", the leaf class, "mask ahead".
   `parOf p`            The sizes (`Par`, Fmt/M3Types.lean) and the number of salt bytes in a leaf
                        of a stored table, from what Fmt/ParamsRead.lean has read. The codes: by
                        their numbers in "codes". The first stage: the group's code, its mask code,
                        1 + clog R, 0. The positions at the test's lists: the plan's entries "CS" in
                        their order, then "BASE". The bits of work: the plan's first entry "LINK".
                        Field, and the salt of a run's own trees: the plan's.
                        Refused: an item that is missing, cut short or too long; a code's number
                        beyond its list; a plan that has not as many lists as there are stages. So
                        is a plan without an entry "LINK". Also refused, as a limit of this
                        development and not by the format page: a leaf class other than 0; a word
                        "mask ahead", or a word of choices, other than 1; a word "rows high" other
                        than 0 or 1. (R13.10 may say what
                        "mask ahead" = 0 means: tree
                        0 then holds no mask. Plan and decision here cover the value 1 alone, so the
                        refusal stays.)








   `samePar`            The test that two records of sizes are the same, field by field (the record
                        has no decidable equality of its own).

2. What is checked when the file compiles. No test stands in this file.







3. Theorems. No theorem here; see Fmt/M3ParOfLaws.lean.

4. What is not claimed.
   It is not claimed that the sizes follow from the public files.
   With s > 0 the sizes are read, but the plan of Fmt/M3Plan.lean has no entry RECORD.

   No byte of the programs stands in this file.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M3Items

namespace Fmt
namespace M3
open Fmt.M1 Fmt.M2

def rdLink : Rd (List UInt64 × List (Nat × Nat × Nat × Nat) × UInt64) :=
  rdPair (rdMany rdWord 14) (rdPair rdStages rdWord)

/-- The sizes, read, with the salt of a table's leaf. What is refused: the head, 1. -/
def parOf (p : Params) : Option (Par × Nat) :=
  match (p.valueOf nameCodes).bind (whole rdCodes),
    (p.valueOf nameLink).bind (whole rdLink),
    p.plan.entries.find? (·.name == "LINK") with
  | some cs, some ([a, l, r, v, s, ts, n0, nj, c, z, R, hi, lc, ah], ss, ride), some lk =>
    match cs.1[c.toNat]?, cs.2[z.toNat]?, possOf p.plan with
    | some C, some Z, t :: tl =>
      if lc == 0 && ah == 1 && ride == 1 && (hi == 0 || hi == 1) && tl.length == ss.length then
        (allSome ((ss.zip tl).map (stageOf cs))).map fun st =>
          ({ fld := p.plan.field, T := ⟨a.toNat, l.toNat, r.toNat⟩, v := v.toNat, s := s.toNat,
             nu0 := n0.toNat, nuj := nj.toNat, C := C, Z := Z, R := R.toNat, high := hi == 1,
             stages := ⟨C, Z, 1 + clog R.toNat, 0, t⟩ :: st, work := lk.work, salt := p.plan.salt },
            ts.toNat)
      else none
    | _, _, _ => none
  | _, _, _ => none

def samePar (P Q : Par) : Bool :=
  P.fld == Q.fld && P.T == Q.T && P.v == Q.v && P.s == Q.s && P.nu0 == Q.nu0 && P.nuj == Q.nuj &&
    P.C == Q.C && P.Z == Q.Z && P.R == Q.R && P.high == Q.high && P.stages == Q.stages &&
    P.work == Q.work && P.salt == Q.salt

/-! ## Tests -/

namespace ParG

/-- The parameters' bytes of sizes, at a made-up configuration's digest. -/
def bytesOf (P : Par) (tsalt : Nat := P.salt) : ByteArray :=
  (entrySpec P zero32 zero32 zero32 tsalt).base.params
def back (P : Par) (tsalt : Nat := P.salt) : Bool :=
  ((paramsRead (bytesOf P tsalt)).bind parOf).any fun x => samePar x.1 P && x.2 == tsalt
/-- The bytes with the item "the link" spelled from other words: f is applied to its words. -/
def withLink (P : Par) (f : List Nat → List Nat) : ByteArray :=
  paramsBytes (planOf P) zero32
    [(nameCodes, codesBytes (baseCodes P false) (maskCodes P)),
      (nameLink, cat ((f (linkWords P false)).map u64n))]
def refused (b : ByteArray) : Bool := ((paramsRead b).map fun p => (parOf p).isNone) == some true

end ParG













end M3
end Fmt
