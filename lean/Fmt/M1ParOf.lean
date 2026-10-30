-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1ParOf.lean: the sizes of the first toy (a product test), read off the parameters' bytes of its
chain, not inferred.

The first toy is a test protocol for the claim that three rows a, b, c of one oracle message have
a_i b_i = c_i for every i (the heads of Fmt/M1Types.lean and Fmt/M1Psc.lean).
The parameters of a run come as one string of bytes. Fmt/ParamsRead.lean cuts the parameters' bytes
into plan, configuration's digest and further items. Here the record of sizes (`Par`,
Fmt/M1Types.lean), which the verifier's decision takes, is made from them. The plan that was read is
then compared with the plan that these sizes give (Fmt/M1Plan.lean).
Total functions on bytes, with tests (#guard). No Mathlib.

Sources. The format page (docs/format/FORMAT.md, which comes with the programs, that is, with the
C++
implementation that accompanies this Lean code), in an edition that is not the one that ships (R12.1
to R12.7 are the same in a second edition, also not the one that ships: compared by a program, rule
by rule): R12.1, R12.2 (a code; the two lists of codes;
equal triples stand once), R12.3 (a notice), R12.4 (a stage's four words), R12.5 (the choices: one
word), R12.6 (the run's five items behind the plan, under their exact names), R12.7 (its public
file).

Main names:
  `rdCode`, `rdCodes`: a code is three words. The item "codes" is two lists of codes, main and mask,
    each behind the word of its length (the page's program line for that type).
  `parOf p : Option Par`: from what was read (the plan, the item "codes", the item on the stages):
      the field and the salt's bytes are the plan's;
      a stage is four words: the place of the main code in its list, the place of the mask code in
        its list, k, h;
      the positions of a stage are the plan's: those of the entries "CS", in their order, then those
        of the entries "BASE";
      K is the number of elements that the plan's first entry "ZERO" draws;
      the bits of work are those of the plan's first entry "BASE".
    Refused:
      one of these two items is missing or is not spelled so;
      a code's place beyond its list;
      a plan without an entry "ZERO" or without an entry "BASE";
      another number of entries "CS" and "BASE" together than stages.
    (`onceL`, `noIn`, `codesItem`: Fmt/M1Codes.lean: in the item "codes" a triple that is in its
    list already is not entered again, and a stage names a code by its place in that list: by an
    answer to questions about the programs.)
  `fillWord`: the entries that fill a stage's mask rows up: 0 at the first stage; from the second on
    2^h l_zk − (2 l_zk(prev) + r(prev) + 2 r_zk(prev)). In a third
    edition of the format page, also not the one that ships, it is a
    stage's fifth word; in the two editions named under Sources it is no
    word of an item (every public fact has one home): it follows from the
    sizes.
  `itemsOf P`: the four further items as the programs spell them (R12.6), from the sizes.
  `publicFile first target P nonceB`: the run's public file (R12.7), from the sizes: the first line
    (free text) and the target's bits are arguments.
  `fitsPlan p P`: the plan that was read is `planOf P` at the nonce's bytes that were read, word for
    word, name for name.
  `Checked`, `check b`: all in one, on the parameters' bytes: what holds and what does not, part by
    part. The result is a record of truth values, so that the first part that differs can be named.
    The parts:
      `read`: the bytes are read;
      `back`: spelled again they are the same bytes;
      `sizes`: `parOf` gives sizes;
      `fits`: `Par.planOK` and `Par.fits` (Fmt/M1Plan.lean);
      `plan`: the plan fits (`fitsPlan`);
      `names`: the further items have the four names, in their order;
      `codes`, `notice`, `stages`, `choices`: the four items are this library's spellings at these
      sizes
        (`itemsOf`).

Tests (#guard). (At the programs' own parameter bytes: Fmt/M1Theirs.lean.)
  Bytes spelled by this library from the sizes, at the toy's sizes and at a tiny size: read and
  spelled again;
    `parOf` gives the sizes; every part of `check` holds.
  At a small toy of this library's own (Fmt/Toy1.lean): read and spelled again; `parOf` refuses
  (it has no such
    items).
  A plan with the word "rows" of its entries "CS" altered: `fitsPlan` fails, and the first place is
    named.
  Two other forms (five words a stage; two words of
    choices): the parts "sizes", "choices" fail.

Notation:
  a code (a, l, r): codewords of length 2^a, messages of l entries, a tail of r entries (`Code`,
    Fmt/M1Codes.lean);
  k, h: fields of `Stage` (Fmt/M1Types.lean, whose head tells them);
  l_zk, r, r_zk: a stage's `Z.l`, `C.r`, `Z.r` (`Stage`, Fmt/M1Types.lean);
  (prev): those of the stage before it (`fillWord`, `fills`).

Limits: no theorem in this file (theorems on these functions: stated in Fmt/M1ParOfLaws.lean, proved
in Fmt/M1ParOfLawsProofs.lean).

Terms: lean/GLOSSARY.md.
-/
import Fmt.ParamsRead
import Fmt.M1Plan
import Fmt.Toy1

namespace Fmt
namespace M1

def rdCode : Rd Code := fun b i =>
  match rdMany rdWord 3 b i with
  | some ([a, l, r], j) => some (⟨a.toNat, l.toNat, r.toNat⟩, j)
  | _ => none

/-- the item "codes" -/
def rdCodes : Rd (List Code × List Code) := rdPair (rdList rdCode) (rdList rdCode)

def rdStage4 : Rd (Nat × Nat × Nat × Nat) := fun b i =>
  match rdMany rdWord 4 b i with
  | some ([a, z, k, h], j) => some ((a.toNat, z.toNat, k.toNat, h.toNat), j)
  | _ => none

/-- the item on the stages -/
def rdStages : Rd (List (Nat × Nat × Nat × Nat)) := rdList rdStage4

def nameCodes : String := "codes"
def nameNotice : String := "the oracle message a, b, c"
def nameStages : String := "the stages of the proximity test"
def nameChoices : String := "the choices of the proximity test"

/-- a stage from its four words, the two lists of codes and its number of positions -/
def stageOf (cs : List Code × List Code) (s : (Nat × Nat × Nat × Nat) × Nat) : Option Stage :=
  match cs.1[s.1.1]?, cs.2[s.1.2.1]? with
  | some C, some Z => some ⟨C, Z, s.1.2.2.1, s.1.2.2.2, s.2⟩
  | _, _ => none

/-- the positions of the stages, by the plan: the entries "CS" in their order, then the entries
"BASE" -/
def possOf (P : Plan) : List Nat :=
  (P.entries.filter (·.name == "CS")).map (·.poss) ++
    (P.entries.filter (·.name == "BASE")).map (·.poss)

/-- all or nothing -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | some x :: l => (allSome l).map (x :: ·)
  | none :: _ => none

/-- The sizes, read. What is taken from where, and what is refused: the head, `parOf`. -/
def parOf (p : Params) : Option Par :=
  match (p.valueOf nameCodes).bind (whole rdCodes),
    (p.valueOf nameStages).bind (whole rdStages),
    p.plan.entries.find? (·.name == "ZERO"),
    p.plan.entries.find? (·.name == "BASE") with
  | some cs, some ss, some z, some bs =>
    if (possOf p.plan).length == ss.length then
      (allSome ((ss.zip (possOf p.plan)).map (stageOf cs))).map fun st =>
        { fld := p.plan.field, K := z.drawE, stages := st, work := bs.work, salt := p.plan.salt }
    else none
  | _, _, _, _ => none

/-- the entries that fill a stage's mask rows up: no word of an item (R12.4: it follows from the
stage's words and the codes) -/
def fillWord : Option Stage → Stage → Nat
  | none, _ => 0
  | some prev, s => 2 ^ s.h * s.Z.l - (2 * prev.Z.l + prev.C.r + 2 * prev.Z.r)

def fills : Option Stage → List Stage → List Nat
  | _, [] => []
  | prev, s :: l => fillWord prev s :: fills (some s) l

/-- The four further items, from the sizes. -/
def itemsOf (P : Par) : List (String × ByteArray) :=
  let cm := onceL (P.stages.map (·.C))
  let cz := onceL (P.stages.map (·.Z))
  [(nameCodes, codesItem (P.stages.map (·.C)) (P.stages.map (·.Z))),
   (nameNotice, noticeBytes 0 0 3 1 1 1 0),
   (nameStages, stagesBytes (P.stages.map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h))),
   (nameChoices, choicesBytes true)]

/-- The run's public file: lines, each ended by a line feed. -/
def publicFile (first : String) (target : Nat) (P : Par) (nonceB : Nat := 8) : ByteArray :=
  let s1 := P.stages.headD default
  ascii (String.join
    (([first, s!"format H8{P.fld.num}1", s!"target {target}", s!"work-on-positions {P.work}",
      s!"salt-bytes {P.salt}", s!"nonce-bytes {nonceB}", "position-bytes 0", "samples 1",
    s!"log-length {P.K}", s!"log-n {s1.C.a}", s!"mask-log-n {s1.Z.a}"] ++ (P.stages.drop 1).map fun s => s!"stage {s.k} {s.h} {s.C.a} {s.Z.a}").map (· ++ "
")))

def samePlan (A B : Plan) : Bool :=
  A.field == B.field && A.salt == B.salt && A.nonce == B.nonce && A.posB == B.posB &&
    A.samples == B.samples && A.saved == B.saved && A.entries == B.entries

/-- The test that the plan that was read is the plan of these sizes. -/
def fitsPlan (p : Params) (P : Par) : Bool := samePlan p.plan (planOf P p.plan.nonce)

/-- the first place at which the plan that was read and the plan of these sizes have different
entries -/
def firstOff (p : Params) (P : Par) : Option Nat :=
  ((p.plan.entries.zip (planOf P p.plan.nonce).entries).zipIdx.find? fun x =>
    x.1.1 != x.1.2).map (·.2)

/-- what holds, part by part -/
structure Checked where
  read    : Bool
  back    : Bool
  sizes   : Bool
  fits    : Bool
  plan    : Bool
  names   : Bool
  codes   : Bool
  notice  : Bool
  stages  : Bool
  choices : Bool
  deriving DecidableEq, Repr

/-- All in one: every part of `Checked`, on the parameters' bytes. -/
def check (b : ByteArray) : Checked :=
  match paramsRead b with
  | none => ⟨false, false, false, false, false, false, false, false, false, false⟩
  | some p =>
    match parOf p with
    | none =>
      ⟨true, p.bytes = b, false, false, false,
        p.others.map (·.1) == [nameCodes, nameNotice, nameStages, nameChoices],
        false, false, false, false⟩
    | some P =>
      ⟨true, p.bytes = b, true, P.planOK && P.fits, fitsPlan p P,
        p.others.map (·.1) == [nameCodes, nameNotice, nameStages, nameChoices],
        p.valueOf nameCodes == (itemsOf P).lookup nameCodes,
        p.valueOf nameNotice == (itemsOf P).lookup nameNotice,
        p.valueOf nameStages == (itemsOf P).lookup nameStages,
        p.valueOf nameChoices == (itemsOf P).lookup nameChoices⟩

def allHold : Checked := ⟨true, true, true, true, true, true, true, true, true, true⟩

def samePar (A B : Par) : Bool :=
  A.fld == B.fld && A.K == B.K && A.stages == B.stages && A.work == B.work && A.salt == B.salt

/-! ## Tests -/

-- Bytes spelled by this library from the sizes: every part holds; the sizes come back
#guard check (specOf toyPar zero32 (itemsOf toyPar)).params = allHold && check (specOf tinyPar zero32 (itemsOf tinyPar)).params = allHold
#guard ((paramsRead (specOf toyPar zero32 (itemsOf toyPar)).params).bind parOf).any fun P => samePar P toyPar
#guard ((paramsRead (specOf tinyPar zero32 (itemsOf tinyPar)).params).bind parOf).any fun P => samePar P tinyPar
#guard ((paramsRead (specOf tinyPar zero32 (itemsOf tinyPar)).params).map fun p => (decide (p.cfg = zero32), p.plan.nonce, p.valueOf nameChoices)) = some (true, 8, some (u64n 1))
-- the items' lengths at the toy's sizes: 17 words; 7; 1 + 3 * 4; 1
#guard (itemsOf toyPar).map (fun x => x.2.size) = [136, 56, 104, 8]
-- a small toy of this library's own (Fmt/Toy1.lean): read and spelled again; it has no such items
#guard ParamsG.back Toy1.params
#guard ((paramsRead Toy1.params).map fun p => (parOf p).isNone) = some true
-- the rows of every CS altered: sizes are still read, the plan no longer fits, the place is named
#guard ((paramsRead (paramsBytes { planOf tinyPar with entries := (planOf tinyPar).entries.map fun e => if e.name == "CS" then { e with rows := e.rows + 1 } else e } zero32 (itemsOf tinyPar))).bind fun p => (parOf p).map fun P => (fitsPlan p P, firstOff p P)) = some (false, some 15)
#guard ((paramsRead (specOf tinyPar zero32 (itemsOf tinyPar)).params).bind fun p => (parOf p).map fun P => firstOff p P) = some none
-- a stage that names a code beyond the list: refused
#guard ((paramsRead (paramsBytes (planOf tinyPar) zero32 [(nameCodes, codesBytes [⟨9, 16, 3⟩] [⟨9, 16, 3⟩]), (nameStages, stagesBytes [(1, 0, 2, 0), (0, 0, 1, 1), (0, 0, 0, 0)])])).map fun p => (parOf p).isNone) = some true
-- two other forms: five words a stage: the item is not
-- spelled so: no sizes; two words of choices: that part fails
#guard (check (paramsBytes (planOf tinyPar) zero32 ((itemsOf tinyPar).map fun x => if x.1 == nameStages then (x.1, u64n 3 ++ cat ((List.replicate 15 0).map u64n)) else x))).sizes == false
#guard check (paramsBytes (planOf tinyPar) zero32 ((itemsOf tinyPar).map fun x => if x.1 == nameChoices then (x.1, u64n 1 ++ u64n 1) else x)) = { allHold with choices := false }

end M1
end Fmt
