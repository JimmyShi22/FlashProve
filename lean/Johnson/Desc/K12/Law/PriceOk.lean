-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SpendOk
import Fmt.Rules6Draws
/-
Johnson/Desc/K12/Law/PriceOk.lean: K12's CONDITION: THE NUMBERS: for each round of the place's chain, what the library's own comparisons on naturals (OnBytes/Slice/ManyNum.lean: LastNum · CsNum; wk_elem_round's premises) give at the place's numbers and at a radius for each stage that is handed in. DEFINITIONS WITH CODE ALONE; NO THEOREM; NO Mathlib BENEATH IT. NOTHING ON HIDING. **NO NUMBER HERE IS A BOUND ON THE RELEASE's SOUNDNESS: each is a share of ONE round's challenge values; W of the k bits are work; the radii below a third are not the release's; not to be held against 128.** WHICH HALF HAS A THEOREM: NO HALF HAS A THEOREM IN THIS LIBRARY. priceLines AT ANY RADII OR LISTS, AND THE COLUMN «GREATEST k», ARE READ BY NO THEOREM: A TRANSCRIPTION OF THE LIBRARY's COMPARISONS.
  dB a              the stage's distance as the library has it (Sg.d, Numbers.lean): the smaller of the main code's and the scaled mask code's.
  thirdB a          the greatest radius below a third of it: THE REGIME IN WHICH Chain.Holds IS PROVED WITH NO FACT ON CODES OWED (Johnson/Desc/K12/Law/ChainHolds.lean: holds_third).
  lastNumB · csNumB W k a t B r (lst)     the two comparisons, term for term; lst: the list's size (1 in the library's CsNum).
  bitsOf f          the LAST k ≤ 512 at which the comparison f holds (0 if none): the greatest, and all below it hold too, where f is falling in k: not shown here; both comparisons have 2 ^ k on their small side alone.
  elemB w           the premises of wk_elem_round on a round that draws one element: the draws are [elem, no matrix entry] · five hash blocks · no test bit · logN ≤ 64: then a count of at most 2 ^ 32 is at most 2 ^ -128 of the round's challenge values.
  priceCl | priceAll | priceOk p k | priceBits p     the named clauses; no theorem of this library gives from them «every error count of the place's chain is at most 2 ^ -k of its round's challenge values», at the greatest radii below a third and lists of one member; the greatest such k ≤ 128.
  priceLines        one line a stage: the distance, the radius, the round of positions' a · t · B · W and ITS GREATEST k; and whether the stage's rounds of one element meet elemB.
W OF THE k BITS ARE WORK (the round's test bits), as the library's comparisons count them.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)
open Fmt.M1 (Stage)

def dB (a : Stage) : Nat :=
  min (2 ^ a.C.a - (a.C.r + a.C.l) + 1) (2 ^ (a.C.a - a.Z.a) * (2 ^ a.Z.a - (a.Z.r + a.Z.l) + 1))

def thirdB (a : Stage) : Nat := (dB a - 1) / 3

def lastNumB (W k a t B r : Nat) : Bool :=
  decide ((2 ^ 128 + 1) ^ B * (2 ^ a - r - 1) ^ t * 2 ^ k ≤ (2 ^ 128) ^ B * (2 ^ a) ^ t * 2 ^ W)

def csNumB (lst W k a t B r : Nat) : Bool :=
  lastNumB W k a t B r &&
    decide ((2 ^ 128 + 1) ^ B * (2 ^ a - r - 1) ^ t * 2 ^ k * 2 ^ 191 +
        (2 ^ 128 + 1) ^ B * ((2 ^ a) ^ t * (lst * (1 + 3 * t))) * 2 ^ k ≤
      (2 ^ 128) ^ B * (2 ^ a) ^ t * 2 ^ W * 2 ^ 191)

/-- The greatest k ≤ 512 with f k (f is falling in k). -/
def bitsOf (f : Nat → Bool) : Nat := ((List.range 513).filter f).getLast?.getD 0

def blocksB (w : WR) : Nat := Fmt.blocksFor (Fmt.wordsAtMost w.entry w.kind)

def elemB (w : WR) : Bool :=
  decide (Fmt.dsOf w.entry w.kind = [.elem, .trits 0]) && blocksB w == 5 && w.entry.work == 0 &&
    decide (w.entry.logN ≤ 64)

/-- The round of positions has the stage's a and t, and draws what the comparison is typed for. cs: one element behind the positions. -/
def posB (cs : Bool) (a : Stage) (w : WR) : Bool :=
  decide (Fmt.dsOf w.entry w.kind =
    List.replicate a.t (Fmt.Draw.pos a.C.a) ++ (if cs then [.elem, .trits 0] else [.trits 0])) &&
    decide (w.entry.logN ≤ 64)

def priceL (rad : Stage → Nat) (lst : Stage → Nat) (tagS : String) :
    Nat → Stage → List Stage → List WR → List String
  | j, a, [], l =>
    match l with
    | [dL, dB'] =>
      [s!"{tagS}.PRICE.{j}\tLAST\td {dB a}\tradius {rad a}\t3e<d {decide (3 * rad a < dB a)} · 2e<d {decide (2 * rad a < dB a)} · e<d {decide (rad a < dB a)} · e≤2^30 {decide (rad a ≤ 2 ^ 30)}\tBASE: a {a.C.a} · t {a.t} · B {blocksB dB'} · W {dB'.entry.work} · draws as typed {posB false a dB'}\tGREATEST k {bitsOf fun k => lastNumB dB'.entry.work k a.C.a a.t (blocksB dB') (rad a)}\tBASE lambda a round of one element {elemB dL}"]
    | _ => [s!"{tagS}.PRICE.{j}\tcut at the last stage"]
  | j, a, b :: rest, l =>
    match l with
    | dE :: dT :: l' =>
      match (dT :: l').drop (kk a) with
      | _ :: dC :: l'' =>
        s!"{tagS}.PRICE.{j}\tSTEP\td {dB a}\tradius {rad a}\t3e<d {decide (3 * rad a < dB a)} · 2e<d {decide (2 * rad a < dB a)} · e<d {decide (rad a < dB a)} · e≤2^30 {decide (rad a ≤ 2 ^ 30)}\tCS: a {a.C.a} · t {a.t} · B {blocksB dC} · W {dC.entry.work} · draws as typed {posB true a dC} · list {lst b}\tGREATEST k {bitsOf fun k => csNumB (lst b) dC.entry.work k a.C.a a.t (blocksB dC) (rad a)}\tFOLD epsilon | FOLD round rounds of one element {elemB dE} | {elemB dT}" ::
          priceL rad lst tagS (j + 1) b rest l''
      | _ => [s!"{tagS}.PRICE.{j}\tcut"]
    | _ => [s!"{tagS}.PRICE.{j}\tcut"]

/-- The clauses under which the library's comparisons give 2 ^ -k at every round of the place's chain, AT THE GREATEST RADII BELOW A THIRD AND LISTS OF ONE MEMBER. W: the test bits of every round of positions. -/
def priceCl (W k : Nat) : Nat → Stage → List Stage → List WR → Clauses
  | j, a, [], l =>
    match l with
    | [dL, dB'] =>
      tag j [("price.hi", decide (thirdB a ≤ 2 ^ 30)), ("price.lambda", elemB dL),
        ("price.base", posB false a dB'), ("price.work", decide (dB'.entry.work = W)),
        ("price.last", lastNumB W k a.C.a a.t (blocksB dB') (thirdB a))]
    | _ => [(toString j ++ ":cut at the last stage", false)]
  | j, a, b :: rest, l =>
    match l with
    | dE :: dT :: l' =>
      match (dT :: l').drop (kk a) with
      | _ :: dC :: l'' =>
        tag j [("price.hi", decide (thirdB a ≤ 2 ^ 30)), ("price.eps", elemB dE), ("price.two", elemB dT),
          ("price.cs", posB true a dC), ("price.work", decide (dC.entry.work = W)),
          ("price.num", csNumB 1 W k a.C.a a.t (blocksB dC) (thirdB a))] ++ priceCl W k (j + 1) b rest l''
      | _ => [(toString j ++ ":cut: no two rounds behind the fold's", false)]
    | _ => [(toString j ++ ":cut: no two rounds of a fold", false)]

def priceAll (p : P12) (k : Nat) : Clauses :=
  match p.nums.stages, writtenOf p.nums with
  | a :: rest, some (_ :: l) => priceCl p.nums.work k 0 a rest l
  | _, _ => [("no stage, or the declared rounds cannot be written", false)]


def priceOk (p : P12) (k : Nat) : Bool := decide (k ≤ 128) && ok (priceAll p k)

/-- The greatest k ≤ 128 at which priceOk says yes (0 if none). -/
def priceBits (p : P12) : Nat := ((List.range 129).filter (priceOk p)).getLast?.getD 0

/-- The lines at a place, at radii and lists handed in. -/
def priceLines (tagS : String) (p : P12) (rad : Stage → Nat) (lst : Stage → Nat) : List String :=
  match p.nums.stages, writtenOf p.nums with
  | a :: rest, some (_ :: l) => priceL rad lst tagS 0 a rest l
  | _, _ => [s!"{tagS}.PRICE\tno stage, or the declared rounds cannot be written"]

/-- At the greatest radii below a third; lists of one member. -/
def priceThird (tagS : String) (p : P12) : List String :=
  priceLines (tagS ++ ".third") p thirdB (fun _ => 1) ++
    [s!"{tagS}.third.PRICE.all\tTHE GREATEST k ≤ 128 WITH priceOk p k\t{priceBits p}\tpriceOk there {priceOk p (priceBits p)} · one more {priceOk p (priceBits p + 1)} (due false) · refusing one more: {((priceAll p (priceBits p + 1)).filter (!·.2)).map (·.1)}"]

end H2K.Pub
