-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.JohOk
/-
Johnson/Desc/K12/Law/RadNeed.lean: K12's CONDITION: A RADIUS FOR EACH STAGE AS A FUNCTION OF THE STAGE's OWN NUMBERS: the least radius at which the library's comparison for a round of positions (CsNum, OnBytes/Slice/ManyNum.lean) holds at k bits. DEFINITIONS WITH CODE ALONE; NO THEOREM; NO Mathlib BENEATH IT. NOTHING ON HIDING. **A TRANSCRIPTION: NO THEOREM READS THESE LINES; NO NUMBER HERE IS A BOUND ON THE RELEASE's SOUNDNESS: each figure is a share of ONE round's challenge values; W of the k bits are work; nothing is said of the counts of the rounds of one element (the library's bchksBound), which grow as a radius nears the Johnson radius.**
WHY. THE RADIUS IS A LETTER OF THE PROOF, NOT OF THE PROTOCOL: no program reads it: a verifier knows the codes, the numbers of positions t and the bits of work. A table of parameters has its radii reckoned outside Lean, by the plan's own rule, from an integer M that is no number of a place. So nobody need name «the plan's radius»: it is enough that SOME radius passes johOk (the facts on codes) and prices the rounds. THAT HOLDS OF EVERY PROGRAM AND OF THE RADII OF THE LATER STAGES; THE FIRST STAGE's RADIUS STANDS IN THE STATEMENT ITSELF: c.rad in «∀ w, ¬ RIn c.rad (q, y) w» and in rIn_rows | NoneNear: TO PICK IT IS TO PICK WHAT THE THEOREM SAYS OF THE COMMITTED WORD (within which distance a witness is sought; how long the list is): A CHOICE OF THE STATEMENT, TO BE NAMED WITH IT; NOT FREE FOR NOTHING. The smaller the radius, the smaller the counts on codes; the larger, the better the round of positions: so the least radius that prices the round of positions at k is the natural pick.
  needB W k lst a e     csNumB (H2K/PriceOk.lean) at the stage's a and t, at B := (t + 21) / 4 hash blocks (a code switch's second round draws t positions and one element: t + 18 words at most; the base case's second round has fewer blocks, so the comparison there is the easier) and a list of lst.
  radNeed W k lst a     the least e ≤ 2 ^ C.a with needB (2 ^ C.a if none): by halving: needB is rising in e: not shown.
  needLines             at r := radNeed p.nums.work k lst: johLines and priceLines at that r, and one line a stage: radNeed · johMax · is radNeed ≤ johMax.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)

def needB (W k lst : Nat) (a : Fmt.M1.Stage) (e : Nat) : Bool := csNumB lst W k a.C.a a.t ((a.t + 21) / 4) e

/-- The least e in (lo, hi] with f e, for f rising with f hi; by halving. -/
def firstYes (f : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then hi
    else if f ((lo + hi) / 2) then firstYes f fuel lo ((lo + hi) / 2) else firstYes f fuel ((lo + hi) / 2) hi

def radNeed (W k lst : Nat) (a : Fmt.M1.Stage) : Nat :=
  if needB W k lst a 0 then 0 else firstYes (needB W k lst a) 70 0 (2 ^ a.C.a)

def needLines (tagS : String) (p : P12) (k lst : Nat) : List String :=
  let r := radNeed p.nums.work k lst
  (p.nums.stages.zipIdx.map fun x =>
    let a := x.1
    s!"{tagS}.NEED.{x.2}\tk {k} · W {p.nums.work} · list {lst}\tthe least radius that prices a round of positions {r a} · there {needB p.nums.work k lst a (r a)} · one less {needB p.nums.work k lst a (r a - 1)} (due false)\tthe greatest radius below the Johnson radius {johMax a}\tROOM {decide (r a ≤ johMax a)}: {johMax a - r a} positions of {2 ^ a.C.a}\td {dB a} · d ≤ 2e {decide (dB a ≤ 2 * r a)}") ++
  johLines (tagS ++ ".need") p (fun a => r a) ++ priceLines (tagS ++ ".need") p (fun a => r a) (fun _ => lst)

end H2K.Pub
