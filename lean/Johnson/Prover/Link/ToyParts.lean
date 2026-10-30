-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ToyParts.lean: a test, behind Johnson/Prover/Link/ToyLink.lean: THE PROXIMITY
TEST's OWN PARTS (guardedProximityTestParts, Johnson/Desc/K12/JoinGuarded.lean) CALLED ONE BY ONE on the toy's honest
view, AND THE CLAIM THAT EACH HANDS ON HELD AGAINST THE PROVER's OWN TABLES.
Definitions with code and evaluations; no theorem. Made-up numbers alone.

What is held. Behind the batching, and behind each switch with its batching: the one row on the
group (Passing.claim), written out, at the stage's main and mask tables. Behind each fold: the claim
on three single rows (Passing.single), written out, at the main table folded at all drawn elements,
the carried mask table and the table of the new mask rows (the field P) folded at the first h.
The prover's tables of the later stages: Fmt.M1.Own.nextSt, as Fmt.M1.Own.go makes them.
THE LAST GROUP HAS ONE ROW VARIABLE THOUGH ITS STAGE HAS k = 0 (a group's layout has 1 ≤ k): its
main table is laid with a zero row beside the one row.

The tests (#guard). The place's numbers give thirteen declared rounds (cuts), as many as the walk
takes. Unbent: the walk comes to its end (no part refuses; that the states are six is fixed by
walk's own text); all five claims hold; so at the second set of draws. bend 1: the walk is refused
at the base case.

Limits: those of ToyLink.lean (among them: no drawn element is 0 or 1; the prover is
Fmt.M1.Own.go; #guard is run by Lean's evaluator, outside the kernel). The parts are called in the
frame's order by this file's own text (walk), not by the frame (proximityTestKind): that the two agree is seen
only in that the last state comes. No command here shows a claim that comes out false (some false):
at bend 1 the walk is refused, and claims gives [] there.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ToyLink

set_option autoImplicit false

namespace Johnson.Prover.Link.Toy
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15

def p12 : P12 :=
  ((numsOf tinyP).map (H2U.proximityTestParametersAt ⟨1, none, 6, .K12⟩)).getD (H2U.noP12 ⟨1, none, 6, .K12⟩)
def cuts : List Fmt.DeclaredRound := (H2U.roundsOfNums p12.nums).getD []
def st (j : Nat) : Fmt.M1.Stage := stagesT.getD j default
abbrev Gs := List (List (Nat × List UInt64))

section
variable (c : Cfg)

def rvs : List Fmt.RoundView := [(⟨[], dr [theta0]⟩ : Fmt.RoundView)] ++ testRounds c
def grp (i : Nat) : Gs := [((ownCols c).filter (·.1 == i)).map fun x => (x.2.1, x.2.2)]
def t0 : Except String T12 :=
  match frontRun c (ansOf c 0) (ansOf c 1) with
  | .ok (s, _, _) => enter s
  | .error e => .error e

/-- the states behind: the batching · fold 1 · switch 1 with its batching · fold 2 · switch 2 with
its batching · the base case -/
def walk : Except String (List T12) := do
  let X := guardedProximityTestParts
  let r := rvs c
  let a ← t0 c
  let a ← (X.front p12).decide a [] []
  let b ← (X.bat p12 (cuts.take 1)).decide a (r.take 1) []
  let c' ← (X.fold p12 0 (st 0) ((cuts.drop 1).take 4)).decide b ((r.drop 1).take 4) []
  let d ← (X.switch p12 0 (st 0) (st 1) false ((cuts.drop 5).take 2)).decide c' ((r.drop 5).take 2)
    (grp c 0)
  let d ← (X.batBehind p12 1 (st 1) ((cuts.drop 5).take 2)).decide d [] []
  let e ← (X.fold p12 1 (st 1) ((cuts.drop 7).take 2)).decide d ((r.drop 7).take 2) []
  let f ← (X.switch p12 1 (st 1) (st 2) true ((cuts.drop 9).take 2)).decide e ((r.drop 9).take 2)
    (grp c 1)
  let f ← (X.batBehind p12 2 (st 2) ((cuts.drop 9).take 2)).decide f [] []
  let g ← (X.base p12 2 (st 2) ((cuts.drop 11).take 2)).decide f ((r.drop 11).take 2) (grp c 2)
  pure [b, c', d, e, f, g]

def els (j : Nat) : X3 := (((vsT c).getD j default).els).getD 0 Fmt.Fld.zeroE
def g1 : List X3 := [els c 1, els c 2, els c 3]
def g2 : List X3 := [els c 7]
def p2 : Fmt.M1.Own.PSt := Fmt.M1.Own.nextSt fl coin 2 (st 0) (st 1) false (g1 c) (p1 c)
def p3 : Fmt.M1.Own.PSt := Fmt.M1.Own.nextSt fl coin 3 (st 1) (st 2) true (g2 c) (p2 c)

def dotA (c m : Array X3) : X3 := Fmt.M1.dot fl c m
/-- a claim on a group, at a stage's tables. bits: the main table's index bits -/
def holdsG (T : T12) (bits : Nat) (p : Fmt.M1.Own.PSt) (s : Fmt.M1.Stage) : Option Bool :=
  match T.pass with
  | .claim row _ =>
    some (decide (fl.addE (dotA ((row.c.writeOut bits).map (·.triple)) (Fmt.M1.Own.tabOf p.M s.C.l))
      (dotA (row.d.map (·.triple)) (Fmt.M1.Own.tabOf p.W s.Z.l)) = row.target.triple))
  | _ => none
/-- a claim on three single rows, at the folded tables -/
def holdsS (T : T12) (bits : Nat) (p : Fmt.M1.Own.PSt) (s : Fmt.M1.Stage) (g : List X3) :
    Option Bool :=
  match T.pass with
  | .single R _ =>
    let tr (a : Array E) : Array X3 := a.map (·.triple)
    some (decide (fl.addE (fl.addE
      (dotA (tr (R.c.writeOut bits)) (Fmt.M1.foldLow fl g (Fmt.M1.Own.tabOf p.M s.C.l)))
      (dotA (tr (R.d.getD 0 #[])) (Fmt.M1.foldLow fl (g.take s.h) (Fmt.M1.Own.tabOf p.W s.Z.l))))
      (dotA (tr (R.d.getD 1 #[])) (Fmt.M1.foldLow fl (g.take s.h) (Fmt.M1.Own.tabOf p.P s.Z.l))) =
        R.target.triple))
  | _ => none

/-- the five claims, in the walk's order -/
def claims : List (Option Bool) :=
  match walk c with
  | .ok [b, c', d, e, f, _] =>
    [holdsG b 5 (p1 c) (st 0), holdsS c' 2 (p1 c) (st 0) (g1 c), holdsG d 2 (p2 c) (st 1),
      holdsS e 1 (p2 c) (st 1) (g2 c),
      holdsG f 2 { p3 c with M := (p3 c).M ++ [zs 2] } (st 2)]
  | _ => []
def walkSays : String :=
  match walk c with
  | .ok l => s!"ok {l.length}"
  | .error e => e

end

#guard cuts.length == 13
#guard walkSays {} == "ok 6"
#guard claims {} == List.replicate 5 (some true)
#guard claims { alt := true } == List.replicate 5 (some true)
#guard walkSays { bend := 1 } == "the base case: the linear claim, or a symbol at a position"

end Johnson.Prover.Link.Toy
