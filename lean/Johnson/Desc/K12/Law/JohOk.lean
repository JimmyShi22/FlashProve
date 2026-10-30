-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.PriceOk
/-
Johnson/Desc/K12/Law/JohOk.lean: K12's CONDITION AT RADII BELOW THE JOHNSON RADIUS: the library's condition on a stage and its radius (Sg.StageJ, OnBytes/Slice/ManyHoldsJoh.lean) AS A TEST ON WHOLE NUMBERS THAT CAN RUN AT A PLACE. DEFINITIONS WITH CODE ALONE; NO THEOREM; NO Mathlib BENEATH IT. NOTHING ON HIDING. NO SOUNDNESS IS CLAIMED.
The nine comparisons are those of stageJB (Johnson/Desc/K12/RadiusLaws.lean: neither the name nor the file is in this library), typed again over the place's plain stage so that no Mathlib stands beneath; tied to Sg.StageJ in Johnson/Desc/K12/Law/ChainJoh.lean.
  stageJL a e       the sizes in order (four) · each code has at least two coefficients (two) · 0 < e · e < d · below the Johnson radius, without a square root: n (n − d) < (n − e) ^ 2, with n = 2 ^ C.a and d the stage's distance (dB, Johnson/Desc/K12/Law/PriceOk.lean).
  johAll | johOk p rad | johNo      at every stage of the place, at a radius for each stage THAT IS HANDED IN: WHICH RADIUS A PLAN MEANS AT A STAGE IS NOT SAID HERE.
  johMax a          the greatest radius at which the stage's test says yes (0 if none): by halving from 1 on: from 1 on the test is falling in e (joh.below and joh.johnson fall; joh.rad rises at 0 alone; the others do not read e): not shown here; each printed line tries one above, 0 and d. IT IS NOT THE PLAN's RADIUS.
  johLines          one line a stage: n · d · the radius · each comparison's word · is twice the radius at least the distance · johMax.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)

def stageJL (a : Fmt.M1.Stage) (e : Nat) : Clauses :=
  [("joh.small", decide (a.C.a ≤ 32)), ("joh.short", decide (a.Z.a ≤ a.C.a)),
   ("joh.roomC", decide (a.C.r + a.C.l ≤ 2 ^ a.C.a)), ("joh.roomZ", decide (a.Z.r + a.Z.l ≤ 2 ^ a.Z.a)),
   ("joh.twoC", decide (0 < a.C.r + a.C.l - 1)), ("joh.twoZ", decide (0 < a.Z.r + a.Z.l - 1)),
   ("joh.rad", decide (0 < e)), ("joh.below", decide (e < dB a)),
   ("joh.johnson", decide (2 ^ a.C.a * (2 ^ a.C.a - dB a) < (2 ^ a.C.a - e) ^ 2))]

def johWalk (rad : Fmt.M1.Stage → Nat) : Nat → List Fmt.M1.Stage → Clauses
  | _, [] => []
  | j, a :: rest => tag j (stageJL a (rad (stN a))) ++ johWalk rad (j + 1) rest

def johAll (p : P12) (rad : Fmt.M1.Stage → Nat) : Clauses := johWalk rad 0 p.nums.stages


def johOk (p : P12) (rad : Fmt.M1.Stage → Nat) : Bool := ok (johAll p rad)

def johNo (p : P12) (rad : Fmt.M1.Stage → Nat) : List String := ((johAll p rad).filter (!·.2)).map (·.1)

/-- The greatest e in [lo, hi) with f e, for f falling; by halving. fuel: at least the bits of hi. -/
def lastYes (f : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else if f ((lo + hi) / 2) then lastYes f fuel ((lo + hi) / 2) hi else lastYes f fuel lo ((lo + hi) / 2)

def johMax (a : Fmt.M1.Stage) : Nat :=
  if ok (stageJL a 1) then lastYes (fun e => ok (stageJL a e)) 70 1 (dB a) else 0

def johLines (tagS : String) (p : P12) (rad : Fmt.M1.Stage → Nat) : List String :=
  (p.nums.stages.zipIdx.map fun x =>
    let a := x.1
    let e := rad (stN a)
    s!"{tagS}.JOH.{x.2}\tn {2 ^ a.C.a} · d {dB a} · radius {e}\tyes {ok (stageJL a e)} · refusing {((stageJL a e).filter (!·.2)).map (·.1)}\td ≤ 2e {decide (dB a ≤ 2 * e)}\tthe greatest radius with a yes {johMax a} · there {ok (stageJL a (johMax a))} · one more {ok (stageJL a (johMax a + 1))} (due false) · at 0 {ok (stageJL a 0)} (due false) · at d {ok (stageJL a (dB a))} (due false)") ++
  [s!"{tagS}.JOH.all\tjohOk {johOk p rad}\tclauses {(johAll p rad).length}\trefusing: {johNo p rad}"]

/-- At the greatest radii with a yes. -/
def johTop (tagS : String) (p : P12) : List String := johLines (tagS ++ ".top") p johMax

end H2K.Pub
