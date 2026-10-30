-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SmallOk.lean: the field `small` of `K12Condition`
(Johnson/Desc/K12/Law/ChainHolds.lean) at the library's Johnson letters and the bound 2 ^ -128, as a
test that can run at a place of a proximity test (the kind K12), at radii and brackets that are
computed from the stage's own numbers. Definitions with code alone; no theorem; no Mathlib beneath.

No soundness of a release and no level of security is claimed. Each comparison bounds ONE round's
share of its written verifier messages, test bits among them. W of the 128 bits are work. There is
no sum over rounds. The round "BAT" stands in front of the chain and is not in it.

Sources. The test's clauses (`roundN`, `lastClB`, `stepClB`, `smallClB`, `smallAllB`, `smallOkB`)
are those of Johnson/Desc/K12/Law/SmallOfPlaces.lean,
typed here over the place's plain stage (`Fmt.M1.Stage`) in the place of `Sg`, so that no
Mathlib stands beneath. By its own head that file was written with six files of Johnson/Bridge/
open. `cntLeB` is `CntLe` of Cb/Ref/CntLe.lean, its ten comparisons term for term. `nValsB` is
`nVals` (OnBytes/Slice/Rates.lean); `clashB` is `clashSeeds` (OnBytes/Params/RecordPrice.lean);
`listMaxB` is `listMax` (Cb/Gen/JohnsonList.lean). The computing of a bracket (`brOf`) was written
from the text of `CntLe` alone: no list of brackets was read.
`roundN` and `brN` are that file's `roundB` and `brB` under other names, so that the two files can
be imported together (Johnson/Desc/K12/Law/SmallCut.lean).
Main names:
  `cntLeB n k e m a b D N`: ten comparisons of natural numbers. Their yes gives ⌊bchksBound n k e⌋ ≤
    N (the library's `floor_le_of_cntLe`).
  `brOf n k e`: a bracket by computing, at D = 2 ^ 64. a: the greatest with a² n ≤ k D². b: a + 1.
    m: the least, at least 3, with b n ≤ m (D n − b n − e D). N: the least with the tenth
    comparison. (0, 0, 0, 0) where D n ≤ b n + e D: no bracket: the radius is too near √(k/n).
  `roundN w count`: one written round and a count: the entry's own numbers and one comparison.
  `smallOkB rad B p`: the test.
  `brAt rad a`: the two brackets of a stage at its radius: at the main code's k, and at that of the
    Reed–Solomon code in which the repeated mask code lies.
  `smallLines tag p`: at rad := `radNeed p.nums.work 128 (2 ^ 58)`
    (Johnson/Desc/K12/Law/RadNeed.lean) and B := `brAt rad`: a line a stage, a last line, and teeth.
  `fourLines tag p K`, `fourLinesAt tag p K rad`: `pubOk`, `spendOk`, `johOk` and `smallOkB` at one
    radius on one line (K: the record's codes), and the tooth at the radius 2 ^ C.a: the test alone
    is no sign of a sound radius.
That the clauses typed here are that file's test is a lemma: `smallOk_eq`
(Johnson/Desc/K12/Law/SmallCut.lean). With it `k12Condition_native`: the four Booleans' yes gives
`K12Condition`.
Limits: as said above. rad and B are letters of `smallOkB`. That `radNeed` and `brOf` find the least
or the greatest number that their heads name is not shown; the test is asked at what they find.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.RadNeed
import Fmt.M1Dec
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)

def cntLeB (n k e m a b D N : Nat) : Bool :=
  decide (0 < n) && decide (0 < k) && decide (0 < a) && decide (0 < D) &&
      decide (a ^ 2 * n ≤ k * D ^ 2) &&
    decide (k * D ^ 2 ≤ b ^ 2 * n) && decide (b * n + e * D < D * n) &&
    decide (b * n + m * (b * n + e * D) ≤ m * (D * n)) && decide (3 ≤ m) &&
    decide (D * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1)) ≤ 48 * k * a * N)

structure BrN where
  m : Nat
  a : Nat
  b : Nat
  N : Nat
  deriving Repr

def BrN.ok (w : BrN) (n k e : Nat) : Bool := cntLeB n k e w.m w.a w.b (2 ^ 64) w.N

def brOf (n k e : Nat) : BrN :=
  let D := 2 ^ 64
  let a := lastYes (fun a => decide (a ^ 2 * n ≤ k * D ^ 2)) 70 0 (D + 1)
  let b := a + 1
  if D * n ≤ b * n + e * D then ⟨0, 0, 0, 0⟩
  else
    let gap := D * n - b * n - e * D
    let m := max 3 ((b * n + gap - 1) / gap)
    let num := D * ((2 * m + 1) ^ 5 * n ^ 2 + 24 * (2 * m + 1) * k * (e + 1))
    let den := 48 * k * a
    ⟨m, a, b, if den = 0 then 0 else (num + den - 1) / den⟩

def nValsB : List Fmt.Draw → Nat
  | [] => 1
  | .elem :: ds => Fmt.Fld.two.p ^ 3 * nValsB ds
  | .elemNZ :: ds => (Fmt.Fld.two.p ^ 3 - 1) * nValsB ds
  | .pos k :: ds => 2 ^ k * nValsB ds
  | .trits n :: ds => 4 ^ n * nValsB ds
  | .sealed :: ds => (2 ^ 64) ^ 4 * nValsB ds

def clashB (q lg : Nat) : Nat := max (lg * q ^ (lg - 1) * (q - 1)) (q ^ lg)

def listMaxB (n d e : Nat) : Nat := n * (d - e) / ((n - e) ^ 2 - n * (n - d))

def choose2 (n : Nat) : Nat := n * (n - 1) / 2

def roundN (w : WR) (count : Nat) : Bool :=
  decide (w.entry.logN ≤ 64) && decide (w.entry.drawNZ ≤ w.entry.drawE) &&
    (decide (w.entry.drawE = 0) || decide (w.entry.work + 66 ≤ 128)) &&
    decide (0 < nValsB (Fmt.dsOf w.entry w.kind)) &&
    decide (count * 2 ^ 193 + 3 * (w.entry.drawE + w.entry.drawNZ) * nValsB
        (Fmt.dsOf w.entry w.kind) ≤
      nValsB (Fmt.dsOf w.entry w.kind) * 2 ^ (w.entry.work + 65))

def kCB (a : Fmt.M1.Stage) : Nat := a.C.r + a.C.l - 1
def kZB (a : Fmt.M1.Stage) : Nat := 2 ^ (a.C.a - a.Z.a) * (a.Z.r + a.Z.l - 1)
def dZB (a : Fmt.M1.Stage) : Nat := 2 ^ (a.C.a - a.Z.a) * (2 ^ a.Z.a - (a.Z.r + a.Z.l) + 1)
def lstJB (a : Fmt.M1.Stage) (e : Nat) : Nat := listMaxB (2 ^ a.C.a) (dB a) e

def brN (a : Fmt.M1.Stage) (e : Nat) (b : BrN × BrN) : Bool :=
  b.1.ok (2 ^ a.C.a) (kCB a) e && b.2.ok (2 ^ a.C.a) (kZB a) e

def bZofB (a : Fmt.M1.Stage) (e : Nat) (b : BrN × BrN) : Nat :=
    b.2.N + listMaxB (2 ^ a.C.a) (dZB a) e

def lastClB (a : Fmt.M1.Stage) (e : Nat) (b : BrN × BrN) (dL dB' : WR) : Clauses :=
  [("small.brackets", brN a e b), ("small.lambda", roundN dL (b.1.N + bZofB a e b + lstJB a e)),
   ("small.base", roundN dB' ((2 ^ a.C.a - e - 1) ^ a.t))]

def stepClB (a a' : Fmt.M1.Stage) (e e' : Nat) (b : BrN × BrN) (dE dT dS dC : WR) : Clauses :=
  [("small.brackets", brN a e b), ("small.eps", roundN dE (lstJB a e)),
   ("small.two", roundN dT (b.1.N + lstJB a e * 2)),
   ("small.two with mask rows",
     decide (a.h = 0) || roundN dT (b.1.N + (bZofB a e b + bZofB a e b) + lstJB a e * 2)),
   ("small.seed", roundN dS (choose2 (lstJB a' e') * clashB (Fmt.Fld.two.p ^ 3) (stN a').na)),
   ("small.cs", roundN dC ((2 ^ a.C.a - e - 1) ^ a.t * Fmt.Fld.two.p ^ 3 +
     (2 ^ a.C.a) ^ a.t * (lstJB a' e' * (1 + 3 * a.t))))]

def smallClB (rad : Fmt.M1.Stage → Nat) (B : Fmt.M1.Stage → BrN × BrN) :
    Nat → Fmt.M1.Stage → List Fmt.M1.Stage → List WR → Clauses
  | j, a, [], l =>
    match l with
    | [dL, dB'] => tag j (lastClB a (rad (stN a)) (B (stN a)) dL dB')
    | _ => [(toString j ++ ":cut at the last stage", false)]
  | j, a, b :: rest, l =>
    match l with
    | dE :: dT :: l' =>
      match (dT :: l').drop (kk a) with
      | dS :: dC :: l'' =>
        tag j (stepClB a b (rad (stN a)) (rad (stN b)) (B (stN a)) dE dT dS dC) ++
          smallClB rad B (j + 1) b rest l''
      | _ => [(toString j ++ ":cut: no two rounds behind the fold's", false)]
    | _ => [(toString j ++ ":cut: no two rounds of a fold", false)]

def smallAllB (rad : Fmt.M1.Stage → Nat) (B : Fmt.M1.Stage → BrN × BrN)
    (N : H2U.TestNums) : Clauses :=
  match N.stages, writtenOf N with
  | a :: rest, some (_ :: l) => smallClB rad B 0 a rest l
  | _, _ => [("no stage, or the declared rounds cannot be written", false)]

/-- The test. -/
def smallOkB (rad : Fmt.M1.Stage → Nat) (B : Fmt.M1.Stage → BrN × BrN) (p : P12) : Bool :=
  ok (smallAllB rad B p.nums)

def smallNoB (rad : Fmt.M1.Stage → Nat) (B : Fmt.M1.Stage → BrN × BrN) (p : P12) : List String :=
  ((smallAllB rad B p.nums).filter (!·.2)).map (·.1)

/-- The two brackets of a stage at its radius, by computing. -/
def brAt (rad : Fmt.M1.Stage → Nat) (a : Fmt.M1.Stage) : BrN × BrN :=
  (brOf (2 ^ a.C.a) (kCB a) (rad a), brOf (2 ^ a.C.a) (kZB a) (rad a))

def lessN (b : BrN × BrN) : BrN × BrN := ({ b.1 with N := b.1.N - 1 }, b.2)

def smallLinesAt (tagS : String) (p : P12) (rad : Fmt.M1.Stage → Nat) : List String :=
  let B := brAt rad
  (p.nums.stages.zipIdx.map fun x =>
    let a := stN x.1
    let e := rad a
    let b := B a
    s!"{tagS}.SMALL.{x.2}\tn {2 ^ a.C.a} · radius {e} · the Johnson bound on the list \
        {lstJB a e}\tmain bracket m {b.1.m} · N < 2^{b.1.N.log2 + 1} · ok \
        {b.1.ok (2 ^ a.C.a) (kCB a) e} · N − 1 \
        {({ b.1 with N := b.1.N - 1 } : BrN).ok (2 ^ a.C.a) (kCB a) e} (due false)\tmask bracket m \
        {b.2.m} · N < 2^{b.2.N.log2 + 1} · ok {b.2.ok (2 ^ a.C.a) (kZB a) e} · N − 1 \
        {({ b.2 with N := b.2.N - 1 } : BrN).ok (2 ^ a.C.a) (kZB a) e} (due false)") ++
  [s!"{tagS}.SMALL.all\tsmallOk {smallOkB rad B p}\tclauses \
      {(smallAllB rad B p.nums).length}\trefusing: {smallNoB rad B p}",
   s!"{tagS}.SMALL.teeth\tevery radius one less \
       {smallOkB (fun a => rad a - 1) (brAt fun a => rad a - 1) p} (refusing \
       {(smallNoB (fun a => rad a - 1) (brAt fun a => rad a - 1) p).take 3}; DUE false AT THE \
       LEAST RADIUS radNeed ALONE: elsewhere one less may still lie in the window) · EACH OF THE \
       NEXT THREE DUE false: every main bracket's N one less \
       {smallOkB rad (fun a => lessN (B a)) p} · the radius 0 \
       {smallOkB (fun _ => 0) (brAt fun _ => 0) p} · the greatest radius below the Johnson radius \
       {smallOkB johMax (brAt johMax) p} (refusing {(smallNoB johMax (brAt johMax) p).take 3})",
   s!"{tagS}.SMALL.four\tAT ONE RADIUS: johOk {johOk p rad} · smallOk {smallOkB rad B p}"]

def smallLines (tagS : String) (p : P12) : List String :=
  smallLinesAt (tagS ++ ".need") p (radNeed p.nums.work 128 (2 ^ 58))

/-- The positions' clauses of the test alone. -/
def posCl (rad : Fmt.M1.Stage → Nat) (p : P12) : Clauses :=
  (smallAllB rad (brAt rad) p.nums).filter fun x => x.1.endsWith "small.cs" ||
      x.1.endsWith "small.base"

/-- The four Booleans of the condition at one radius, on one line; and the tooth at the radius 2 ^
C.a: there «2 ^ C.a − e − 1» is cut off, the positions' counts are 0 and the test's clauses on
positions are free: `johOk` must refuse. K: the record's codes. -/
def fourLinesAt (tagS : String) (p : P12) (K : Codes) (rad : Fmt.M1.Stage → Nat) : List String :=
  [s!"{tagS}.FOUR\tAT ONE RADIUS: pubOk {pubOk p K} · spendOk {spendOk p} · johOk {johOk p rad} · \
      smallOk {smallOkB rad (brAt rad) p}\tALL FOUR \
      {pubOk p K && spendOk p && johOk p rad && smallOkB rad (brAt rad) p}\tthe radii \
      {p.nums.stages.map fun a => rad (stN a)}\tWHAT STANDS BEHIND IT: pubOk · spendOk · johOk: \
      Booleans with theorems; smallOk: the clauses of SmallOfPlaces.lean's test without Mathlib \
      beneath, by the lemma smallOk_eq (SmallCut.lean) · each comparison: ONE ROUND's SHARE · W OF \
      THE 128 BITS ARE WORK · NO SUM OVER ROUNDS · \"BAT\" NOT IN IT · NO LEVEL OF SECURITY \
      IS CLAIMED",
   s!"{tagS}.FOUR.tooth\tat the radius 2 ^ C.a: the gate's positions' clauses \
       {ok (posCl (fun a => 2 ^ a.C.a) p)} (free there: due true) · johOk \
       {johOk p fun a => 2 ^ a.C.a} (due false) · smallOk \
       {smallOkB (fun a => 2 ^ a.C.a) (brAt fun a => 2 ^ a.C.a) p} (due false: no bracket)"]

def fourLines (tagS : String) (p : P12) (K : Codes) : List String :=
  fourLinesAt (tagS ++ ".need") p K (radNeed p.nums.work 128 (2 ^ 58))

end H2K.Pub
