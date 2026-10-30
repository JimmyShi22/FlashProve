-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3Written.lean: THE LOT OF THE KIND "LOOKUP": THE WRITTEN VALUES OF WHAT
ITS FIFTY SUB-PROTOCOLS' SKELETONS READ AT THE FULL SIZE. Definitions with code alone; the closed
facts on them stand in K3NumC.lean, K3NumD.lean and K3Table.lean. The values were printed by a run
of the lot's own text at the goals' term of public files VerifierAndGoals.storedPublicFiles (a harness, not shown
here) and are typed after that print. A place's numbers hang on
the segment's sort alone: 0: segment 0 · 1: attention · 2: the other layers' · 3: the output head's.
  `sortOf`, `nameW`, `pieceW`, `callsW` (THE CALLS WITHOUT THEIR TABLES), `pubW`, `firstW`, `nsW`,
    `lmW`, `nW` (the number of rounds), `quietW`, `callerW`.
  `coreW s d`: the lookup's parameters at these values, name and link left out. `numOf p laid`: what
    a skeleton reads of the parameters beside name and link: the number of rounds and the plan's
    tests.
  `beforeW i d`: the column "before" OF THE WRITTEN TABLE OF THE FIRST CHAIN ITSELF (cutFirstFull,
    Johnson/Desc/Ok/PlanWritten/CutLit.lean) at the lookup's place: no literal of this file's.
  `rowW i d`, `k3RowsW`: the fifty written skeletons.
Limits. Written values: nothing says here that any public files have them. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Strip
import Johnson.Desc.Ok.PlanWritten.CutLit
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Look (P)
open ProofFile.Sk (Skel)

/-- The segment's sort. -/
def sortOf (i : Nat) : Nat :=
  if i == 24 then 3 else if i % 2 == 1 then 1 else if i == 0 then 0 else 2

def wordOf : Nat → String
  | 1 => "attention"
  | 3 => "head"
  | _ => "layers"

def nameW (i : Nat) (d : Bool) : String :=
  "LINK " ++ toString i ++ " (" ++ wordOf (sortOf i) ++ ") " ++ (if d then "digits" else "calls")

def pieceW (i : Nat) (d : Bool) : Nat :=
  if i == 24 then (if d then 8 else 3) else (if d then 7 else 2)

/-- A call without a table. -/
def cl (name : String) (n iota k fn t0 : Nat) (pub : Array Nat := #[]) : Call :=
  { name := name, n := n, iota := iota, k := k, kappa := 5, fn := fn, t0 := t0, tau := none,
    pub := pub, heavy := [] }

def padW : Nat → Nat
  | 1 => 5242880
  | 3 => 17825792
  | _ => 3145728

def layCalls : Array Call :=
  #[cl "R16a" 27 1 16 0 0, cl "R16b" 27 1 16 0 0, cl "R16c" 27 1 16 0 0, cl "R8" 28 2 8 0 0,
    cl "FC" 27 1 16 1 32768, cl "FS" 27 1 16 1 32768, cl "FL" 26 0 16 1 32768,
    cl "R16d" 26 0 16 0 0]

/-- **The calls, their tables taken out.** -/
def callsW (s : Nat) : Bool → Array Call
  | true => #[cl "R10z" (if s == 1 then 25 else 26) 0 10 0 0 #[padW s],
      cl "R8d" (if s == 1 then 25 else 26) 0 8 0 0 #[padW s]]
  | false =>
    match s with
    | 1 => #[cl "KR" 27 2 16 2 0, cl "KFD" 27 2 16 1 2307, cl "R16" 26 1 16 0 0,
        cl "WH" 25 0 16 2 0]
    | 3 => #[cl "R16a" 28 1 16 0 0, cl "R16b" 28 1 16 0 0, cl "R8" 28 1 8 0 0, cl "FEa" 27 0 16 1 0,
        cl "FEb" 27 0 16 1 0, cl "FC" 27 0 16 1 32768]
    | _ => layCalls

/-- The numbers of padding keys, tree by tree; the host's count is the same list. -/
def pubW (s : Nat) : Bool → Array Nat
  | true => #[padW s, padW s]
  | false =>
    match s with
    | 1 => #[0, 0, 6291456, 33554432, 0, 0, 6291456, 33554432, 0, 25001984, 12582912]
    | 3 => #[0, 51052544, 0, 61538304, 0, 61415424, 0, 61538304, 128974848]
    | _ => #[5040128, 4646912, 5040128, 4646912, 0, 0, 2097152, 2097152, 36306944, 36306944,
        31326208, 31326208, 33553408, 33553408, 0, 0]

def firstW (s : Nat) : Bool → Nat
  | false => 0
  | true => match s with
    | 0 => 2696
    | 1 => 2884
    | 2 => 2695
    | _ => 2168

def nsW : Nat → Nat
  | 0 => 4059
  | 1 => 4190
  | 2 => 4058
  | _ => 3570

def lmW (s : Nat) : Bool → Nat
  | true => 5
  | false => match s with
    | 1 => 14
    | 3 => 15
    | _ => 16

/-- The number of rounds. -/
def nW (s : Nat) : Bool → Nat
  | true => if s == 1 then 716 else 746
  | false => match s with
    | 1 => 984
    | 3 => 1080
    | _ => 1046

/-- Whether a step without a round stands behind the lookup. -/
def quietW (i : Nat) (d : Bool) : Bool := d || (sortOf i == 0 || sortOf i == 2)

/-- Whether the calling kind's readers are there. -/
def callerW (i : Nat) : Bool := sortOf i == 1 || sortOf i == 3

def setW : Params.Setting := Params.settingOf Params.recordLines

/-- **The parameters at the written values**, name and link left out. -/
def coreW (s : Nat) (d : Bool) : P :=
  { name := "", set := setW, link := 0, digits := false, calls := callsW s d, pub := pubW s d,
    lid := 28, first := firstW s d, ns := nsW s, lm := lmW s d }

/-- What a skeleton reads of the parameters beside name and link. -/
def numOf (p : P) (laid : Array Nat) : Nat × Bool :=
  (p.rounds.length, K3.planOk (S := First.S) (Cl := Claim) p laid [] && K3.Law.fitsVia p)

/-- The written table's row at the lookup's place. -/
def tableAt (i : Nat) (d : Bool) :=
  VerifiableInference.PlanWritten.cutFirstFull.find? fun r =>
    r.2.1 == (⟨1, some i, pieceW i d, .K3⟩ : VerifiableInference.Desc.Place)

/-- **The written table's own column "before".** -/
def beforeW (i : Nat) (d : Bool) : List (Nat × Nat) := ((tableAt i d).map (·.2.2.2.2.2)).getD []

/-- **The written skeleton at segment i.** -/
def rowW (i : Nat) (d : Bool) : Skel :=
  dress (quietW i d) (!d && callerW i) i (pieceW i d)
    { name := nameW i d, place := ⟨1, some i, pieceW i d, .K3⟩, nRounds := nW (sortOf i) d
      nOracles := nW (sortOf i) d, told := [], before := beforeW i d, planOk := true
      claims := ["objects", "guests"], after := [] }

/-- **THE FIFTY.** -/
def k3RowsW : List Skel := (List.range 25).flatMap fun i => [false, true].map fun d => rowW i d

end Johnson.AtFull.Lots.K3
