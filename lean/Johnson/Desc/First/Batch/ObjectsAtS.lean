-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ObjectsAtS.lean: the step that adds the smallness test's claims
(Johnson/Desc/First/Batch/Objects.lean) at the state that the proof file's first chain carries
(Johnson/Desc/First/State.lean: S). Definitions with code; no theorem.

THE PARAMETERS ARE OTHER FILES' TEXTS, BY NAME:
  THE ORDER: the second stretch of the driver's one table (Johnson/Desc/First/Driver/Chain.lean:
    orderCuts), each entry looked up by name (`runsBy`);
  the lookup on the digits' own claims: K3's block at the digits, its runs "objects" and "guests"
    (Johnson/Desc/First/Look/K3Own.lean: theOwn, with runs);
  between them K9's OWN ONE LINE: K3's list is as long as the lookup has equations of its own
    (`digitsRowsCounted`);
  the smallness test's equations: `First.TailClaims.equations`
    (Johnson/Desc/First/TailClaims/Equations.lean), handed the ledger's count and the number
    gathered;
  behind the adding: the coefficients on the smallness test's own slots are read off the ledger
    (ONE LINE, TYPED HERE AFTER TWO SOURCES: Tail.lean:1094 of the program `verify-on-bytes`, and
    the smallness test's own run "K8.lsTail", whose file is not imported here);
  at a layers' segment two counts of the layers' own stand in front (Layer.lean:620-621).
Limits: definitions; no law is stated here. The parameters are other files' texts, taken by name;
one line (the coefficients on the smallness test's own slots) is typed after `verify-on-bytes`'s.
Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Objects
import Johnson.Desc.First.Batch.TestsAtS
import Johnson.Desc.First.Look.K3Own
import Johnson.Desc.First.TailClaims.Equations
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- K8's equations at S. -/
def k8Equations : RunOf S :=
  ("K8.equations", fun front s => do
    let F ← there "K9.in-a-segment" s.fork?
    let tl ← there "K9.in-a-segment" s.tl?
    let funs ← there "K9.in-a-segment" s.funs?
    let x ← First.TailClaims.equations (F.nClaim + front) tl funs F
    pure (x.2.2, (s.putTl x.1).putFork x.2.1))

/-- Behind the adding. -/
def k8LsTailAtS (s : S) : Except String S := do
  let F ← there "K9.in-a-segment" s.fork?
  let tl ← there "K9.in-a-segment" s.tl?
  pure (s.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB })

/-- The sort of a segment in the driver's words. -/
def subOf : SegSort → First.ModelPart
  | .layers => .layers
  | .attention => .attention
  | .head => .head

/-- A stretch of the driver's table of the order, at a sort of segment. -/
def cutAt (k : SegSort) (n : Nat) : List (Nat × String) := ((First.orderCuts (subOf k))[n]?).getD []

/-- **The smallness test's window of slots**, off its record in S: THE SAME AT EVERY STEP OF THE
SEGMENT. ITS OWNERS ARE THE SECOND STRETCH OF THE ORDER (the lookup on the digits' two runs and K8's
equations, by the word of those who keep the smallness test's texts): no other table. -/
def k8Window (k : SegSort) (s : S) : List Window :=
  (s.tl?.map fun tl => [(⟨cutAt k 1, tl.slotA, tl.slotB⟩ : Window)]).getD []

/-- **What block number b of segment i states**, as far as it is K3's or K8's: by the kind that the
driver has at b (`First.kindsBeforeBatching`): K3: its own block at that piece (the calls' or the digits'),
its runs; K8: the equations. Other kinds: nothing here: their own files add theirs. -/
def statesK3K8 (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (k : SegSort) (b : Nat) : List (RunOf S) :=
  match (First.kindsBeforeBatching (subOf k) (i == 0))[b]? with
  | some .K3 =>
    ((K3.theOwn (Cl := Claim) (fun a => { form := a }) true X codes shape
      ⟨1, some i, b + 1, .K3⟩).map fun x => x.claims).getD []
  | some .K8 => [k8Equations]
  | _ => []

/-- THE COUNT THAT THE ADDING STEP ALONE CAN ASK (a debt that the smallness test's text names;
`verify-on-bytes`'s Tail.lean:1053): the lookup on the digits has laid as many claims as it has
equations of its own
(`First.TailClaims.lookRows`). It stands right behind K3's "objects": the number that it is handed
is that list's length. It lays no claim. -/
def digitsRowsCounted : RunOf S :=
  ("K9.digits-rows", fun front s => do
    let tl ← there "K9.in-a-segment" s.tl?
    need "K9.lookup-rows-counted" (front == First.TailClaims.lookRows tl)
    pure ([], s))

/-- The runs of the step: THE SECOND STRETCH OF THE DRIVER's TABLE OF THE ORDER, by name (K3's
"objects" · "guests" at the digits · "K8.equations"), with K9's own count right behind "objects". -/
def objectsRuns (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (k : SegSort) : Option (List (RunOf S)) :=
  (runsBy (statesK3K8 X codes shape i k) (cutAt k 1)).bind
    (behindRun "objects" digitsRowsCounted)

/-- The layers' own two counts in front of the step. -/
def objectsCounts (k : SegSort) : List (String × (S → Bool)) :=
  match k with
  | .layers =>
    [("K9.matrix-drawn-once", fun s => (s.tl?.map (·.foldDrawn == 1)).getD false),
     ("K9.two-lookups", fun s => (s.tl?.map (1 + ·.groupsRun == 2)).getD false)]
  | _ => []

/-- **The block at segment i.** withK3: the lookup on the digits' own claims come of K3's runs, in
front of K8's equations; else K8's equations stand alone. -/
def objectsAt {Cl : Type} (withK3 : Bool) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (i piece : Nat) : Option (Block S Cl) :=
  (testsWhere X i piece).bind fun w =>
    (if withK3 then objectsRuns X codes shape i w.1 else some [k8Equations]).map
      fun runs =>
        addsStep atS ⟨1, i, piece, piece, 0, 0, 0⟩ "the smallness test's" (objectsCounts w.1)
          (k8Window w.1) (cutAt w.1 1) runs k8LsTailAtS

end VerifiableInference.Desc.K9
