-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/Ops.lean: what a lookup's hearing does to the shape of the
ledger, as code: a list of steps, made of the lookup's public numbers alone, and the function that
runs them on the shape. Definitions; one small theorem.

Terms. Honest/K3/GLOSSARY.md: see there ledger, slot, hearing, sumcheck, face and shape (of the
ledger). In this file: the shape of the ledger (`LedSh`, `ledSh`:
Johnson/Desc/First/Shape/Parts.lean) holds no field element: counts, sizes,
marks.

What is defined. The verifier's hearing of a lookup (`hearV`,
Johnson/Desc/First/Look/Via/Rounds.lean) touches the ledger in three ways:
  `Op.sum own ends`: a masked sumcheck with end values, its row made at once: the count of slots
    goes on by own + ends; the end values' slots are filled (at the hearing), then its own (at the
    row).
  `Op.left own`: a masked sumcheck without end values, left open: the count goes on by own; no slot
    is filled.
  `Op.owe`: a claim more on the list of owed claims, not marked as added.
  `runOps l L`: the steps of l, one after the other, on the shape L (`runOps_append`: of two lists
    in a row).
  `lookOps f`: the steps of a lookup at the face f, in the order of its rounds.
  `lookUpd f L`: these steps run on L.
Helpers: `setNext`, `Op.on`, `sumOp`, `levelOp`, `levelOps`, `tieOps`, `partsOps`, `keysOps`.
How many slots of its own a sumcheck has is the library's `ownSlots`
(Johnson/Desc/Part/MaskedSum4.lean) of its list of variables. That number depends on the variables'
degrees alone; here the lists are made at stand-in points.

Users. Honest/K3/Shape/Atoms.lean, Honest/K3/Shape/Closed.lean and
Honest/K3/Shape/HeardOps.lean import this file.

Limits. `lookUpd` is a fold of steps and no closed form. That the hearing does just this to the
ledger's shape is shown in Honest/K3/Shape/Walk.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Shape.Parts
import Johnson.Desc.First.Look.Via.Rounds
import Johnson.Desc.Part.MaskedSumReady

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.First.Shape (LedSh fillB)
open VerifiableInference.Desc.Part (MaskedSum.Call MaskedSum.ownSlots)
open VerifiableInference.Desc.First.ProdV (levelVars levelEnds)
open VerifiableInference.Desc.K3 (Face noVar leafVars bitsCall)

/-- The shape with another count of slots. -/
def setNext (L : LedSh) (n : Nat) : LedSh :=
  LedSh.mk L.ns L.shown L.factors L.got L.owed L.planClaims L.trees n L.coefs L.claims L.drawn
    L.handed L.shut

/-- A step of a hearing on the ledger's shape. -/
inductive Op where
  /-- A masked sumcheck with end values, its row made at once -/
  | sum (own ends : Nat)
  /-- A masked sumcheck without end values, left open -/
  | left (own : Nat)
  /-- A claim more is owed -/
  | owe
  deriving Repr, DecidableEq

/-- What a step does to the shape. Kin in the library, not tied here: `H2K5.Honest.ledStep`
(Johnson/Desc/K5/Honest/Law/ShapeK5.lean) fills n slots from the next free number on and moves that
number by n, as the arm at `.sum` does in two stretches. -/
def Op.on : Op → LedSh → LedSh
  | .sum o e, L =>
    ((setNext L (L.next + o + e)).setGot (fillB L.got (L.next + o) e)).setGot
      (fillB (fillB L.got (L.next + o) e) L.next o)
  | .left o, L => setNext L (L.next + o)
  | .owe, L => L.setOwed (L.owed ++ [false])

/-- The steps, one after the other. -/
def runOps (l : List Op) (L : LedSh) : LedSh := l.foldl (fun L o => o.on L) L

theorem runOps_append (a b : List Op) (L : LedSh) : runOps (a ++ b) L = runOps b (runOps a L) :=
  List.foldl_append ..

/-- The step of a masked sumcheck with end values at a call. -/
def sumOp (k : MaskedSum.Call) : Op := .sum (MaskedSum.ownSlots k.all) k.endsN

/-- The step of one level of a product tree; order: which bit each round fixes. -/
def levelOp (order : List Nat) : Op :=
  sumOp { lead := 0, vs := levelVars 0 #[] order, ends := some levelEnds }

/-- A run of levels: one for each number i of the list l, with the order of level m0 + i. -/
def levelOps (m0 : Nat) (orders : Nat → List Nat) (l : List Nat) : List Op :=
  l.map fun i => levelOp (orders (m0 + i))

/-- The tie of the two sides' roots, at w planes. -/
def tieOps (w : Nat) : List Op :=
  [sumOp (noVar 3 3)] ++ (List.range (w - 2)).flatMap fun _ => [sumOp (noVar 3 2)]

/-- From the product of the parts' roots to each root: n steps. -/
def partsOps : Nat → List Op
  | 0 => []
  | n + 1 => [sumOp (noVar 2 2)] ++ partsOps n

/-- The parts' key trees, one after the other. -/
def keysOps (f : Face) : List (Nat × Nat) → List Op
  | [] => []
  | x :: xs => levelOps 0 (f.orders x.2) (List.range x.1) ++ keysOps f xs

/-- **The steps of a lookup at the face f**, in the order of its rounds. -/
def lookOps (f : Face) : List Op :=
  [.owe] ++ ([.owe] ++ ([.owe] ++ (tieOps f.planes ++ (partsOps (f.parts.length - 1) ++
    (keysOps f f.parts.zipIdx ++ (levelOps f.mu orderDefault (List.range f.d) ++
      ([.left (MaskedSum.ownSlots (leafVars f #[]))] ++
        [sumOp (bitsCall (List.replicate (f.mu + f.d) zeroE))])))))))

/-- **What a lookup's hearing does to the ledger's shape.** -/
def lookUpd (f : Face) (L : LedSh) : LedSh := runOps (lookOps f) L

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.runOps_append
