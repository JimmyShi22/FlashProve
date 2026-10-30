-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ClaimsAtS.lean: the step of adding of an attention segment in front of the
step that adds the smallness test's claims, as `K9.adds` over K3's and K5's seven runs, at the state
that the proof file's first chain carries. Definitions with code; no theorem.
THE ORDER IS THE FIRST STRETCH OF THE DRIVER's ONE TABLE (Johnson/Desc/First/Driver/Chain.lean:
`orderCuts`), each entry looked up by name (Johnson/Desc/First/Batch/Objects.lean: `runsBy`). The
block's test on the plan is K5's claims' tests on the plan alone (`First.Att.P.claimsOkAtO`).
THE RUNS ARE OTHER FILES' TEXTS, BY NAME: K3's block at the calls, its runs on, "planes" stated with
K5 as its caller (Johnson/Desc/First/Look/K3Own.lean, K3Runs.lean; the caller's readers:
`First.Att.P.readersOfO`) and K5's four (`First.Att.P.runsO`, Johnson/Desc/First/Att/SeatO.lean).
Limits: definitions; no law is stated here. Runs alone hold the step against the lines of the
program `verify-on-bytes`: at both stored sizes with K5's list at another seat (`runsW`); with this
one (`runsO`) at the small size alone, inside whole rides of the chain. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ObjectsAtS
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.First.Att.SeatW
import Johnson.Desc.First.Att.SeatC
import Johnson.Desc.First.Att.SeatO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- A linear form, claimed to be 0, as a claim. -/
def ofForm (a : Aff) : Claim := { form := a }

/-- A named run of forms as a named run of claims. -/
def runOfForms (r : String × (Nat → S → Except String (List Aff × S))) : RunOf S :=
  (r.1, fun n s => (r.2 n s).map fun y => (y.1.map ofForm, y.2))

/-- K3's block at the calls of segment i, its runs on, "planes" stated with K5 as its caller. -/
def k3CallsWith (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (A : Attention.Plan) : Option (Block S Claim) :=
  (First.Look.placeAt X i false).bind fun p =>
    (K3.theOwn (Cl := Claim) ofForm true X codes shape
      ⟨1, some i, K3.pieceAt X i false, .K3⟩).map fun b =>
        K3.withCaller (K3.seatCalls ofForm) p (First.Att.P.readersOfO A) b

/-- The attention plan of segment i; nothing unless it is an attention segment. -/
def attPlan (X : Verify.Public) (i : Nat) : Option Attention.Plan :=
  let step := if X.p4 then 2 else 1
  if i == step * X.NGr || i % step == 0 then none else X.A[i / step]?

/-- **What block number b of an attention segment states**, for the first stretch: by the kind that
the driver has at b: K3 at the calls' piece: its block with K5 as caller; K5: its four. -/
def statesAtt (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat)
    (A : Attention.Plan) (b : Nat) : List (RunOf S) :=
  match (First.kindsBeforeBatching .attention (i == 0))[b]? with
  | some .K3 =>
    if b + 1 == K3.pieceAt X i false then
      ((k3CallsWith X codes shape i A).map fun x => x.claims).getD []
    else []
  | some .K5 => (First.Att.P.runsO A).map runOfForms
  | _ => []

/-- **The seven runs at segment i.** -/
def claimsRuns (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (i : Nat) :
    Option (List (RunOf S)) :=
  (attPlan X i).bind fun A =>
    runsBy (statesAtt X codes shape i A) (cutAt .attention 0)

/-- The step as a block, the list of runs turned by f. -/
def claimsAtWith {Cl : Type} (f : List (RunOf S) → List (RunOf S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (i piece : Nat) : Option (Block S Cl) :=
  (attPlan X i).bind fun A =>
    (claimsRuns X codes shape i).map fun runs =>
      { addsStep atS ⟨1, i, piece, piece, 0, 0, 0⟩ "the attention segment's" []
          (k8Window .attention) (cutAt .attention 0) (f runs) pure with
        planOk := First.Att.P.claimsOkAtO A }

/-- **The block at segment i.** -/
def claimsAt {Cl : Type} (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (i piece : Nat) : Option (Block S Cl) := claimsAtWith id X codes shape i piece

end VerifiableInference.Desc.K9
