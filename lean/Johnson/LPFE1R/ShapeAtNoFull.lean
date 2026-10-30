-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ShapeAtNoFull.lean: THE CLOSED FACT BENEATH THE CLAUSE "shape"
(ShapeAtNo.lean beside this file): AT A MEMBER's NUMBER THE PLAN's LIST OF SHAPES HAS THE WRITTEN
LIST's SHAPE: at the written values of the full size BY LEAN's KERNEL, at all 25 links; carried to
the composed meaning's own letters IN THE GOALS' SCOPE, where the verifier's own value is laid; and
the clause itself there. Theorems. A law file; no running text imports it.
  `seatsFullW`         the written plan's seats, as (tree, tenant).
  `shapes_written`     BY THE KERNEL: at every l < 25 and every place i of the l-th written list
                    lo: MList[noK10 seatsFullW lo P5T.psFull l i]? = some (lo.get i).1. MList: the
                    written sendings' messages' shapes in the order in which they are written
                    (Johnson/Top/H0/K2Hands/FrontsFull.lean); it is MW, the same sorted (MW_eq
                    there: Lean's kernel does not unfold the sorting); noK10: the term for
                    a member's number (Johnson/Desc/First/Close/Law/NoOfLink.lean).
  `shapes_written_next`   A NEGATIVE LINE, BY THE KERNEL: with the numbers of link l + 1 in their
                    place no link passes.
  `shape_fact_laid`    in scope, where the value is laid: (msgsOfChain Zp.made.proof.1)[noK10
                    (At.seats Zp) lo (At.pseats Zp) l i]? = some (lo.get i).1. By two other files'
                    joints: LaidAt.seats (Johnson/P5T/CoreAtMg.lean) · sends_in_scope
                    (Johnson/Goal/Numbers/MadeInScope.lean).
  `shape_clause_laid`  so, at a state s with the fold's fact atFirstShapes (msgsOfChain
                    Zp.made.proof.1) s, at every member whose number lies below the number of the
                    statement's messages: (s.st.oracles[no i]?).map (·.shape) = some (lo.get i).1.
                    AT l = 24 AS AT THE OTHERS.

Limits. "The number lies below" is a premise (the promise's bookAt with a count, or the group's
members being messages of the statement, pays it). atFirstShapes is a premise on the state. The full
size alone. Nothing on soundness or on hiding.
-/
import Johnson.LPFE1R.ShapeAtNo
import Johnson.Desc.First.Close.Law.NoOfLink
import Johnson.Top.H0.K2Hands.FrontsFull
import Johnson.P5T.PlanSeatsFull
import Johnson.P5T.CoreAtMg
import Johnson.Goal.Numbers.MadeInScope
import Johnson.G.LinkLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (noK10)
open VerifiableInference.Desc.First.K2Hands (MW MList MW_eq)
open VerifiableInference.Desc.K12.Door (atFirstShapes msgsOfChain)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)

/-- The written plan's seats. -/
def seatsFullW : List (ℕ × ℕ) := P5T.psFull.map fun p => (p.j, p.t)

set_option maxRecDepth 1000000 in
/-- **At the written values, at all 25 links.** -/
theorem shapes_written : ((List.range 25).all fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      MList[noK10 seatsFullW (linksFullLit.getD l []) P5T.psFull l i]? ==
        some ((linksFullLit.getD l []).get i).1) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: the numbers of the next link. -/
theorem shapes_written_next : ((List.range 25).any fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      MList[noK10 seatsFullW (linksFullLit.getD l []) P5T.psFull (l + 1) i]? ==
        some ((linksFullLit.getD l []).get i).1) = false := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **The closed fact at the composed meaning's own letters.** -/
theorem shape_fact_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (i : Fin (linksFullLit.getD l []).length) :
    (msgsOfChain Zp.made.proof.1)[noK10 (P5J.At.seats Zp) (linksFullLit.getD l [])
      (P5J.At.pseats Zp) l i]? = some ((linksFullLit.getD l []).get i).1 := by
  have e1 : P5J.At.pseats Zp = P5T.psFull := L.seats hW
  have e2 : P5J.At.seats Zp = seatsFullW := by
    unfold P5J.At.seats seatsFullW
    rw [e1]
  have e3 : msgsOfChain Zp.made.proof.1 = MList := by
    rw [sends_in_scope hW L.pub (P5J.pins_of_laid hW L).1]
    exact MW_eq
  rw [e1, e2, e3]
  have h := List.all_eq_true.1 (List.all_eq_true.1 shapes_written l (List.mem_range.2 hl)) i
    (List.mem_finRange i)
  exact eq_of_beq h

/-- **The clause "shape" there.** -/
theorem shape_clause_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25) {s : S}
    (hshapes : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true)
    (i : Fin (linksFullLit.getD l []).length)
    (hlt : noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l i <
      s.st.oracles.size) :
    (s.st.oracles[noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l i]?).map
      (·.shape) = some ((linksFullLit.getD l []).get i).1 :=
  shape_at_no hshapes hlt (shape_fact_laid hW L hl i)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.shapes_written
#print axioms VerifiableInference.Desc.LinkJoin.shapes_written_next
#print axioms VerifiableInference.Desc.LinkJoin.shape_fact_laid
#print axioms VerifiableInference.Desc.LinkJoin.shape_clause_laid
