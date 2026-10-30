-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Kind.lean: THE FIELD OF THE KINDS' LAWS FOR THE KIND K10 (the closing of a link), AT
THE CLOSED CONSTANT: "the kind's one named condition gives the kind's share in the form in which a
kind's law is counted" (`AtMgA.Kind`, Johnson/P5J/RowsAtAll.lean). A call of
Johnson/Desc/First/Close/Law/KindK10.lean; no more. After Johnson/P5J/K09Kind.lean, which does the
like for the batching kind.

What is said.
  `sorts_are_full`: the row of 25 sorts at which K10's two tests on the table are shown (`sortsOf
    25`, Johnson/Desc/First/Close/Law/PromiseBehind.lean) is the tower's `fullLinks`: by the kernel.
    `fit_full`, `next_full`: so the two tests say yes at `fullLinks` and `At.ps`.
  `AtMgA.K10Cond h L`: `K10Cond` at the numbers, the closed meaning, the written lists, the fence
    that the join spends (`h.toAtMg.rch`), the extractor and the pieces of the seated term.
  `k10_kind_at`: `h.Kind L .K10` from it.
Limits. BOOK-KEEPING. THE CONDITION IS THE DEBT: no member is known; KindK10.lean's head says what
each of its ten fields is, and which two name parts of the conclusion. L is an argument: whoever
states the condition as a hypothesis lays the closed term in. Nothing on soundness.

-/
import Johnson.P5J.RowsAtAll
import Johnson.Desc.First.Close.Law.KindK10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start closersFit closersNext flatPlacesOf sortsOf
  closersFit_real closersNext_real)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (k10_kind)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The row of sorts at which K10's tests on the table are shown is the tower's. -/
theorem sorts_are_full : sortsOf 25 = fullLinks := by decide +kernel

theorem fit_full : closersFit fullLinks At.ps (start fullLinks) = true := by
  have h := (closersFit_real true).1
  rw [sorts_are_full] at h
  exact h

theorem next_full : closersNext fullLinks At.ps = true := by
  have h := (closersNext_real true).1
  rw [sorts_are_full] at h
  exact h

/-- **K10's ONE NAMED CONDITION, AT THE CLOSED CONSTANT.** -/
def AtMgA.K10Cond (h : AtMgA o Z D r Zp Np cF x)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  VerifiableInference.Desc.First.Close.K10Cond
    (F := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
    (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.toAtMg.rch (h.toAtMg.ex L) (h.toAtMg.row L)

/-- **THE FIELD.** -/
theorem k10_kind_at (h : AtMgA o Z D r Zp Np cF x)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) (C : h.K10Cond L) : h.Kind L .K10 :=
  k10_kind (F := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
    (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.toAtMg.rch (h.toAtMg.ex L) (h.toAtMg.row L)
    fit_full next_full C

end P5J

#print axioms P5J.sorts_are_full
#print axioms P5J.fit_full
#print axioms P5J.next_full
#print axioms P5J.k10_kind_at
