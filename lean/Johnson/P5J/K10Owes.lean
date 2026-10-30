-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Owes.lean: THE FIELD OF THE KINDS' LAWS FOR THE KIND K10, AT THE CLOSED CONSTANT,
FROM THE CONDITION's SECOND FORM (`K10Owes`, Johnson/Desc/First/Close/Law/KindK10Owes.lean): the
fifth tie is no field of it. A call; no more. Beside Johnson/P5J/K10Kind.lean.

What is said.
  `ex_is_table`: the seated term's extractor `h.toAtMg.ex L` is the table's own extractor `extQAt`
    at the seated term's letters: by definition.
  `AtMgA.K10Owes h L`: `K10Owes` at these letters, the numbers, the closed meaning, the written
    lists, the fence that the join spends, and the pieces of the seated term.
  `k10_cond_at_of_owes`: it gives `h.K10Cond L`. `k10_kind_at_owes`: so `h.Kind L .K10`.
Limits. BOOK-KEEPING. THE CONDITION IS THE DEBT: no member is known. One field still names a part of
the conclusion (law). Nothing on soundness.

-/
import Johnson.P5J.K10Kind
import Johnson.Desc.First.Close.Law.KindK10Owes

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
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (k10_cond_of_owes)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The seated term's extractor is the table's own, at the seated term's letters. -/
theorem ex_is_table (h : AtMgA o Z D r Zp Np cF x)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) :
    h.toAtMg.ex L =
      extQAt (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
        (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp Z.lay)
        (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) L.c₀ At.tokOf (At.N Zp cF) fullLinks At.ps
        (fun a => a) := rfl

/-- **K10's ONE NAMED CONDITION, SECOND FORM, AT THE CLOSED CONSTANT.** -/
def AtMgA.K10Owes (h : AtMgA o Z D r Zp Np cF x)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  VerifiableInference.Desc.First.Close.K10Owes
    (F := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
    (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp Z.lay)
    (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) L.c₀ At.tokOf (At.N Zp cF) (mgAtAll h) fullLinks
    At.ps h.toAtMg.rch (h.toAtMg.row L)

/-- The second form gives the first. -/
theorem k10_cond_at_of_owes (h : AtMgA o Z D r Zp Np cF x)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) (W : h.K10Owes L) : h.K10Cond L :=
  k10_cond_of_owes _ _ _ _ _ _ _ _ _ _ _ _ _ _ W

/-- **THE FIELD.** -/
theorem k10_kind_at_owes (h : AtMgA o Z D r Zp Np cF x)
    (L : Free numsFull D (F0T o Zp Np cF) At.Tok) (W : h.K10Owes L) : h.Kind L .K10 :=
  k10_kind_at h L (k10_cond_at_of_owes h L W)

end P5J

#print axioms P5J.ex_is_table
#print axioms P5J.k10_cond_at_of_owes
#print axioms P5J.k10_kind_at_owes
