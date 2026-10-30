-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10CarryOut.lean: AT THE CLOSED CONSTANT: THE TABLE's RELATION BEHIND K10's PLACE HOLDS
THE SENTENCE "carry" OF THE PLACE's LINK, AND THAT SENTENCE IS `carryAtZ`: the
tie that `hCar_end` (Johnson/Desc/First/Link/Law/HCarEnd.lean) wants between K10's
law's hypothesis on the statement behind and its own premise. Statements and proofs; two evaluations
by the kernel.

  `carryOut_full`: at every place of the kind K10 of `At.ps` the item "carry" of the place's link is
    among what the table's row opens: by the kernel, on the written lists. `carryOut_bent`: A
    NEGATIVE LINE: the next link's is among what no such row opens.
  `k10_carry_out_at`: so `outsQ fullLinks At.ps i (Item.carry (a.link.getD 0))`.
  `mgAtAll_carry`: the composed meaning's sentence "carry" at the constant IS `K2Caller.carryAtZ Zp
    Z.lay`: by definition.
  `k10_carry_behind`: SO: the table's relation at what K10's row opens, at a statement s and a
    witness w, gives `carryAtZ Zp Z.lay (a.link.getD 0) s.1 (strsOf .. s.2) w`.
Limits. A reading of the table and of the constant's letters. Nothing on soundness.

-/
import Johnson.P5J.K10AsksFill

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item rowOf)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- The first chain's pieces' type. -/
local notation "PC" => Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl
  (Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

/-- "carry" of link (the place's + d) is among what the row opens. -/
def carryOutBy (d : ℕ) (a : VerifiableInference.Desc.Place) : Bool :=
  (rowOf fullLinks a).outs.contains (Item.carry (a.link.getD 0 + d))

theorem carryOut_full :
    (At.ps.all fun a => a.kind != KindName.K10 || carryOutBy 0 a) = true := by decide +kernel

/-- A negative line: the next link's is among what no such row opens. -/
theorem carryOut_bent :
    (At.ps.any fun a => a.kind == KindName.K10 && carryOutBy 1 a) = false := by decide +kernel

theorem k10_carry_out_at (i : ℕ) (a : VerifiableInference.Desc.Place) (ha : At.ps[i]? = some a)
    (hk : a.kind = KindName.K10) : outsQ fullLinks At.ps i (Item.carry (a.link.getD 0)) := by
  have h1 := List.all_eq_true.1 carryOut_full a (List.mem_of_getElem? ha)
  rw [hk] at h1
  have h2 : (rowOf fullLinks a).outs.contains (Item.carry (a.link.getD 0 + 0)) = true := h1
  unfold outsQ
  rw [rowQ_at i a ha]
  exact List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.1 h2))

/-- The sentence "carry" at the constant is the switch's files' `K2Caller.carryAtZ`. -/
theorem mgAtAll_carry (h : AtMgA o Z D r Zp Np cF x) :
    (mgAtAll h).carry = VerifiableInference.Desc.First.K2Caller.carryAtZ Zp Z.lay := rfl

/-- **THE RELATION BEHIND K10's PLACE GIVES carryAtZ.** -/
theorem k10_carry_behind (h : AtMgA o Z D r Zp Np cF x) (i : ℕ)
    (a : VerifiableInference.Desc.Place) (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K10)
    (s : ST) (w : Wit (CellsM numsFull) At.Tok MsgT)
    (hw : relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
      (outsQ fullLinks At.ps i) s w) :
    VerifiableInference.Desc.First.K2Caller.carryAtZ Zp Z.lay (a.link.getD 0) s.1
      (strsOf FR s.2) w :=
  hw _ (k10_carry_out_at i a ha hk)

end P5J

#print axioms P5J.carryOut_full
#print axioms P5J.carryOut_bent
#print axioms P5J.k10_carry_out_at
#print axioms P5J.mgAtAll_carry
#print axioms P5J.k10_carry_behind
