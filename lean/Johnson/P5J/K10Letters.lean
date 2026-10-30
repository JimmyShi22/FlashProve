-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Letters.lean: THE CLOSED CONSTANT's EXTRACTOR AND TWO FIELDS OF ITS MEANING, SPELLED
IN THE LETTERS IN WHICH K10's ASSEMBLED LAW SPEAKS. Three statements; each holds by definition.

Why. `k10_two_cs` (Johnson/Desc/First/Close/Law/LawTwoCs.lean) speaks of `extQAt cs Gd arr smpS ms
decT c₀ tokOf Nu links ps (fun a => a) k`, and asks `Mg.row = rowSays Nu (wordsAtFirst arr)` and
`Mg.pin = pinJT cs Gd arr smpS ms`. K10's debt at the constant (`AtMgA.K10Pieces`,
K10LawPieces.lean) speaks of `h.toAtMg.ex L i` and `mgAtAll h`.
  `AtMg.ex_is`: `h.ex L i` IS `extQAt` at `At.cs Zp`, the seated term, `At.arr Zp`, `At.smp Zp`,
    `At.ms Zp Z.lay`, the constant's decoder, `L.c₀`, `At.tokOf`, `At.N Zp cF`, `fullLinks`,
    `At.ps`, the identity, i.
  `mgAtAll_row`, `mgAtAll_pin`: the two fields of `mgAtAll h`.
Limits. Spellings. Nothing on soundness.

-/
import Johnson.P5J.K10Two

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

theorem AtMg.ex_is (h : AtMg o Z D r Zp Np cF) (L : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (i : ℕ) :
    h.ex L i = extQAt (Fr := FR) (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp)
      (At.ms Zp Z.lay) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) L.c₀ At.tokOf (At.N Zp cF)
      fullLinks At.ps (fun a => a) i := rfl

theorem mgAtAll_row (h : AtMgA o Z D r Zp Np cF x) :
    (mgAtAll h).row =
      VerifiableInference.Desc.First.rowSays (At.N Zp cF)
        (VerifiableInference.Desc.First.wordsAtFirst (At.arr Zp)) := rfl

theorem mgAtAll_pin (h : AtMgA o Z D r Zp Np cF x) :
    (mgAtAll h).pin = pinJT (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp)
      (At.ms Zp Z.lay) := rfl

end P5J

#print axioms P5J.AtMg.ex_is
#print axioms P5J.mgAtAll_row
#print axioms P5J.mgAtAll_pin
