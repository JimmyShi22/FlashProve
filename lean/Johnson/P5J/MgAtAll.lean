-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/MgAtAll.lean: THE ONE HEAD WITH WHAT IS HANDED IN, AND THE CONSTANT WITH ALL 29 LETTERS AT TERMS. One structure, two definitions, two theorems.
  AtMgA o Z D r Zp Np cF x : Prop: A STRUCTURE THAT EXTENDS AtMg (Johnson/P5J/AtMg.lean) BY FOUR FIELDS:
    headAt  headAt (X Zp) = some x: the output head's lookup has its place (its test: isSome): the condition under which x is handed in
    cols13  2 ^ (P13 Zp).lin.kCol = cols: WITH nR := rows (laid here) the last sub-protocols' matrix off the committed table's cells neither drops a cell nor reads a 0 beyond the bounds. (P13 Zp).lin is READ BACK from the first chain's parameter bytes: that it is the sized shape: `linOne`, Johnson/P5J/Cols13Paid.lean, where the value is laid (`LaidAt`).
    opts    At.OptsOk Zp Z.lay (Johnson/P5J/OptsOk.lean): SEVEN Bools: NO DEFAULT INSIDE A PARAMETER's TERM ANSWERS IN SILENCE: the built links at every written segment · tlAt at the feed-forward ones · the attention plans · the last sub-protocols' "from" and its three rounds · the code switches' places wherever a typed row answers · the whole data · the listed seats (by report: in scope the scale file and eight numbers of the policy are free: an evaluation stands at one value of them)
    k3      At.k3SeatsB Zp cF Z.lay = true (Johnson/P5J/Rad3Seat3Tests.lean): the like for rad3 | seat3's 0 | (0, 0)
  AtMgA.𝔇 h := At.𝔇Whole … at nR := numsFull.rows · **mgAtAll h := mgAll h.𝔇 mgBase: THE CONSTANT: NO LETTER LEFT BUT THE HEAD's OWN.**
  mgAtAll_is: it IS mgAt h.toAtMg ‹that structure› (rfl): so whatever is shown of mgAt at every 𝔇₀ holds of it · AtMgA.tieStart: the eleven facts on a start at its letter mgLetter h.𝔇 mgBase, for every DP.
None of these conditions, nor any of PlanOk's, is itself a test that verify() runs: they are named conditions with code. In scope, where protocolDataWellFormed accepts, they follow from what verify() does ask (AtNameA.lean's head; `conds_of_laid`, Goal/Skeleton/CondsOfLaid.lean:134; `P5J.owed_of_live`).
Limits. A bundling. It shows no condition to hold. The full size alone. A MEMBER OF THE HEAD IS PROVED AT THE SECOND HASH FUNCTION OnBytes.secondHashFunction, AT TWO WRITTEN SETS OF PUBLIC FILES VerifierAndGoals.storedPublicFiles AND VerifierAndGoals.zGap, IN THE SIDE LIBRARY (AtFullSide/Top/: headMember_zFull, headMember_zGap); AT OTHER FILES OR HASHES NONE IS SHOWN. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtConst
import Johnson.P5J.LettersAt4
import Johnson.P5J.OptsOk
import Johnson.P5J.Rad3Seat3Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase mgLetter MsgT)
open OnBytes.Maker (WholeD)

/-- **THE ONE HEAD, WITH WHAT IS HANDED IN.** -/
structure AtMgA (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) : Prop extends AtMg o Z D r Zp Np cF where
  headAt : VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some x
  cols13 : 2 ^ (At.P13 Zp).lin.kCol = colsAt OnBytes.Flat.numsFull
  opts : At.OptsOk Zp Z.lay
  k3 : At.k3SeatsB Zp cF Z.lay = true

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The structure of letters under it. -/
noncomputable def AtMgA.𝔇 (h : AtMgA o Z D r Zp Np cF x) :
    MgData ProofFile.Inst ProofFile.InstPub At.Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull)
      OnBytes.Flat.numsFull.rows (At.X Zp) :=
  At.𝔇Whole o Zp Np cF (At.EAt Z) h.plan.shape Z.lay h.plan.laid h.plan.hN h.plan.hG
    x OnBytes.Flat.numsFull.rows

/-- **THE CONSTANT.** -/
noncomputable def mgAtAll (h : AtMgA o Z D r Zp Np cF x) :
    VerifiableInference.Desc.First.Meaning ProofFile.InstPub (Wit (CellsM OnBytes.Flat.numsFull) At.Tok MsgT) :=
  mgAll h.𝔇 mgBase

/-- It is mgAt at that structure. -/
theorem mgAtAll_is (h : AtMgA o Z D r Zp Np cF x) :
    mgAtAll h = mgAt h.toAtMg h.𝔇 := rfl

/-- The facts on a start, at the constant's letter. -/
theorem AtMgA.tieStart (h : AtMgA o Z D r Zp Np cF x) (DP : WholeD) :
    TieStart (Z := Z) (lay := some Z.lay) (X := At.X Zp) OnBytes.Flat.numsFull (At.EAt Z) DP
      (F0T o Zp Np cF) LPFD.Full.instanceAsPlainRecord (fun s => s) (fun q : ProofFile.InstPub => q.request)
      (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) ProofFile.Inst.asked (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay)
      (At.N Zp cF) (mgLetter h.𝔇 mgBase) At.ps (F0T o Zp Np cF) (At.smp Zp)
      Zp.made.p.chains.proof.first.codes (fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request) :=
  h.toAtMg.tieStart DP h.𝔇

end P5J

#print axioms P5J.mgAtAll_is
#print axioms P5J.AtMgA.tieStart
