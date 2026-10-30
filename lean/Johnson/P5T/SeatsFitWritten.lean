-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/SeatsFitWritten.lean: the head's named test `seatsFitP` (Johnson/P5T/MembersPlain.lean:
no entry with a sample has a fault at its tree and tenant) AT THE WRITTEN VALUES OF THE FULL SIZE,
and in the goals' scope. Definitions and statements with their proofs.

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM AND ITS TIE:
  F · of F the test reads what is told of a tree alone (`FileDescription.oracleAt`); the written seats'
    trees lie below 83, so the first chain's tellings alone · `toldCut.flatten`
    (Johnson/Desc/First/CutWritten.lean) · `told_at_written` UNDER "the first chain's cut is the
    written one": an accept of the verifier's second test gives it: a law elsewhere; a premise here.
  cs · `codesFull2` (Johnson/G/PackLit.lean) · `first_written_in_scope`, `codes_written`: compiled.
  ps · `psFull` · `seats_in_scope`: compiled.

  `seatFaultO`, `seatFaultAt_is`: the fault's own text at what is told of the tree; by the make.
  `seatsFitO os cs ps`: the test's own text at a list of tellings.
  `seatsFit_written`: (W). `seatsFit_rejects`: (N): with each tree handed its neighbour's telling,
    and at no telling, it rejects. `seatsFit_walks`: 167 entries are walked; every seat's tree is
    below 83.
  `seatsFit_of_cut`: at any IOP as written in Lean whose first chain has the written cut.
  `seatsFit_in_scope`: (Z).
  `seatsFit_at_name`: **the same in the letters of the law that asks the test**: from the scope,
    `LaidAt` (Johnson/P5J/LaidOpens.lean) and TWO PREMISES MORE: hy, an accept of `madePinnedAt`;
    hc, the first chain's cut is the written one: no field of `LaidAt` pays them today: they are the
    two comparisons with written values in the verifier's thirteen tests (ProofAsksFirstThirteenTests.lean): where
    these are laid, the field `asks` pays them.
    (Where this and lean/THEOREM.md differ, the page holds.)
By evaluations in Lean's kernel (`decide +kernel`): `seatsFit_written`, `seatsFit_rejects`,
`seatsFit_walks`.

Limits. Nothing on the two later chains' seats. Nothing on soundness.
-/
import Johnson.P5T.EndsWritten
import Johnson.P5T.MembersPlain
import Johnson.HB.LLHARD.TreesOfCut
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- `seatFaultAt`'s own text (Johnson/Desc/SeatAt.lean), at what is told of the tree. -/
def seatFaultO (orc? : Option Oracle) (codes : OnBytes.Codes) (tag : String)
    (s : OnBytes.OracleShape) (j t : Nat) : Option String :=
  match orc? with
  | none => some s!"{tag}: tree {j} is told by no block"
  | some orc =>
    match orc.tenants[t]? with
    | none => some s!"{tag}: tree {j} has no tenant {t} ({orc.tenants.length} told)"
    | some n =>
      let bad : List String :=
        (if orc.logLength == longOf codes s then []
          else [s!"logLength {orc.logLength} | the code's {longOf codes s}"]) ++
        (if n.main == s.mainRows * s.mainDeg then []
          else [s!"main {n.main} | rows {s.mainRows} * degree {s.mainDeg}"]) ++
        (if n.mask == s.maskRows * 3 then [] else [s!"mask {n.mask} | rows {s.maskRows} * 3"]) ++
        (if s.mainRows == 0 || (codes.base.getD s.code default).logN == longOf codes s
          then [] else ["the mask's code is the longer"]) ++
        (if (orc.tenants.map fun x => x.main + x.mask).sum == orc.words then []
          else [s!"the tenants' words {(orc.tenants.map fun x => x.main + x.mask).sum} | " ++
            s!"the tree's {orc.words}"]) ++
        (if s.mainDeg == 1 || s.mainDeg == 3 then [] else [s!"degree {s.mainDeg}"])
      if bad.isEmpty then none
      else some (s!"{tag}: tree {j} tenant {t} (answers {s.answers}): " ++ "; ".intercalate bad)

theorem seatFaultAt_is {Xi : Type} (F : FileDescription Xi) (codes : OnBytes.Codes) (tag : String)
    (s : OnBytes.OracleShape) (j t : Nat) :
    seatFaultAt F codes tag s j t = seatFaultO (F.oracleAt j) codes tag s j t := rfl

end VerifiableInference.Desc

namespace P5T
open Johnson.G
open VerifiableInference.Desc (FileDescription Oracle oraclesOf seatFaultAt seatFaultO seatFaultAt_is)
open VerifiableInference.Desc.First (toldCut told_at_written)
open VerifiableInference.Desc.K13.Law (oraclesOf_told cut_tells)
open VerifiableInference.PlanWritten (madePinnedAt cutFirstFull codes_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)

/-- The test's own text, at a list of what is told, tree by tree. -/
def seatsFitO (os : List Oracle) (cs : OnBytes.Codes) (ps : List PSeat) : Bool :=
  (ps.filter (·.smpd)).all fun p =>
    (seatFaultO os[p.seat.1]? cs "" p.shape p.seat.1 p.seat.2).isNone

set_option maxRecDepth 1000000 in
/-- **(W)** At the written values it accepts: the written seats against the written cut. -/
theorem seatsFit_written : seatsFitO toldCut.flatten codesFull2 psFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With each tree handed its neighbour's telling it rejects; and at no telling at all. -/
theorem seatsFit_rejects :
    (seatsFitO (toldCut.flatten.drop 1) codesFull2 psFull, seatsFitO [] codesFull2 psFull) =
      (false, false) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- How many entries the test walks; and all sit in trees below 83. -/
theorem seatsFit_walks :
    ((psFull.filter (·.smpd)).length, psFull.all fun p => decide (p.seat.1 < 83)) =
      (167, true) := by decide +kernel

/-- **At an IOP as written in Lean whose first chain has the written cut.** -/
theorem seatsFit_of_cut {Xi : Type} (F : FileDescription Xi)
    (hc : VerifiableInference.PlanWritten.cutOf F.first.blocksInOrder = cutFirstFull) :
    seatsFitP F codesFull2 psFull = true := by
  have hA : oraclesOf F.first.blocksInOrder = toldCut.flatten := by
    rw [oraclesOf_told, (told_at_written hc).2]
  have hL : toldCut.flatten.length = 83 := cut_tells.2.2
  unfold seatsFitP
  rw [List.all_eq_true]
  intro p hp
  have hj : p.seat.1 < 83 := of_decide_eq_true
    (List.all_eq_true.1 (congrArg Prod.snd seatsFit_walks) p (List.mem_of_mem_filter hp))
  have e : F.oracleAt p.seat.1 = toldCut.flatten[p.seat.1]? := by
    unfold FileDescription.oracleAt
    rw [hA, List.getElem?_append_left (by rw [List.length_append, hL]; omega),
      List.getElem?_append_left (by rw [hL]; exact hj)]
  rw [seatFaultAt_is, e]
  exact List.all_eq_true.1 seatsFit_written p hp

/-- **(Z)** In the goals' scope, at the public part's own codes and seats. -/
theorem seatsFit_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) {Xi : Type} (F : FileDescription Xi)
    (hc : VerifiableInference.PlanWritten.cutOf F.first.blocksInOrder = cutFirstFull) :
    seatsFitP F Z.first.codes (planSeats Z Z.D.1) = true := by
  rw [(seats_in_scope hW h hy hl).1, (first_written_in_scope hW h hy).1, codes_written]
  exact seatsFit_of_cut F hc

/-- **The head's named test, in the letters of the law that asks it.** hy: an accept of the
verifier's test on the sizes, the lists of rounds and the sendings. hc: of its test on the first
chain's cut. -/
theorem seatsFit_at_name {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (_hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hc : VerifiableInference.PlanWritten.cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder =
      cutFirstFull) :
    seatsFitP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (P5J.At.cs Zp) (P5J.At.pseats Zp) = true :=
  seatsFit_in_scope hZ L.pub hy (laid_of_at L) _ hc

end P5T

#print axioms VerifiableInference.Desc.seatFaultAt_is
#print axioms P5T.seatsFit_written
#print axioms P5T.seatsFit_rejects
#print axioms P5T.seatsFit_walks
#print axioms P5T.seatsFit_of_cut
#print axioms P5T.seatsFit_in_scope
#print axioms P5T.seatsFit_at_name
