-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillProducts.lean: CONDITIONAL: the clauses on values
(`PartVals`, Honest/K5/Law/RowsK5.lean) at four of an attention segment's masked sumchecks: the
denominator times the output; the value product on the diagonal; the score at the index; the index's
cells are bits. One abbreviation, and statements with their proofs.

EVERY STATEMENT IS CONDITIONAL. Paid, out of Johnson/Desc/K5/Honest/Law/Parts.lean: the summand is
tame; it has the call's number of end values; at the challenges heard its terms are weighted
products under the verifier's own weights. Staying premises: the shape's and the plan's numbers;
what the summand's points are at the part's front; the ties between the challenges that the summand
reads there and those that the hearing holds; the coins under the sumcheck's own slots; the start
form's worth.
Main names:
  `frontQ`   the challenges that part q may read in a run
  `partVals_division`, `partVals_on`, `partVals_atIndex`, `partVals_cells`

Limits. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Fill
import Johnson.Desc.K5.Honest.Law.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.First.Att.P (Heard UnitG chal batched weights inner wDivision wOn
  wAtIndex wCells)
open H2K5.Honest (Summand K5In Chal shapes iSE iVD iSF iHB Planned Drawn DivIn divIn DivPts PairsAre
  heardAt)

/-- The challenges that part q may read in a run: those heard up to its first round. -/
abbrev frontQ (Z : Seat5) (heard ds : List Fmt.Drawn) (q : Nat) : Chal :=
  chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q))

variable (V X : Type) (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
  (Z : Seat5) (wit : V → K5In) (w : K5In) (heard ds : List Fmt.Drawn) (Wd : World GE)

/-- **The clauses on values at the sumcheck "the denominator times the output".** CONDITIONAL on:
the shape's and the plan's numbers; at the part's front the division's points are there, read as the
library's, and have a piece for each pair; the hearing holds a challenge for each variable and one
more; the key points at the part's front are those at which the verifier lays its weights; the coins
under the sumcheck's own slots; the start form's worth. Tame, the number of end values, the terms
and the weights are paid. -/
theorem partVals_division (hd : Heard) (zk : Array (Array E)) (H : H2K5.Honest.Sized Z.P)
    (Pl : Planned Z.P) {Dv : DivIn} (h : divIn Z.P (frontQ Z heard ds (iSE Z.P.x)) = some Dv)
    {C : Inst.Model.AttSeg.Calls}
    {p : Inst.Model.AttSeg.Pub GE} (R : DivPts Reading.gl Z.P C p Dv) (pr : PairsAre Z.P.g Dv.d.pwW)
    (hr : hd.division.r.length = Z.P.x.e + 1) {wl : UnitG} (hwl : Z.P.g.single .wl = some wl)
    (hsz : (weights wl (zk.getD wl.call #[])).size = Z.P.g.NP)
    (hzk : (frontQ Z heard ds (iSE Z.P.x)).zk = zk)
    (hc : CoinsUnder V X Bk rows look Z wit Wd (iSE Z.P.x) (List.replicate Z.P.x.e 4)
      (prodEnds Z.P.x.pairs) hd.division)
    (hs : (.slot (hd.five + 1) : Aff).value Reading.gl Wd =
      Reading.gl.val (summandAt Z w heard ds (iSE Z.P.x)).total) :
    PartVals V X Bk rows look Z wit w heard ds Wd (iSE Z.P.x) (.slot (hd.five + 1))
      (List.replicate Z.P.x.e 4) (prodEnds Z.P.x.pairs) hd.division
      (GoodProducts (prodEnds Z.P.x.pairs) hd.division
        (wDivision Z.P.g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[]))
          hd)) := by
  subst hzk
  have G := H2K5.Honest.sSE_good Z.P w Pl h hr hwl hsz
  refine partVals_products V X Bk rows look Z wit w heard ds Wd _ _ _ _ _ _ _
    (H2K5.Honest.shape_iSE Z.P.x) ?_ ?_ hc hs ?_
  · rw [summandAt_iSE]
    exact H2K5.Honest.sSE_tame_x Reading.gl H w Pl h R pr
  · rw [summandAt_iSE]
    exact H2K5.Honest.sSE_ends_x Z.P w _ Pl
  · rw [summandAt_iSE]
    exact ⟨Z.P.x.pairs, _, rfl, G.1, G.2, fun _ _ => rfl⟩

/-- **The clauses on values at the sumcheck "the value product on the diagonal".** CONDITIONAL on:
the shape's and the plan's numbers; at the part's front the division's points are there, read as the
library's, and have a piece for each pair; the hearing holds a challenge for each variable and one
more; the key points at the part's front are those at which the verifier lays its weights; the coins
under the sumcheck's own slots; the start form's worth. Tame, the number of end values, the terms
and the weights are paid. -/
theorem partVals_on (hd : Heard) (zk : Array (Array E)) (H : H2K5.Honest.Sized Z.P)
    (Pl : Planned Z.P) {Dv : DivIn} (h : divIn Z.P (frontQ Z heard ds (iVD Z.P.x)) = some Dv)
    {C : Inst.Model.AttSeg.Calls}
    {p : Inst.Model.AttSeg.Pub GE} (R : DivPts Reading.gl Z.P C p Dv) (pr : PairsAre Z.P.g Dv.d.pwW)
    (hr : hd.on.r.length = Z.P.x.valueD + 1) {wl : UnitG} (hwl : Z.P.g.single .wl = some wl)
    (hsz : (weights wl (zk.getD wl.call #[])).size = Z.P.g.NP)
    (hzk : (frontQ Z heard ds (iVD Z.P.x)).zk = zk)
    (hc : CoinsUnder V X Bk rows look Z wit Wd (iVD Z.P.x) (List.replicate Z.P.x.valueD 4)
      (prodEnds Z.P.x.pairs) hd.on)
    (hs : (.slot (hd.values + 1) : Aff).value Reading.gl Wd =
      Reading.gl.val (summandAt Z w heard ds (iVD Z.P.x)).total) :
    PartVals V X Bk rows look Z wit w heard ds Wd (iVD Z.P.x) (.slot (hd.values + 1))
      (List.replicate Z.P.x.valueD 4) (prodEnds Z.P.x.pairs) hd.on
      (GoodProducts (prodEnds Z.P.x.pairs) hd.on
        (wOn Z.P.g (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])) hd)) := by
  subst hzk
  have G := H2K5.Honest.sVD_good Z.P w Pl h hr hwl hsz
  refine partVals_products V X Bk rows look Z wit w heard ds Wd _ _ _ _ _ _ _
    (H2K5.Honest.shape_iVD Z.P.x) ?_ ?_ hc hs ?_
  · rw [summandAt_iVD]
    exact H2K5.Honest.sVD_tame_x Reading.gl H w Pl h R pr
  · rw [summandAt_iVD]
    exact H2K5.Honest.sVD_ends_x Z.P w _ Pl
  · rw [summandAt_iVD]
    exact ⟨Z.P.x.pairs, _, rfl, G.1, G.2, fun _ _ => rfl⟩

/-- **The clauses on values at the sumcheck "the score at the index".** CONDITIONAL on: the shape's
and the plan's numbers; at the part's front the round that draws many elements has been heard whole;
the hearing holds a challenge for each variable and one more; the batching element's powers and the
point that the hearing holds are those that the summand reads at the part's front; the coins under
the sumcheck's own slots; the start form's worth. -/
theorem partVals_atIndex (hd : Heard) (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P)
    (Dr : Drawn Z.P (frontQ Z heard ds (iSF Z.P.x)))
    (hr : hd.atIndex.r.length = Z.P.x.attained + 1)
    (ho : hd.om = (heardAt Z.P (frontQ Z heard ds (iSF Z.P.x)) fun _ => none).om)
    (hpt : hd.point = (heardAt Z.P (frontQ Z heard ds (iSF Z.P.x)) fun _ => none).point)
    (hc : CoinsUnder V X Bk rows look Z wit Wd (iSF Z.P.x) (List.replicate Z.P.x.attained 4)
      (prodEnds Z.P.x.pairs) hd.atIndex)
    (hs : (batched Z.P.x.pairs hd.om hd.maxima 1 0).value Reading.gl Wd =
      Reading.gl.val (summandAt Z w heard ds (iSF Z.P.x)).total) :
    PartVals V X Bk rows look Z wit w heard ds Wd (iSF Z.P.x)
      (batched Z.P.x.pairs hd.om hd.maxima 1 0) (List.replicate Z.P.x.attained 4)
      (prodEnds Z.P.x.pairs) hd.atIndex
      (GoodProducts (prodEnds Z.P.x.pairs) hd.atIndex (wAtIndex Z.P.g hd)) := by
  have G := H2K5.Honest.sSF_good H w Pl _ hr ho hpt
  refine partVals_products V X Bk rows look Z wit w heard ds Wd _ _ _ _ _ _ _
    (H2K5.Honest.shape_iSF Z.P.x) ?_ ?_ hc hs ?_
  · rw [summandAt_iSF]
    exact H2K5.Honest.sSF_tame_x Reading.gl H w Pl Dr
  · rw [summandAt_iSF]
    exact H2K5.Honest.sSF_ends_x Z.P w _ Pl
  · rw [summandAt_iSF]
    exact ⟨Z.P.x.pairs, _, rfl, G.1, G.2, fun _ _ => rfl⟩

/-- **The clauses on values at the sumcheck "the index's cells are bits".** CONDITIONAL likewise,
and on: a token has at most 16 bits. -/
theorem partVals_cells (hd : Heard) (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P)
    (Dr : Drawn Z.P (frontQ Z heard ds (iHB Z.P.x))) (hK : Z.P.D.lT ≤ 2 ^ 4)
    (hr : hd.cells.r.length = Z.P.x.bits + 1)
    (ho : hd.om'' = (heardAt Z.P (frontQ Z heard ds (iHB Z.P.x)) fun _ => none).om'')
    (hpt : hd.point = (heardAt Z.P (frontQ Z heard ds (iHB Z.P.x)) fun _ => none).point)
    (hc : CoinsUnder V X Bk rows look Z wit Wd (iHB Z.P.x) (List.replicate Z.P.x.bits 4)
      (prodEnds Z.P.x.pairs) hd.cells)
    (hs : (Aff.ofConst zeroE).value Reading.gl Wd =
      Reading.gl.val (summandAt Z w heard ds (iHB Z.P.x)).total) :
    PartVals V X Bk rows look Z wit w heard ds Wd (iHB Z.P.x) (.ofConst zeroE)
      (List.replicate Z.P.x.bits 4) (prodEnds Z.P.x.pairs) hd.cells
      (GoodProducts (prodEnds Z.P.x.pairs) hd.cells (wCells Z.P.g hd)) := by
  have G := H2K5.Honest.sHB_good H w Pl _ hr ho hpt
  refine partVals_products V X Bk rows look Z wit w heard ds Wd _ _ _ _ _ _ _
    (H2K5.Honest.shape_iHB Z.P.x) ?_ ?_ hc hs ?_
  · rw [summandAt_iHB]
    exact H2K5.Honest.sHB_tame_x Reading.gl H w Pl Dr hK
  · rw [summandAt_iHB]
    exact H2K5.Honest.sHB_ends_x Z.P w _ Pl
  · rw [summandAt_iHB]
    exact ⟨Z.P.x.pairs, _, rfl, G.1, G.2, fun _ _ => rfl⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.partVals_division
#print axioms ProofFile.Honest.K5.partVals_on
#print axioms ProofFile.Honest.K5.partVals_atIndex
#print axioms ProofFile.Honest.K5.partVals_cells
