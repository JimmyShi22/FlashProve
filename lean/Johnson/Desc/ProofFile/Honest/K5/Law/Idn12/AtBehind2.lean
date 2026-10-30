-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/AtBehind2.lean: CONDITIONAL: A SECOND FORM of 2
declarations of Johnson/Desc/ProofFile/Honest/K5/Law/AtBehind.lean: `partVals_cells_at`,
`partVals_atIndex_at`.
The source forms take as a premise that the cells meet all three of the library's families of
identities on an attention segment (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean). These take the
first two families alone (`Idn12`, Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean).

Why. CONDITIONALLY, `Idn12` follows from two items that the row of the segment's own rounds asks in
front (Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean): among others under the library's head on the
public input as a hypothesis, hH and hc; none of these, nor the items, is shown. The third family on
the whole cube follows from no such item.

How. THE TEXT IS THE ELDER FILE's: each declaration named above with its docstring and its proof,
the premise's name exchanged, and each name of a declaration that has a second form exchanged for
that form's (a subscript 2 at its end). Every other lemma is called from the elder files, which are
imported and stay as they are.

Limits. Those of the source file, whose head says what each premise is.
Every theorem is conditional, FIRST OF ALL ON THE THREE TIES BETWEEN THE WITNESS AND THE HONEST SIDE
(`K5Script`, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtBehind
import Johnson.Desc.K5.Honest.Law.Idn12.Parts2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open VerifiableInference.Desc.First.Att.P (Par Heard UnitG chal batched weights inner wDivision wOn
  wAtIndex wCells)
open H2K5.Honest (shapes slotsTo SumPut Laid iSE iVD iM6 iSF iSD iHB keyVars Planned Drawn DivIn
  divIn DivPts PairsAre heardAt rhoOf om4Of ptsOf IndexPts MaxPts Idn12 tOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
include Hs Sc hT hd hM e hD

variable {G : Fork} {hd5 : Heard} (L : Laid Z.P.x att.F.next (roundsOf y.1) hd5 G)
  (Al : Along Z.P.x (roundsOf y.1) G hd5) (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P)
include L Al H Pl

/-- **The like at "the index's cells are bits".** CONDITIONAL as `coinsUnder_at`, and on: L, Al; the
numbers; at the part's front the round that draws many elements has been heard whole; a token has at
most 16 bits; the powers and the point that the hearing holds are those that the summand reads at
the part's front; THE WITNESS's CELLS MEET THE FIRST TWO OF THE LIBRARY's FAMILIES OF IDENTITIES
(Ai). -/
theorem partVals_cells_at₂ (Dr : Drawn Z.P (frontQ Z m.st.heard ds (iHB Z.P.x)))
    (hK : Z.P.D.lT ≤ 2 ^ 4)
    (ho : hd5.om'' = (heardAt Z.P (frontQ Z m.st.heard ds (iHB Z.P.x)) fun _ => none).om'')
    (hpt : hd5.point = (heardAt Z.P (frontQ Z m.st.heard ds (iHB Z.P.x)) fun _ => none).point)
    (Ai : Idn12 Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace)))) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iHB Z.P.x) (.ofConst zeroE)
      (List.replicate Z.P.x.bits 4) (prodEnds Z.P.x.pairs) hd5.cells
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.cells (wCells Z.P.g hd5)) := by
  have hr : hd5.cells.r.length = Z.P.x.bits + 1 := by
    have := Al.cells.r_length
    rwa [prodVs, List.length_replicate] at this
  refine partVals_cells _ _ _ _ _ Z _ _ _ _ _ hd5 H Pl Dr hK hr ho hpt
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.cells _ hq) ?_
  rw [summandAt_iHB]
  exact H2K5.Honest.start_cells_total₂ Reading.gl H _ Pl Dr hK Ai

/-- **The like at "the score at the index".** CONDITIONAL as `coinsUnder_at`, and on: L, Al; the
numbers; there is a pair; in front of this part and of the maxima's the round that draws many
elements has been heard whole; the powers and the point that the hearing holds are those that the
summand reads at the part's front; these read as the library's letters pb, at both fronts; THE
WITNESS's CELLS MEET THE FIRST TWO OF THE LIBRARY's FAMILIES OF IDENTITIES (Ai). -/
theorem partVals_atIndex_at₂ {n : Nat} (hn : Z.P.x.pairs = n + 1)
    (Dr : Drawn Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)))
    (Dr0 : Drawn Z.P (frontQ Z m.st.heard ds (iM6 Z.P.x)))
    (ho : hd5.om = (heardAt Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => none).om)
    (hpt : hd5.point = (heardAt Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => none).point)
    {pb : Inst.Model.AttSeg.Pub GE}
    (I : IndexPts Reading.gl Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) pb)
    (I0 : MaxPts Reading.gl Z.P (frontQ Z m.st.heard ds (iM6 Z.P.x)) pb)
    (Ai : Idn12 Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace)))) :
    PartVals (Local W₀ Rc Xi Tr) X Bk (Bk.rowsOf T.chain) (k.look T.chain) Z
      (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
      (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds
      (worldOwn (behindPart s att G) [] D) (iSF Z.P.x) (batched Z.P.x.pairs hd5.om hd5.maxima 1 0)
      (List.replicate Z.P.x.attained 4) (prodEnds Z.P.x.pairs) hd5.atIndex
      (GoodProducts (prodEnds Z.P.x.pairs) hd5.atIndex (wAtIndex Z.P.g hd5)) := by
  have hr : hd5.atIndex.r.length = Z.P.x.attained + 1 := by
    have := Al.atIndex.r_length
    rwa [prodVs, List.length_replicate] at this
  obtain ⟨pts, hp0⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iM6 Z.P.x))
  refine partVals_atIndex _ _ _ _ _ Z _ _ _ _ _ hd5 H Pl Dr hr ho hpt
    (coinsUnder_at Hs Sc hT hd hM e hD fun _ hq => L.atIndex _ hq) ?_
  rw [summandAt_iSF]
  refine H2K5.Honest.start_atIndex_total₂ Reading.gl H _ Pl Dr Dr0 hp0 I I0 Ai ho fun i hi => ?_
  have hi' : i < n + 1 := by
    rw [← hn]
    exact hi
  rw [maxima_slots Hs Sc hT hd hM e hD L hn i hi', ProofFile.Honest.SumLaw.padTo_getD, if_pos hi']

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.partVals_cells_at₂
#print axioms ProofFile.Honest.K5.partVals_atIndex_at₂
