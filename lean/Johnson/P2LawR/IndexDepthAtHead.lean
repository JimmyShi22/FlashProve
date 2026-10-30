-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/IndexDepthAtHead.lean: THE THIRD PART OF PlanAt's FIFTH CLAUSE AT THE INDEX MASKS'
MEMBER, UNDER THE HEAD: the member's tree is told no deeper than the first stage's Z.a at the place
of the request's own test: the premise hlg that Johnson/P2LawR/IndexAtHead.lean's AtMg.fits_index
keeps. FROM THE HEAD AND THE FIELD seats AT THAT MEMBER. At every o.
HOW. · The tree's told depth: SeatFits' third clause: o.logLength = aOf cs (the member's shape) ·
the shape and the codes: the written ones (AtMg.sized_at_head) · the first stage:
place_W_of_full (Johnson/Desc/K12/Law/Sizes/PlacesAtScope.lean) over atFull_of_pubPlain
(Johnson/Loose/H2K12/AtFullPlain.lean): the stages at the plan's own place are the closed place's ·
then ONE CLOSED COMPARISON OF TWO NUMBERS, by Lean's kernel.
  depth_index_written   the closed comparison.
  stages_of_p12At   where proximityTestParametersAt's stages are not empty they are the place's own.
  AtMg.stages_W   the plan's own stages at that place are piWFull's.
  **AtMg.depth_index**   the statement.
Limits. The field seats at the member (hF) and the member's shape (hy: mineI and oneSeat) are
premises. The two radii are not spoken of. NO MEMBER: that a head can be had is not said. The full
size alone. It leans on the door's asksAt2. (Where
this and lean/THEOREM.md differ, the page holds.) Raised limits: maxRecDepth 1000000 at the closed
fact. Nothing on soundness.

-/
import Johnson.P2LawR.IndexAtHead
import Johnson.P2LawR.PlanLeftAt
import Johnson.Loose.H2K12.AtFullPlain
import Johnson.Desc.K12.Law.Sizes.PlacesAtScope
import Johnson.Desc.K12.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.Sound (Mem SeatFits seatOf)
open VerifiableInference.PlanWritten (proofSizedFull)

set_option maxRecDepth 1000000 in
/-- The closed comparison: the written shape's depth at the written codes against the closed place's
first stage. -/
theorem depth_index_written :
    H2K.Pin.aOfB proofSizedFull.codes indexShapeFull ≤
      (H2K.Member.piWFull.nums.stages.head?.map fun s => s.Z.a).getD 0 := by
  decide +kernel

/-- Where proximityTestParametersAt's list of stages is not empty it is the place's own. -/
theorem stages_of_p12At (x : H2U.PlaceNums) (st : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ x).nums.stages = st :: rest) :
    x.nums.stages = st :: rest := by
  unfold H2U.proximityTestParametersAt at h
  split at h
  · simp [H2U.noP12] at h
  · split at h
    · exact h
    · simp [H2U.noP12] at h

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Under the head the stages at the place of the request's own test are the closed place's. -/
theorem AtMg.stages_W (h : AtMg o Z D r Zp Np cF) :
    Np.W.nums.stages = H2K.Member.piWFull.nums.stages :=
  (H2K.Sizes.place_W_of_full (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub) h.laid.places).1

/-- **THE INDEX MASKS' MEMBER's TREE IS TOLD NO DEEPER THAN THE FIRST STAGE's Z.a.** -/
theorem AtMg.depth_index (h : AtMg o Z D r Zp Np cF) {Xi' : Type} (G' : FileDescription Xi') (y : Mem)
    (hF : SeatFits G' Zp.p.chains.made.sized.proof.codes y.1.l y.1.seat)
    (hy : (y.1.l.get y.2).1 =
      (Zp.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default)
    (st : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest) :
    ∀ oo, G'.oracleAt (seatOf y).1 = some oo → oo.logLength ≤ st.Z.a := by
  intro oo ho
  obtain ⟨o', n, ho', _, hlen, _⟩ := hF y.2
  obtain rfl : o' = oo := Option.some.inj (ho'.symm.trans ho)
  have hs : H2K.Member.piWFull.nums.stages = st :: rest :=
    h.stages_W.symm.trans (stages_of_p12At Np.W st rest hst)
  have hc := depth_index_written
  rw [hs] at hc
  rw [hlen, hy, h.sized_at_head]
  exact hc

end P5J

#print axioms P5J.depth_index_written
#print axioms P5J.stages_of_p12At
#print axioms P5J.AtMg.stages_W
#print axioms P5J.AtMg.depth_index
