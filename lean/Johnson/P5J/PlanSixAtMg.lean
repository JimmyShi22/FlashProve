-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/PlanSixAtMg.lean (kind K9): `PlanFits` (Johnson/Desc/First/Link/Law/PartFitsReached.lean: the closed sentence under K9's inSeg · inRun · inTot) AT THE CONSTANT's OWN LETTERS, AT THE THREE BORDERS A SEGMENT, FROM THE HEAD AND ONE COMPARISON OF NUMBERS («room»). Theorems: the ties of PlanSixFull.lean
(Johnson/P5T) to the constant.

What is said. h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF.
  `keptAt_msgs`: the frames' list keptBefore reads the numbers by msgsAt alone. `AtMg.kept_is`: (At.foldD Zp cF Ld).keptAt m = P5T.keptFull m (the like of `AtMg.own_is`).
  `AtMg.M_full`: the listed shapes at the constant are the written MFull. `AtMg.ms_full`: the members at the constant are the written ones (`ms_at_laid` with `rows_at_head`).
  `AtMg.five_at_border`: **k ∈ bordersW · At.ps[k]? = some p · p.link = some m ⊢ the five parts (lengths · shapes · members · mask · answers) of planFitsB accept at At.foldD Zp cF LFull · At.ms Zp Z.lay · (At.N Zp cF).group m · the place's moment · (At.N Zp cF).msgsAt At.ps[k]?.**
  `AtMg.planFits_of_room`: **with `AtMg.layoutOk`: these and «ns + the answers ≤ the mask code's length» ⊢ `PlanFits` … ns.**

WHAT STAYS: room: ns is the planning program's number of slots of the BUILT segment (`At.nsAt`, Johnson/P5J/FoldMoreAt.lean): no pin fixes it; evaluated: 4059 | 4190 | 4058 | … | 3570, true at 50 of 50.

Limits. AtMg is a premise (WITH THE FOURTEEN ENTRY TESTS). AT THE SECOND HASH FUNCTION. Nothing on soundness.

-/
import Johnson.P5T.PlanSixFull
import Johnson.P5T.NotIxAtMg
import Johnson.P5J.InsideAtMg
import Johnson.P5J.CodesFullAtMg
import Johnson.P5J.StartAtHead
import Johnson.IMR.RadAtHead
import Johnson.Desc.First.Close.Law.AlikeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (Numbers ModelPart momentAt shiftAt)
open VerifiableInference.Desc.First.FillSent (keptAt sentDataAt baseAt)
open VerifiableInference.Desc.First.Close (mlFull ms_at_laid group_at_laid)
open VerifiableInference.Desc.Sound (msOf)
open VerifiableInference.Desc.LinkJoin (PlanFits planFitsB planFits_of_B shapesB membersB maskB)
open VerifiableInference.Desc.K13.Law (LFull MFull msgs_at)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- `keptAt` reads the numbers by `msgsAt` alone. -/
theorem keptAt_msgs (s : Params.ReqShape) {N N' : Numbers} (h : N.msgsAt = N'.msgsAt)
    (links : List ModelPart) (ps : List Place) (b : Array Stages.LinkH) (m : ℕ) :
    keptAt s N links ps b m = keptAt s N' links ps b m := by
  unfold keptAt sentDataAt
  have e0 : baseAt N links ps = baseAt N' links ps := by
    funext i
    unfold baseAt
    rw [h]
  rw [e0]

/-- The frames' list keptBefore at the constant is the written one. -/
theorem AtMg.kept_is {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) (Ld : Desc.K12.Door.Laid)
    (m : ℕ) : (At.foldD Zp cF Ld).keptAt m = P5T.keptFull m := by
  show keptAt (At.shape Zp) (At.N Zp cF) At.links At.ps Zp.made.p.built.links m =
    keptAt shapeFull P5T.NFull At.links At.ps #[] m
  have es : At.shape Zp = shapeFull := h.shape_full
  rw [es, keptAt_msgs shapeFull (h.laid.msgs h.scope)]
  rfl

/-- The listed shapes at the constant are the written ones. -/
theorem AtMg.M_full (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (Ld : Desc.K12.Door.Laid) :
    (At.foldD Zp cF Ld).M = MFull := msgs_at (written_at_head h).1

/-- The members at the constant are the written ones. -/
theorem AtMg.ms_full (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : At.ms Zp Z.lay = msOf mlFull := by
  obtain ⟨R, hR, -⟩ := IM.Seats.rows_at_head h
  exact ms_at_laid h.scope h.laid hR

/-- **THE FIVE PARTS AT THE CONSTANT's LETTERS.** -/
theorem AtMg.five_at_border (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {k : ℕ}
    (hk : k ∈ P5T.bordersW) {p : Place} (hp : At.ps[k]? = some p) {m : ℕ} (hl : p.link = some m) :
    ((At.foldD Zp cF LFull).sent.codes.lengthsOk &&
      shapesB (At.foldD Zp cF LFull) m (momentAt (shiftAt At.links m) p.piece)
        ((At.N Zp cF).msgsAt At.ps[k]?) &&
      membersB (At.foldD Zp cF LFull) (At.ms Zp Z.lay) ((At.N Zp cF).group m)
        ((At.N Zp cF).msgsAt At.ps[k]?) &&
      maskB (At.foldD Zp cF LFull) m (momentAt (shiftAt At.links m) p.piece)
        ((At.N Zp cF).msgsAt At.ps[k]?) &&
      decide (1 ≤ (At.foldD Zp cF LFull).sent.shape.answers)) = true := by
  have h0 := P5T.five_at hk
  unfold P5T.fiveAtM at h0
  rw [hp] at h0
  simp only [hl] at h0
  rw [P5T.five_is]
  have e1 : (At.foldD Zp cF LFull).sent.codes = Johnson.G.codesFull2 := h.codes_full
  have e2 : (At.foldD Zp cF LFull).sent.shape = shapeFull := h.shape_full
  have e3 : (At.foldD Zp cF LFull).ownAt = P5T.ownFull := by
    funext a b
    exact h.own_is LFull a b
  have e4 : (At.foldD Zp cF LFull).keptAt = P5T.keptFull := by
    funext a
    exact h.kept_is LFull a
  rw [e1, e2, h.M_full LFull, e3, e4, h.ms_full, group_at_laid h.scope h.laid m,
    h.laid.msgs h.scope, hp]
  exact h0

/-- **PlanFits AT THE CONSTANT, FROM THE HEAD AND «room».** -/
theorem AtMg.planFits_of_room (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {k : ℕ}
    (hk : k ∈ P5T.bordersW) {p : Place} (hp : At.ps[k]? = some p) {m : ℕ} (hl : p.link = some m)
    (ns : ℕ)
    (room : ns + (At.foldD Zp cF LFull).sent.shape.answers ≤
      ((At.foldD Zp cF LFull).sent.codes.mask.getD (At.foldD Zp cF LFull).sent.shape.maskCode
        default).ell) :
    PlanFits (At.foldD Zp cF LFull) (At.ms Zp Z.lay) ((At.N Zp cF).group m) m
      (momentAt (shiftAt At.links m) p.piece) ((At.N Zp cF).msgsAt At.ps[k]?) ns := by
  have h5 := h.five_at_border hk hp hl
  simp only [Bool.and_eq_true] at h5
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h5
  refine planFits_of_B ?_
  unfold planFitsB
  have hlay : reqLayoutOk (At.foldD Zp cF LFull).sent.codes (At.foldD Zp cF LFull).sent.shape
      (At.foldD Zp cF LFull).sent.layout = true := h.layoutOk LFull
  rw [a1, hlay, a2, a3, a4, a5, decide_eq_true room]
  rfl

end P5J

#print axioms P5J.keptAt_msgs
#print axioms P5J.AtMg.kept_is
#print axioms P5J.AtMg.M_full
#print axioms P5J.AtMg.ms_full
#print axioms P5J.AtMg.five_at_border
#print axioms P5J.AtMg.planFits_of_room
