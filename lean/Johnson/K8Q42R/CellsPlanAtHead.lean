-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/K8Q42R/CellsPlanAtHead.lean: kind K8: THE CLOSED CONDITION CellsPlan
(Johnson/K8Q33R/CellsInAtDraw.lean) AT THE COMPOSED MEANING's CONSTANT's OWN LETTERS (P5J.At,
Johnson/P5J/LettersAt.lean), AT THE DRAW's BORDER OF ALL 25
SEGMENTS, FROM THE HEAD (WITH ITS ENTRY TESTS).
  five_draw    BY LEAN's KERNEL: the closed test fiveAtM (Johnson/P5T/PlanSixFull.lean) accepts at
               the 25 borders drawAt l (14 l + 6; 343), which are not among its own 75
  five_draw_off    a bent twin: with the listed shapes reversed it accepts at none
  five_at_k    AtMg.five_at_border (Johnson/P5J/PlanSixAtMg.lean), with «fiveAtM MFull k =
  true»
               as a letter in the place of «k ∈ bordersW». A NEAR-COPY OF ITS WALK, SAID: all its
               steps are calls of other files' ties
  rad3W        the written reader «a shape's radius» · rad3_at_head: At.rad3At is it: by
               rows_at_head (IMR/RadAtHead.lean) and first_rows_written (LPFE1R/TableClosed.lean)
  radded_full  BY THE KERNEL: raddedB accepts at the written members (AtMg.ms_full) and rad3W
  radded_off   a bent twin: every radius one more: rejected
  cellsPlan_at_head  MAIN: statement (a) of a list of ours, not in this repository, to the letter
LIMITS. Joins and two closed facts by the kernel, each with a bent twin. A member of the head is
proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). WHAT IT SPENDS OF THE
HEAD: scope · laid (its pub; the pin, read off its «asks») · AND
plan.radii: «the rows' maker returns» (rows_at_head) is read off that test of the head's, whose own
text runs the maker, and which no entry test asks: THE MAKER's RUN IS MOVED INTO THE HEAD, NOT
SPARED. The full size alone; at the second hash function. The flag on the closed test in its own
file's head (Johnson/P5T/PlanSixFull.lean) travels: with the listed seats reversed it still accepted
at 26 of 50 borders: the test is blind to something. No soundness is claimed.
-/
import Johnson.K8Q33R.CellsInAtDraw
import Johnson.P5J.PlanSixAtMg
import Johnson.LPFE1R.TableClosed
import Johnson.P5J.PlanSitsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q42
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (momentAt shiftAt flatPlacesOf)
open VerifiableInference.Desc.First.K8 (drawAt)
open VerifiableInference.Desc.First.Close (mlFull group_at_laid)
open VerifiableInference.Desc.Sound (msOf linksFull)
open VerifiableInference.Desc.LinkJoin (shapesB membersB maskB rowsFirstW first_rows_written)
open VerifiableInference.Desc.K13.Law (LFull MFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Maker (WholeD)
open P5J
open K8Q33 (CellsPlan raddedB radded_of_B cellsPlan_of_B cellsPlanB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## The closed test at the draw's borders -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **By the kernel**: the five accept at the 25 borders of the draw. -/
theorem five_draw : ((List.range 25).all fun l => P5T.fiveAtM MFull (drawAt l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A bent twin: with the listed shapes reversed they accept at none. -/
theorem five_draw_off :
    ((List.range 25).any fun l => P5T.fiveAtM MFull.reverse (drawAt l)) = false := by
  decide +kernel

/-- AtMg.five_at_border, at any border at which the closed test accepts. -/
theorem five_at_k (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {k : ℕ}
    (h0 : P5T.fiveAtM MFull k = true) {p : Place} (hp : At.ps[k]? = some p) {m : ℕ}
    (hl : p.link = some m) :
    ((At.foldD Zp cF LFull).sent.codes.lengthsOk &&
      shapesB (At.foldD Zp cF LFull) m (momentAt (shiftAt At.links m) p.piece)
        ((At.N Zp cF).msgsAt At.ps[k]?) &&
      membersB (At.foldD Zp cF LFull) (At.ms Zp Z.lay) ((At.N Zp cF).group m)
        ((At.N Zp cF).msgsAt At.ps[k]?) &&
      maskB (At.foldD Zp cF LFull) m (momentAt (shiftAt At.links m) p.piece)
        ((At.N Zp cF).msgsAt At.ps[k]?) &&
      decide (1 ≤ (At.foldD Zp cF LFull).sent.shape.answers)) = true := by
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

/-! ## One shape, one radius -/

/-- The written reader «a shape's radius». -/
def rad3W (sh : OracleShape) : ℕ :=
  (((rowsFirstW.flatMap (·.sampled)).find? (·.1 == sh)).map (·.2)).getD 0

/-- The reader At.rad3At at the constant is the written one. -/
theorem rad3_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : At.rad3At Zp Z.lay = rad3W := by
  obtain ⟨R, hR, e⟩ := IM.Seats.rows_at_head h
  funext sh
  unfold At.rad3At At.sampledAt rad3W
  rw [e, first_rows_written h.scope h.laid.pub (P5J.pins_of_laid h.scope h.laid).1 hR]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **By the kernel**: every written member's radius is its shape's. -/
theorem radded_full : raddedB (msOf mlFull) rad3W = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A bent twin: every radius one more: rejected. -/
theorem radded_off : raddedB (msOf mlFull) (fun sh => rad3W sh + 1) = false := by decide +kernel

/-! ## MAIN -/

/-- **CellsPlan AT THE CONSTANT, AT THE DRAW's BORDER OF EVERY SEGMENT.** -/
theorem cellsPlan_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid} (hL : At.laid? Zp = some L₀) {l : ℕ}
    (hl : l ≤ 24) :
    CellsPlan (At.foldD Zp cF L₀) (At.ms Zp Z.lay) ((At.N Zp cF).group l) (At.rad3At Zp Z.lay) l 2
      ((At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?) := by
  obtain rfl : LFull = L₀ := Option.some.inj (h.toAtMg.laid_at_head.symm.trans hL)
  obtain ⟨p, hp, hpl, -, hmo⟩ := P1K8T.draw_place_full l hl
  have hp' : At.ps[drawAt l]? = some p := hp
  have hmo' : momentAt (shiftAt At.links l) p.piece = 2 := hmo
  have h0 := List.all_eq_true.1 five_draw l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  have h5 := five_at_k h.toAtMg h0 hp' hpl
  rw [hmo'] at h5
  simp only [Bool.and_eq_true] at h5
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, -⟩, -⟩ := h5
  refine cellsPlan_of_B ?_
  unfold cellsPlanB
  have hr : raddedB (At.ms Zp Z.lay) (At.rad3At Zp Z.lay) = true := by
    rw [h.toAtMg.ms_full, rad3_at_head h.toAtMg]
    exact radded_full
  show (_ && _ && shapesB (At.foldD Zp cF LFull) l 2 ((At.N Zp cF).msgsAt At.ps[drawAt l]?) &&
    membersB (At.foldD Zp cF LFull) (At.ms Zp Z.lay) ((At.N Zp cF).group l)
      ((At.N Zp cF).msgsAt At.ps[drawAt l]?) && _) = true
  rw [a1, h.toAtMg.layoutOk LFull, a2, a3, hr]
  rfl

end K8Q42

#print axioms K8Q42.five_draw
#print axioms K8Q42.five_draw_off
#print axioms K8Q42.five_at_k
#print axioms K8Q42.rad3_at_head
#print axioms K8Q42.radded_full
#print axioms K8Q42.radded_off
#print axioms K8Q42.cellsPlan_at_head
