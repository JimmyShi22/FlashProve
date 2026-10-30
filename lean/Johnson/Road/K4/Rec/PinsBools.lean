-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/PinsBools.lean: THE TWO LEAN STRUCTURES OF CONDITIONS ON THE PLAN's LETTERS
(`MaskPlan`, `CellPlan`: Johnson/Road/K4/Rec/Pins.lean) AS TESTS WITH CODE, for each the law "a yes
gives the structure", and the mask row's theorem under its test. THE TESTS STAND IN NO
`noncomputable section`. After the pattern, and in the two laws' proofs after the text, of
Johnson/Road/K4/MaskCellBools.lean, whose tests read a part of the verifier's state; its
`blocksOneB` and `blocksOne_of_B` are called.

  `maskPlanB A own R n m`, `maskPlan_of_B`. `maskEllP A`: the plan's length of the mask row: of the
    member that the test finds; 0 where it finds none.
  `cellPlanB A own R n m T r c`, `cellPlan_of_B`: AT ONE CELL. (No walk over all symbols stands
    here: it could not be evaluated at the full size: Johnson/Road/K4/Rec/Arrays.lean asks an array
    at a time.)
  **`mask_dataQ_B`**: a yes of `maskPlanB`, `RecIs a R n m`: `A.mask t j = (dataQ own a t.1).mask j`
    at every j below `maskEllP A`.

OBJECT: none of its own. USER: none yet; meant: the sheet that evaluates the conditions of K4's row
at the real plan, and whoever ties the table's item formsT m 3 "own" to the road's sentence on the
forms. LETTERS, filled by nobody: every field of `PinPlan`, tl, own, R, n, m.

Limits. NOTHING IS EVALUATED HERE. ONE DIRECTION: a yes gives the structure. `RecIs` IS A PREMISE
HERE. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on soundness.

-/
import Johnson.Road.K4.MaskCellBools
import Johnson.Road.K4.Rec.Pins

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open Johnson.Pack
open OnBytes.Model (HTailF2)
open Johnson.Road.K4.SeamBools (blocksOneB blocksOne_of_B)
open VerifiableInference.Desc.First.Look (sigListCalls seatCalls laidPlace messagesAt keptAt szOf)
open VerifiableInference.Desc.First.FillSent (whereIsP maskP)
open VerifiableInference.Desc.First.RecordPlan (seatP rowBitsP placeBitsP)
open VerifiableInference.Desc.Sound (dataQ)

variable {Cells : Type} (A : PinPlan Cells)

/-! ## The mask row -/

/-- The conditions of `MaskPlan`, with what they name found by the searches that they name. -/
def maskPlanB (own : List (ℕ × ℕ)) (R : RecPlan) (n m : ℕ) : Bool :=
  match (messagesAt A.D A.link).findIdx? fun x => x.shape.maskRows != 0 with
  | none => false
  | some mI =>
    if member : (keptAt A.D A.link).length + mI < (sigListCalls A.D A.rad A.link).length then
      decide (0 < ((sigListCalls A.D A.rad A.link).get ⟨_, member⟩).1.maskRows) &&
        match maskP R.shape R.d m with
        | none => false
        | some o =>
          decide (seatP own R.L.places n o = some (A.seatT ⟨_, member⟩)) &&
            decide (rowBitsP R.M n o .mask = 0)
    else false

/-- **A yes gives the structure.** -/
theorem maskPlan_of_B {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ}
    (h : maskPlanB A own R n m = true) : Nonempty (MaskPlan A own R n m) := by
  unfold maskPlanB at h
  split at h
  · cases h
  · rename_i mI hI
    split at h
    · rename_i member
      rw [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h⟩ := h
      split at h
      · cases h
      · rename_i o ho
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
        exact ⟨⟨mI, hI, member, h1, o, ho, h.1, h.2⟩⟩
    · cases h

/-- The plan's length of the mask row. -/
def maskEllP : ℕ :=
  match (messagesAt A.D A.link).findIdx? fun x => x.shape.maskRows != 0 with
  | none => 0
  | some mI =>
    if member : (keptAt A.D A.link).length + mI < (sigListCalls A.D A.rad A.link).length then
      (pMask A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨_, member⟩).1).ell
    else 0

theorem maskEllP_at {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ} (H : MaskPlan A own R n m) :
    maskEllP A = (pMask A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨_, H.member⟩).1).ell := by
  unfold maskEllP
  rw [H.first]
  exact dif_pos H.member

/-- **The two readings of the mask row are one**, at a yes of `maskPlanB`, under `RecIs`, below the
plan's length of the mask row. -/
theorem mask_dataQ_B {own : List (ℕ × ℕ)} {R : RecPlan} {n m : ℕ} {a : Part9}
    (hB : maskPlanB A own R n m = true) (h : RecIs a R n m) (t : PinM Cells) (j : ℕ)
    (hj : j < maskEllP A) : A.mask t j = (dataQ own a t.1).mask j := by
  obtain ⟨H⟩ := maskPlan_of_B A hB
  rw [maskEllP_at A H] at hj
  exact mask_dataQ_plan A H h t j hj

/-! ## A cell -/

/-- The conditions of `CellPlan`, with what they name found by the searches that they name. -/
def cellPlanB (own : List (ℕ × ℕ)) (R : RecPlan) (n m T r c : ℕ) : Bool :=
  match (A.D.arrayOf.getD A.link #[])[T]? with
  | none => false
  | some bn =>
    match OnBytes.reqArray A.D.layout bn.1 bn.2 with
    | none => false
    | some ar =>
      match laidPlace ar.blocks r c with
      | none => false
      | some rp =>
        match seatCalls A.D A.link (.cell T r c) with
        | none => false
        | some st =>
          decide (st = ⟨st.msg, false, rp.1, rp.2⟩) &&
            if member : st.msg < (sigListCalls A.D A.rad A.link).length then
              decide (rp.1 < ((sigListCalls A.D A.rad A.link).get ⟨st.msg, member⟩).1.mainRows) &&
                decide (rp.2 <
                  (pMain A.D.codes ((sigListCalls A.D A.rad A.link).get ⟨st.msg, member⟩).1).ell) &&
                decide (R.layout = A.D.layout) &&
                match whereIsP R.d m bn.1 ar.message with
                | none => false
                | some o =>
                  decide (seatP own R.L.places n o = some (A.seatT ⟨st.msg, member⟩)) &&
                    decide (rp.1 < 2 ^ rowBitsP R.M n o .main) &&
                    blocksOneB ar.blocks (rowBitsP R.M n o .main) (placeBitsP R.cs R.M n o .main)
            else false

/-- **A yes gives the structure.** -/
theorem cellPlan_of_B {own : List (ℕ × ℕ)} {R : RecPlan} {n m T r c : ℕ}
    (h : cellPlanB A own R n m T r c = true) : Nonempty (CellPlan A own R n m T r c) := by
  unfold cellPlanB at h
  split at h
  · cases h
  · rename_i bn hbn
    split at h
    · cases h
    · rename_i ar har
      split at h
      · cases h
      · rename_i rp hrp
        split at h
        · cases h
        · rename_i st hst
          rw [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨hs, h⟩ := h
          split at h
          · rename_i member
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨h1, h2⟩, h3⟩, h⟩ := h
            split at h
            · cases h
            · rename_i o ho
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              exact ⟨⟨bn, hbn, ar, har, rp, hrp, st.msg, hst.trans (congrArg some hs), member, h1,
                h2, h3, o, ho, h.1.1, h.1.2, blocksOne_of_B h.2⟩⟩
          · cases h

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.maskPlan_of_B
#print axioms OnBytes.Road.K4.Rec.cellPlan_of_B
#print axioms OnBytes.Road.K4.Rec.mask_dataQ_B
