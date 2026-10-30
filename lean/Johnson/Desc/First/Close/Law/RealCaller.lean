-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealCaller.lean: that the cap bears the proved block's errors, at the
caller on a group with kept rows: from four clauses on numbers.

`real_fits_batFold` (Law/RealErrs.lean) at `RowsK.foldCaller` (Johnson/Top/H/CallerKept.lean), whose
lists and counts do not hang on the round: Lst is the Johnson bound's list size `lstJ R.s R.e`, mC
is bC, mS and mW are bZ. So the k numbers of the "FOLD round"s take two values.
  `real_fits_caller`: the premise hFit of K10's law at a piece (Law/AtPiece.lean), in its own
  letters, from `RealReads` and: the list bound times the evader's number is held at "BAT"; the list
  size at "FOLD epsilon"; bC + (bZ + bZ) + list size * n and bC + 0 + list size * n at "FOLD round"
  (`HeldAt` at 2⁻¹ ^ 128, Law/RealCount.lean).
Limits. Numbers: that the four are so held at the release's values is the row on K10's rounds: not
shown here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Close.Law.RealErrs
import Johnson.Top.H.CallerKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop IOR Prob Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

local notation "cc" => RowsK.foldCaller R keep Sb sl Z fx A₀ bC bZ w₀ w₁

/-- **The cap bears the proved block's errors at this caller, if four numbers are held.** -/
theorem real_fits_caller {dB dE dR : RDT} {rdZ : List E → Option (cc).s.Z.D}
    {rdCh : List E → Option (Yc cc).Ch} (H : RealReads cc dB dE dR rdZ rdCh)
    (hB : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dB ((cc).s.L * (cc).s.Z.err))
    (hE : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dE (lstJ R.s R.e))
    (hLow : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dR (bC + (bZ + bZ) + lstJ R.s R.e * (Yc cc).n))
    (hHigh : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dR (bC + 0 + lstJ R.s R.e * (Yc cc).n)) :
    (realRd cc dB dE dR rdZ rdCh).carS.Fits
      (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx (fun _ => lstJ R.s R.e) (fun _ => bC)
        (fun _ => bZ) fun _ => bZ)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc cc).k (wT dR))) :=
  real_fits_batFold H (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) hB hE
    fun i _ => by
      by_cases h : i + 1 ≤ (Yc cc).h
      · rw [if_pos h]
        exact hLow
      · rw [if_neg h]
        exact hHigh

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.real_fits_caller
