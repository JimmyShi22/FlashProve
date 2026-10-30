-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealErrs.lean: K10's law at the real written rounds: that the cap bears
the proved block's own errors, from k + 2 clauses on numbers.

Why. K10's law at a piece asks `ρ.carS.Fits (Tower.batFoldErrRide ..) (Err.cap 128 ..)`. The proved
block's errors are a term whose parts Lean's elaborator does not reach in time; the library says
what they are AS A LIST (`errRide_toList`, `fold_errList`, Cb/Pv/Tower/Fold.lean). So the counts are
asked along that list.
  `real_fits_list`: at any errors ε of the typed shape: if along the list of ε's entries each is
  held at its written round (`HeldAt` at 2⁻¹ ^ 128, Law/RealCount.lean: "BAT", "FOLD epsilon", k
  times "FOLD round"), the cap bears ε.
  `batFold_errList`: the proved block's errors as a list: the list bound times the evader's number;
  Lst 0; then, for i < k, mC (i + 1) + (mS (i + 1) + mW (i + 1) while i + 1 ≤ h) + Lst i * n.
  `real_fits_batFold`: so the cap bears the proved block's errors if these k + 2 numbers are held.
Limits. Numbers: that the k + 2 numbers are so held at the release's values is the row on K10's
rounds: not shown here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Close.Law.RealCount
import Cb.Pv.Tower.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop Prob Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv

/-- Held along the list of k entries. -/
theorem heldAll_of_list {εs : ℝ≥0∞} {d : RDT} {r' : Round} :
    ∀ (k : ℕ) (ε : Err (List.replicate k r')),
      List.Forall₂ (HeldAt εs) (List.replicate k d) ε.toList → HeldAll εs d k ε
  | 0, _, _ => trivial
  | k + 1, (e, ε), h => by
    have h' : List.Forall₂ (HeldAt εs) (d :: List.replicate k d) (e :: ε.toList) := h
    obtain ⟨h1, h2⟩ := List.forall₂_cons.1 h'
    exact ⟨h1, heldAll_of_list k ε h2⟩

/-- One written round against every member of a list. -/
theorem forall₂_replicate {α β : Type} (P : α → β → Prop) (a : α) :
    ∀ l : List β, (∀ b ∈ l, P a b) → List.Forall₂ P (List.replicate l.length a) l
  | [], _ => .nil
  | b :: l, h =>
    .cons (h b (List.mem_cons_self ..))
      (forall₂_replicate P a l fun x hx => h x (List.mem_cons_of_mem _ hx))

variable {c : BatFoldCaller GE} {dB dE dR : RDT} {rdZ : List E → Option c.s.Z.D}
  {rdCh : List E → Option (Yc c).Ch}

/-- **Held along the list of its entries, any list of typed errors is borne by the cap.** -/
theorem real_fits_list (H : RealReads c dB dE dR rdZ rdCh)
    (ε : Err (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).shape)
    (h : List.Forall₂ (HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128)) (dB :: dE :: List.replicate (Yc c).k dR)
      ε.toList) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits ε
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) := by
  obtain ⟨eB, eE, εK⟩ := ε
  have h' : List.Forall₂ (HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128))
      (dB :: dE :: List.replicate (Yc c).k dR)
      (eB :: eE :: Err.toList (s := List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n))
        εK) := h
  obtain ⟨hB, h2⟩ := List.forall₂_cons.1 h'
  obtain ⟨hE, hR⟩ := List.forall₂_cons.1 h2
  exact real_fits_held H eB eE εK hB hE (heldAll_of_list _ εK hR)

/-- The proved block's errors, as a list. -/
theorem batFold_errList (c : BatFoldCaller GE) (Lst mC mS mW : ℕ → ℕ) :
    (Tower.batFoldErrRide (St₀ := c.St₀) (E₀ := c.E₀) c.s c.Sh c.fx Lst mC mS mW).toList =
      c.s.L * c.s.Z.err :: Lst 0 :: (List.range (Yc c).k).map fun i =>
        mC (i + 1) + (if i + 1 ≤ (Yc c).h then mS (i + 1) + mW (i + 1) else 0) +
          Lst i * (Yc c).n :=
  (congrArg (List.cons (c.s.L * c.s.Z.err))
    (Tower.errRide_toList (Yc c) c.fx Lst mC mS mW)).trans
    (congrArg (List.cons (c.s.L * c.s.Z.err)) (Tower.fold_errList (Yc c) Lst mC mS mW))

/-- **The cap bears the proved block's errors, if k + 2 numbers are held.** -/
theorem real_fits_batFold (H : RealReads c dB dE dR rdZ rdCh) (Lst mC mS mW : ℕ → ℕ)
    (hB : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dB (c.s.L * c.s.Z.err))
    (hE : HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dE (Lst 0))
    (hR : ∀ i, i < (Yc c).k → HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128) dR
      (mC (i + 1) + (if i + 1 ≤ (Yc c).h then mS (i + 1) + mW (i + 1) else 0) +
        Lst i * (Yc c).n)) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits
      (Tower.batFoldErrRide (St₀ := c.St₀) (E₀ := c.E₀) c.s c.Sh c.fx Lst mC mS mW)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) := by
  refine real_fits_list H _ ?_
  rw [batFold_errList]
  refine .cons hB (.cons hE ?_)
  have h1 := forall₂_replicate (HeldAt ((2 : ℝ≥0∞)⁻¹ ^ 128)) dR
    ((List.range (Yc c).k).map fun i =>
      mC (i + 1) + (if i + 1 ≤ (Yc c).h then mS (i + 1) + mW (i + 1) else 0) +
        Lst i * (Yc c).n) (fun b hb => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      exact hR i (List.mem_range.1 hi))
  rwa [List.length_map, List.length_range] at h1

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.real_fits_list
#print axioms VerifiableInference.Desc.First.Close.batFold_errList
#print axioms VerifiableInference.Desc.First.Close.real_fits_batFold
