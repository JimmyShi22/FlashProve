-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RealPaid.lean: that the cap bears the proved block's errors at K10's
real written rounds, from the clause in which the counts of a fold are priced.

The counts of a folded stage are priced in Johnson/Bridge/FoldPriced.lean: `RoundBelow n d εs`
(OnBytes/Slice/ManyErr.lean): n times the sampler's number is at most εs times the round's written
verifier messages. That is, by its make, the entry of `Err.Below` which `real_fits_cap`
(Law/RealRounds.lean) asks at that round. So the road goes straight, not through `HeldAt`.
  `RoundAll`, `real_fits_round`, `real_fits_listR`, `real_fits_batFoldR`, `real_fits_callerR`:
  Law/RealCount.lean's, RealErrs.lean's and RealCaller.lean's theorems with `RoundBelow` in the
  place of `HeldAt`. At the caller the count with mask rows is asked only where the fold has a round
  with mask rows.
  `real_fits_caller_of_paid`: at a priced place x (`FoldedPlace.Paid`) with the caller's stage and
  radius, whose two counts are at least the caller's: the premise hFit of K10's law at a piece, up
  to the clause at "BAT". That a round sends two scalars and which rounds fold mask rows are read
  off the caller's own text (`yc_n`, `yc_h`).
Limits. That the description's K10 stands at a place that is priced, that its written rounds are the
format's own, and the clause at "BAT" are premises. This file rests, through FoldPriced.lean, on the
files under ThirdParty/ (lean/LIMITS.md, L15).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Close.Law.RealCaller
import Johnson.Bridge.FoldPriced

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker Iop IOR Prob Run
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

/-- Each of k typed counts meets the clause at the written round d. -/
def RoundAll (εs : ℝ≥0∞) (d : RDT) {r' : Round} : ∀ k : ℕ, Err (List.replicate k r') → Prop
  | 0, _ => True
  | k + 1, (e, ε) => RoundBelow e (toRD d) εs ∧ RoundAll εs d k ε

theorem RoundAll.below {εs : ℝ≥0∞} {d : RDT} {r' : Round} :
    ∀ (k : ℕ) (ε : Err (List.replicate k r')), RoundAll εs d k ε →
      Err.Below (s := List.replicate k (wT d)) (timesW (bsRound .two d.entry d.kind).w k ε) εs
  | 0, _, _ => trivial
  | k + 1, (_, ε), h => ⟨h.1, RoundAll.below k ε h.2⟩

theorem roundAll_of_list {εs : ℝ≥0∞} {d : RDT} {r' : Round} :
    ∀ (k : ℕ) (ε : Err (List.replicate k r')),
      List.Forall₂ (fun d e => RoundBelow e (toRD d) εs) (List.replicate k d) ε.toList →
        RoundAll εs d k ε
  | 0, _, _ => trivial
  | k + 1, (e, ε), h => by
    have h' : List.Forall₂ (fun d e => RoundBelow e (toRD d) εs) (d :: List.replicate k d)
        (e :: ε.toList) := h
    obtain ⟨h1, h2⟩ := List.forall₂_cons.1 h'
    exact ⟨h1, roundAll_of_list k ε h2⟩

section
variable {c : BatFoldCaller GE} {dB dE dR : RDT} {rdZ : List E → Option c.s.Z.D}
  {rdCh : List E → Option (Yc c).Ch}

/-- **Priced round by round at 2⁻¹ ^ 128, the typed counts are borne by the cap.** -/
theorem real_fits_round (H : RealReads c dB dE dR rdZ rdCh) (eB eE : ℕ)
    (εK : Err (List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n)))
    (hB : RoundBelow eB (toRD dB) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hE : RoundBelow eE (toRD dE) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hR : RoundAll ((2 : ℝ≥0∞)⁻¹ ^ 128) dR (Yc c).k εK) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits (eB, eE, εK)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) :=
  real_fits_cap H eB eE εK ⟨hB, hE, RoundAll.below _ εK hR⟩

theorem real_fits_listR (H : RealReads c dB dE dR rdZ rdCh)
    (ε : Err (Tower.batFoldRide c.s c.Sh c.fx c.St₀ c.E₀).shape)
    (h : List.Forall₂ (fun d e => RoundBelow e (toRD d) ((2 : ℝ≥0∞)⁻¹ ^ 128))
      (dB :: dE :: List.replicate (Yc c).k dR) ε.toList) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits ε
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) := by
  obtain ⟨eB, eE, εK⟩ := ε
  have h' : List.Forall₂ (fun d e => RoundBelow e (toRD d) ((2 : ℝ≥0∞)⁻¹ ^ 128))
      (dB :: dE :: List.replicate (Yc c).k dR)
      (eB :: eE :: Err.toList (s := List.replicate (Yc c).k (Cb.sRoundS GE (Yc c).Ch (Yc c).n))
        εK) := h
  obtain ⟨hB, h2⟩ := List.forall₂_cons.1 h'
  obtain ⟨hE, hR⟩ := List.forall₂_cons.1 h2
  exact real_fits_round H eB eE εK hB hE (roundAll_of_list _ εK hR)

theorem real_fits_batFoldR (H : RealReads c dB dE dR rdZ rdCh) (Lst mC mS mW : ℕ → ℕ)
    (hB : RoundBelow (c.s.L * c.s.Z.err) (toRD dB) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hE : RoundBelow (Lst 0) (toRD dE) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hR : ∀ i, i < (Yc c).k → RoundBelow
      (mC (i + 1) + (if i + 1 ≤ (Yc c).h then mS (i + 1) + mW (i + 1) else 0) +
        Lst i * (Yc c).n) (toRD dR) ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    (realRd c dB dE dR rdZ rdCh).carS.Fits
      (Tower.batFoldErrRide (St₀ := c.St₀) (E₀ := c.E₀) c.s c.Sh c.fx Lst mC mS mW)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc c).k (wT dR))) := by
  refine real_fits_listR H _ ?_
  rw [batFold_errList]
  refine .cons hB (.cons hE ?_)
  have h1 := forall₂_replicate (fun d e => RoundBelow e (toRD d) ((2 : ℝ≥0∞)⁻¹ ^ 128)) dR
    ((List.range (Yc c).k).map fun i =>
      mC (i + 1) + (if i + 1 ≤ (Yc c).h then mS (i + 1) + mW (i + 1) else 0) +
        Lst i * (Yc c).n) (fun b hb => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
      exact hR i (List.mem_range.1 hi))
  rwa [List.length_map, List.length_range] at h1

end

variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

local notation "cc" => RowsK.foldCaller R keep Sb sl Z fx A₀ bC bZ w₀ w₁

/-- At the caller on a group with kept rows. -/
theorem real_fits_callerR {dB dE dR : RDT} {rdZ : List E → Option (cc).s.Z.D}
    {rdCh : List E → Option (Yc cc).Ch} (H : RealReads cc dB dE dR rdZ rdCh)
    (hB : RoundBelow ((cc).s.L * (cc).s.Z.err) (toRD dB) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hE : RoundBelow (lstJ R.s R.e) (toRD dE) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hLow : (Yc cc).h ≠ 0 → RoundBelow (bC + (bZ + bZ) + lstJ R.s R.e * (Yc cc).n) (toRD dR)
      ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (hHigh : RoundBelow (bC + 0 + lstJ R.s R.e * (Yc cc).n) (toRD dR) ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    (realRd cc dB dE dR rdZ rdCh).carS.Fits
      (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx (fun _ => lstJ R.s R.e) (fun _ => bC)
        (fun _ => bZ) fun _ => bZ)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc cc).k (wT dR))) :=
  real_fits_batFoldR H (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) hB hE
    fun i _ => by
      by_cases h : i + 1 ≤ (Yc cc).h
      · rw [if_pos h]
        exact hLow (by omega)
      · rw [if_neg h]
        exact hHigh

/-- At this caller a round of the fold sends two scalars. -/
theorem yc_n : (Yc cc).n = 2 := rfl

/-- At this caller the fold's rounds with mask rows are the stage's. -/
theorem yc_h : (Yc cc).h = R.s.h := rfl

/-- **From a priced place.** -/
theorem real_fits_caller_of_paid {dB dE dR : RDT} {rdZ : List E → Option (cc).s.Z.D}
    {rdCh : List E → Option (Yc cc).Ch} (H : RealReads cc dB dE dR rdZ rdCh)
    (x : Johnson.Bridge.FoldedPlace) (hx : x.Paid) (hs : x.s = R.s) (he : x.e = R.e)
    (hC : bC ≤ x.bC) (hZ : bZ ≤ x.bZ)
    {na nb : String} (iE : IsRd (toRD dE) (Fmt.M1.rEps na)) (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (hB : RoundBelow ((cc).s.L * (cc).s.Z.err) (toRD dB) ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    (realRd cc dB dE dR rdZ rdCh).carS.Fits
      (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx (fun _ => lstJ R.s R.e) (fun _ => bC)
        (fun _ => bZ) fun _ => bZ)
      (Err.cap 128 (wT dB :: wT dE :: List.replicate (Yc cc).k (wT dR))) := by
  have el : x.lst = lstJ R.s R.e := by
    unfold Johnson.Bridge.FoldedPlace.lst
    rw [hs, he]
    rfl
  have hn : (Yc cc).n ≤ 2 := le_of_eq (yc_n R keep Sb sl Z fx A₀ bC bZ w₀ w₁)
  have hh : (Yc cc).h ≠ 0 → x.s.h ≠ 0 := fun h0 => by
    rw [hs, ← yc_h R keep Sb sl Z fx A₀ bC bZ w₀ w₁]
    exact h0
  refine real_fits_callerR R keep Sb sl Z fx A₀ bC bZ w₀ w₁ H hB ?_ (fun h0 => ?_) ?_
  · rw [← el]
    exact hx.eps _ _ iE
  · rw [← el]
    exact RoundBelow.mono
      (Nat.add_le_add (Nat.add_le_add hC (Nat.add_le_add hZ hZ)) (Nat.mul_le_mul_left _ hn))
      (hx.mask (hh h0) _ _ iR)
  · rw [← el]
    exact RoundBelow.mono
      (Nat.add_le_add (by rw [Nat.add_zero]; exact hC) (Nat.mul_le_mul_left _ hn))
      (hx.plain _ _ iR)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.yc_n
#print axioms VerifiableInference.Desc.First.Close.yc_h
#print axioms VerifiableInference.Desc.First.Close.real_fits_round
#print axioms VerifiableInference.Desc.First.Close.real_fits_batFoldR
#print axioms VerifiableInference.Desc.First.Close.real_fits_callerR
#print axioms VerifiableInference.Desc.First.Close.real_fits_caller_of_paid
