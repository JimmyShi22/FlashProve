-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FitProofs.lean: the proofs of the statements of Johnson/Desc/K13/Law/Fit.lean.

No sumcheck is proved here. `row_iff` is algebra: both sides are written as the same sum.
`batt_doomed` is one call of the library's `Cb.Pv.BattShort.hAt`, at the powers of one element
(`Cb.ok_powers`), with `TWhole.short_outC` for what the library's verifier puts out.
Main names: `inHolds_iff`, `row_iff`, `batt_doomed`, `batt_errs`, `batt_vals`; on the way
`lhs_eq`, `target_val`, `masks_val`, `weights_val`, `whole_eq`.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/FitA.lean, FitB.lean and FitC.lean name;
`walk_hU`, `place` (OnBytes/Tie/Pv/Psc/StepWalk.lean), `walk_length`
(OnBytes/Tie/Pv/Psc/Run/PscPure.lean).

What is not claimed. What Johnson/Desc/K13/Law/Fit.lean says is not claimed.

-/
import Johnson.Desc.K13.Law.FitC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.L5.Layers (rd sRounds)
open OnBytes.Road.Hd (place walk_hU)

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {nR k : ℕ}

/-- The form of the claim q reads one entry: the value of the row's mask form. -/
theorem sum_slM (pile : List TensorRow) (q : Fin pile.length) (u : Unit)
    (m : (parOf ρ nR k pile).J → K) :
    ∑ j, (parOf ρ nR k pile).slM q u j * m j = m (.inr (.inr q)) := by
  show ∑ j : (Fin nR × (Fin k → Bool)) ⊕ (PIdx (fmtOf K k) ⊕ Fin pile.length), _ = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp

/-- The library's left side of the claim q is the row's. -/
theorem lhs_eq (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot)
    (q : Fin pile.length) :
    (parOf ρ nR k pile).lhs () q (msgOf ρ w pile fresh) = lhs ρ w (pile.get q) := by
  unfold BattPar.lhs
  rw [sum_slM]
  rfl

/-- All rows of the pile are true exactly if the library's input claim holds. -/
theorem inHolds_iff : Spec.inHolds_iff := by
  intro K _ _ ρ nR k w pile fresh
  constructor
  · intro h r hr
    obtain ⟨q, rfl⟩ := List.mem_iff_get.1 hr
    have := h q
    rw [lhs_eq] at this
    exact this
  · intro h q
    show (parOf ρ nR k pile).lhs () q (msgOf ρ w pile fresh) = targets ρ pile q
    rw [lhs_eq]
    exact h _ (List.get_mem _ _)

/-- The target of the sumcheck's claim, read. -/
theorem target_val (pile : List TensorRow) (x : E) :
    ρ.val (Batt.claimOf pile x).target =
      ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) * targets ρ pile q := by
  show ρ.val ((zipT (Psc.powers oneE x pile.length) pile).foldl
    (fun t p => addE t (mulE p.1 p.2.target)) zeroE) = _
  rw [zipT_eq, foldl_add ρ (fun p : E × TensorRow => mulE p.1 p.2.target), ρ.zero, zero_add]
  simp only [ρ.mul]
  rw [zip_powers_sum ρ x (fun r : TensorRow => ρ.val r.target) pile oneE]
  exact Finset.sum_congr rfl fun q _ => by rw [ρ.one, one_mul]; rfl

/-- The mask form of the sumcheck's claim, at the mask entries. -/
theorem masks_val (mask : Slot → K) (pile : List TensorRow) (x : E) :
    formVal ρ mask (Batt.claimOf pile x).masks =
      ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) * formVal ρ mask (pile.get q).masks := by
  show formVal ρ mask ((zipT (Psc.powers oneE x pile.length) pile).flatMap
    fun p => Psc.scaleForm p.1 p.2.masks) = _
  rw [zipT_eq, formVal_flatMap]
  simp only [formVal_scale]
  rw [zip_powers_sum ρ x (fun r : TensorRow => formVal ρ mask r.masks) pile oneE]
  exact Finset.sum_congr rfl fun q _ => by rw [ρ.one, one_mul]

/-- The weights of the row handed on. -/
theorem weights_val (nR : ℕ) {k : ℕ} (pile : List TensorRow) (x eps : E) (ch : List E)
    (hch : ch.length = k) (hpsi : ∀ r ∈ pile, r.psi.length = k) :
    weights ρ nR ((zipT pile (((Psc.powers oneE x pile.length).zip pile).map fun p =>
      mulE eps (mulE p.1 (eqEval p.2.psi ch)))).flatMap fun p => p.1.g.map fun t => t.scale p.2) =
    fun i => ∑ q : Fin pile.length, (ρ.val eps * (ρ.val x ^ (q : ℕ) *
      Alg.eqPt (rd ρ k (pile.get q).psi) (rd ρ k ch))) * weights ρ nR (pile.get q).g i := by
  funext i
  rw [zipT_eq, weights_flatMap]
  simp only [weights_scale]
  rw [zip_self x (fun p : E × TensorRow => mulE eps (mulE p.1 (eqEval p.2.psi ch)))
    (fun p : TensorRow × E => ρ.val p.2 * weights ρ nR p.1.g i) pile oneE]
  have e : (fun p : E × TensorRow =>
      ρ.val (mulE eps (mulE p.1 (eqEval p.2.psi ch))) * weights ρ nR p.2.g i) =
      fun p => ρ.val p.1 *
        (fun r : TensorRow => ρ.val eps * ρ.val (eqEval r.psi ch) * weights ρ nR r.g i) p.2 := by
    funext p
    simp only [ρ.mul]
    ring
  rw [e, zip_powers_sum ρ x
    (fun r : TensorRow => ρ.val eps * ρ.val (eqEval r.psi ch) * weights ρ nR r.g i) pile oneE]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ρ.one, eqEval_val ρ k _ ch (hpsi _ (List.get_mem _ _)) hch]
  ring

/-- The library's polynomial of the sumcheck, at a point, in the words of the rows. -/
theorem whole_eq (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot) (a ε : K)
    (X : HPt (varsOf K k)) :
    (parOf ρ nR k pile).par.whole ((), a) (msgOf ρ w pile fresh) ε X =
      hU (varsOf K k) (place (fun j => w.mask (fresh.getD j default)) (varsOf K k) 0) X +
        ε * (hPsi (varsOf K k) X *
          (∑ q : Fin pile.length, a ^ (q : ℕ) * formVal ρ w.mask (pile.get q).masks) +
          ∑ q : Fin pile.length, a ^ (q : ℕ) *
            Alg.eqPt (rd ρ k (pile.get q).psi) (hFnOf (pfCube K 2) k (pdPlains K 2 k) X) *
            Alg.mle (colOf w (weights ρ nR (pile.get q).g))
              (hFnOf (pfCube K 2) k (pdPlains K 2 k) X)) := by
  have hW : (parOf ρ nR k pile).par.W ((), a) (msgOf ρ w pile fresh) =
      place (fun j => w.mask (fresh.getD j default)) (varsOf K k) 0 := by
    funext i
    show place _ _ 0 ((pIx (fmtOf K k) (pdPlains K 2 k)).symm (pIx (fmtOf K k) (pdPlains K 2 k) i))
      = _
    rw [Equiv.symm_apply_apply]
  unfold PscPar.whole
  rw [BattPar.sum_eq, BattPar.inc_eq, hW]
  unfold BattPar.sumFn
  rw [zero_add]
  refine congrArg₂ (· + ·) rfl (congrArg (ε * ·) (congrArg₂ (· + ·)
    (congrArg (hPsi (varsOf K k) X * ·) (Finset.sum_congr rfl fun q _ => ?_)) rfl))
  rw [sum_slM]
  rfl

/-- The row handed on is true exactly if the library's output claim holds. -/
theorem row_iff : Spec.row_iff := by
  intro K _ _ ρ nR k w pile fresh Ex x h o hf hr
  obtain ⟨hl, h2, hfr, hpt, hmk, hmp, htg⟩ := run_fields hf hr
  obtain ⟨-, hk, hpsi⟩ := of_fits x hf
  have hch : (h.rounds.map (·.2)).length = k := by simp [hl]
  have hσ : ρ.val h.mu + ρ.val h.eps * ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) * targets ρ pile q =
      ρ.val (addE h.mu (mulE h.eps (Batt.claimOf pile x).target)) := by
    rw [ρ.add, ρ.mul, target_val]
  have hne : (wsOf k).zip (h.rounds.map (·.2)) ≠ [] := by
    intro e
    have := congrArg List.length e
    simp [hl] at this
    omega
  have hwl : (walkOf k h).1.length ≤ fresh.length := by
    have := OnBytes.Model.Road.walk_length (wsOf k) (h.rounds.map (·.2))
      (by intro e; have := congrArg List.length e; simp at this; omega) (by simp [hl])
      (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact (by decide : 1 ≤ 3))
    rw [this, hfr]
    simp [Psc.hidingEntries, Psc.Weight.plain]
    omega
  obtain ⟨a1, a2⟩ := walk_hU ρ (fun j => w.mask (fresh.getD j default)) _ (varsOf K k)
    (pH (fmtOf K k) (pdPlains K 2 k)
      (vOf ρ k (ρ.val (addE h.mu (mulE h.eps (Batt.claimOf pile x).target))) h.rounds).2) 0 hne
    (vOf_match ρ k h.rounds _ hl)
  have hz := zip_sumFrom ρ w.mask fresh (walkOf k h).1 0
    (fun j => w.mask (fresh.getD j default)) hwl (fun j _ => by rw [Nat.zero_add])
  have hfin := vOf_fin ρ k h.rounds (addE h.mu (mulE h.eps (Batt.claimOf pile x).target)) hl h2
  have hp := vOf_pt ρ k h.rounds
    (ρ.val (addE h.mu (mulE h.eps (Batt.claimOf pile x).target))) hl
  -- the left side
  have L : Holds ρ w (Batt.rowOf pile o) ↔
      Alg.mle (colOf w (weights ρ nR ((zipT pile o.rowMaps).flatMap fun p =>
        p.1.g.map fun t => t.scale p.2))) (rd ρ k o.point) + formVal ρ w.mask o.rowMasks =
        ρ.val o.rowTarget := Iff.rfl
  rw [L, hpt, hmk, htg, hmp, weights_val ρ nR pile x h.eps _ hch hpsi, mle_comb, formVal_append,
    formVal_scale, hz, a1, ρ.mul, a2, masks_val, ρ.sub, ρ.mul, ρ.zero, ← hfin]
  -- the right side
  have Rr : (parOf ρ nR k pile).par.MidHolds (outOf ρ nR pile Ex (trOf ρ nR pile Ex x h))
      (msgOf ρ w pile fresh) ↔
      (parOf ρ nR k pile).par.whole ((), ρ.val x) (msgOf ρ w pile fresh) (ρ.val h.eps)
        (pH (fmtOf K k) (pdPlains K 2 k) (vOf ρ k (ρ.val h.mu + ρ.val h.eps *
          ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) * targets ρ pile q) h.rounds).2) =
        (vOf ρ k (ρ.val h.mu + ρ.val h.eps *
          ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) * targets ρ pile q) h.rounds).1 := Iff.rfl
  rw [Rr, hσ, whole_eq, hp]
  have hA : ∑ q : Fin pile.length, (ρ.val h.eps * (ρ.val x ^ (q : ℕ) *
        Alg.eqPt (rd ρ k (pile.get q).psi) (rd ρ k (h.rounds.map (·.2))))) *
        Alg.mle (colOf w (weights ρ nR (pile.get q).g)) (rd ρ k (h.rounds.map (·.2))) =
      ρ.val h.eps * ∑ q : Fin pile.length, ρ.val x ^ (q : ℕ) *
        Alg.eqPt (rd ρ k (pile.get q).psi) (rd ρ k (h.rounds.map (·.2))) *
        Alg.mle (colOf w (weights ρ nR (pile.get q).g)) (rd ρ k (h.rounds.map (·.2))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hA]
  constructor <;> intro hh <;> linear_combination hh

/-- For each fixed witness the prover has lost, at the library's errors. -/
theorem batt_doomed : Spec.batt_doomed := by
  intro K _ _ ρ nR k w pile fresh Ex y hf
  have hK := Cb.Pv.BattShort.hAt (parOf ρ nR k pile) (le_refl 2) (ok_powers K pile.length) Ex
    (Wit K nR k) Unit Unit ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩
    (fun w => msgOf ρ w pile fresh) w
  refine Doomed.mono _ _ ?_ (hK ((targets ρ pile, ()), y) trivial)
  intro τ hτ x h o hx hr hrow
  have hout : (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).out (targets ρ pile, ()) y τ =
      some (outOf ρ nR pile Ex τ) := by
    show ((some ((parOf ρ nR k pile).nx (targets ρ pile, ()) (IOR.drawn (Tr.fst τ)))).bind fun x₂ =>
      (TWhole.shortRC (parOf ρ nR k pile).par (Cb.Pv.BattShort.F₁ (parOf ρ nR k pile)) Ex).out x₂ y
        (Tr.snd (s := [IOR.drawRound (parOf ρ nR k pile).Z.D]) τ)) = _
    rw [Option.bind_some, TWhole.short_outC _ _ Ex
      (Cb.Pv.BattShort.F₁_ok (parOf ρ nR k pile) (by norm_num))]
    rfl
  have hred : (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).red.out ((targets ρ pile, ()), y) τ =
      some (outOf ρ nR pile Ex τ, (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).imp y τ) := by
    show ((Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).out (targets ρ pile, ()) y τ).map _ = _
    rw [hout]
    rfl
  have hmid : (parOf ρ nR k pile).par.MidHolds (outOf ρ nR pile Ex τ) (msgOf ρ w pile fresh) := by
    rw [← hx]
    exact (row_iff K ρ nR k w pile fresh Ex x h o hf hr).1 hrow
  exact (inHolds_iff K ρ nR k w pile fresh).1 (hτ _ () hred ⟨trivial, hmid⟩).2

/-- The errors, round by round. -/
theorem batt_errs : Spec.batt_errs := fun _ _ _ ρ nR k pile Ex =>
  Cb.Pv.BattShort.errs (parOf ρ nR k pile) Ex

/-- The numbers of values of the challenges, round by round. -/
theorem batt_vals : Spec.batt_vals := fun _ _ _ ρ nR k pile Ex =>
  Cb.Pv.BattShort.vals (parOf ρ nR k pile) Ex

end VerifiableInference.Desc.K13.Law
