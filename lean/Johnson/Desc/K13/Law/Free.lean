-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Free.lean: with the witness free behind the draws, the batching's bound is
false. Statements with their proofs.

`batt_doomed` (Johnson/Desc/K13/Law/Fit.lean) bounds the bad draws for each fixed witness. Here the
same bound is written with the witness behind all draws (`FreeAt`), and refuted: so the premise of
the law that the pin fixes what is read of a witness (Johnson/Desc/K13/Law/Law.lean) cannot be
dropped.
Main names:
  `run_some`: where the sizes fit, `Psc.run` returns: none of its tests is on a value.
  `FreeAt ρ nR k`; `pile1`, `fresh1`, `wit1`: one row over one column variable, with the target 1;
    the matrix 0, and the hiding polynomial's constant as the one mask entry that is not 0.
  `not_free`, `not_free_gl`: at every transcript the witness whose constant is the last value meets
    the row handed on and fails the pile's row.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/FitC.lean names.

What is not claimed. The refutation is at one column variable and a pile of one row.

-/
import Johnson.Desc.K13.Law.Pin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Prob
open Johnson.L5.Layers (rd sRounds)
open OnBytes.Road.Hd (place powers_len)

/-- **Where the sizes fit, the run returns**: no test of `Psc.run` is on a value. -/
theorem run_some {k : ℕ} {pile : List TensorRow} {x : E} {fresh : List Slot} {h : Psc.Heard}
    (hf : Batt.fits k pile = true) (hfr : fresh.length = 1 + 2 * k) (hl : h.rounds.length = k)
    (h2 : ∀ p ∈ h.rounds, p.1.length = 2) (hv : h.values = []) :
    ∃ o, Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o := by
  obtain ⟨hcv, hk, -⟩ := of_fits x hf
  have hvs : Psc.varsOf (Batt.claimOf pile x) (Batt.summandOf pile x) = wsOf k := by
    rw [← hcv]
    rfl
  have hm : Psc.masksOf (Batt.claimOf pile x) (Batt.summandOf pile x) = 1 + 2 * k := by
    unfold Psc.masksOf
    rw [hvs]
    simp [Psc.hidingEntries, Batt.summandOf, Psc.Weight.plain]
    omega
  have hform : Psc.formOK (Batt.claimOf pile x) (Batt.summandOf pile x) = true := by
    unfold Psc.formOK
    rw [hcv]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [Batt.summandOf, Psc.Weight.fits, Psc.Weight.plain, List.replicate_succ]
  unfold Psc.run
  simp only [hvs, hm, hcv]
  rw [if_pos]
  · exact ⟨_, rfl⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.length_replicate]
    refine ⟨⟨⟨⟨⟨hform, hfr⟩, hl⟩, by rw [hv]; rfl⟩, ?_⟩, fun p hp => ?_⟩
    · simp [Batt.summandOf, Batt.chiOf, zipT_eq, powers_len]
      omega
    · obtain ⟨h1, h3⟩ := List.of_mem_zip hp
      rw [List.eq_of_mem_replicate h1, h2 _ h3]
      rfl

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The bound of `batt_doomed` with the witness behind the draws. -/
def FreeAt (nR k : ℕ) : Prop :=
  ∀ (pile : List TensorRow) (fresh : List Slot) (Ex : ExtSpec) (_ : Ex.Str),
    Batt.fits k pile = true →
    Doomed (Cb.Pv.BattShort.R (parOf ρ nR k pile) Ex).shape
      (Cb.Pv.BattShort.eps (parOf ρ nR k pile) Ex)
      fun τ => ∀ (x : E) (h : Psc.Heard) (o : Psc.Out), trOf ρ nR pile Ex x h = τ →
        Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o →
        ∀ w : Wit K nR k, Holds ρ w (Batt.rowOf pile o) → ∀ r ∈ pile, Holds ρ w r

/-- A pile of one row over one column variable, with the target 1. -/
def pile1 : List TensorRow := [⟨[{}], [zeroE], [], oneE⟩]

/-- Three mask entries. -/
def fresh1 : List Slot := [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩]

/-- The matrix 0, and one mask entry: the hiding polynomial's constant. -/
def wit1 (nR : ℕ) (c : K) : Wit K nR 1 := ⟨fun _ _ => 0, fun s => if s = ⟨0, 0⟩ then c else 0⟩

omit [Fintype K] in
/-- Over the matrix 0 every tensor part is 0. -/
theorem mle_zero_mat {nR : ℕ} (c : K) (v : Fin nR → K) (z : Fin 1 → K) :
    Alg.mle (colOf (wit1 nR c) v) z = 0 := by
  simp [Alg.mle, colOf, wit1]

/-- The hiding polynomial whose constant is c and whose other coefficients are 0 is c. -/
theorem hU_wit1 (nR : ℕ) (c : K) (X : HPt (varsOf K 1)) :
    hU (varsOf K 1) (place (fun j => (wit1 nR c).mask (fresh1.getD j default)) (varsOf K 1) 0) X
      = c := by
  show hPsi ([] : List (HVar K)) X.2 • hev (Fin.cons 0 fun t : Fin 2 =>
      (wit1 nR c).mask (fresh1.getD (0 + 1 + (t : ℕ)) default) : Fin 3 → K) X.1 +
    (wit1 nR c).mask (fresh1.getD 0 default) = c
  rw [OnBytes.Road.Hd.hev_cons, Fin.sum_univ_two]
  simp [wit1, fresh1]

variable (σ : K → E) (hσ : ∀ a, ρ.val (σ a) = a)

include hσ in
/-- **With the witness free behind the draws the bound is false**: at every transcript some witness
meets the row handed on and fails the pile's row. -/
theorem not_free (nR : ℕ) (h3 : 2 < Fintype.card K) (Ex : ExtSpec) (y : Ex.Str) :
    ¬ FreeAt ρ nR 1 := by
  intro h
  have hf : Batt.fits 1 pile1 = true := rfl
  refine not_doomed _ _ _ (below_eps ρ nR 1 pile1 Ex h3 (by simp [pile1]; omega))
    (fun τ hbad => ?_) (h pile1 fresh1 Ex y hf)
  obtain ⟨m0, c, m1, e, τ'⟩ := τ
  obtain ⟨o, ho⟩ := run_some (x := σ c) (fresh := fresh1)
    (h := ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩) hf rfl rfl
    (fun p hp => by
      obtain ⟨m2, g, u⟩ := τ'
      obtain rfl := List.mem_singleton.1 hp
      rfl) rfl
  have htr : trOf ρ nR pile1 Ex (σ c) ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩ =
      (m0, c, m1, e, τ') := by
    show (((), ()), ρ.val (σ c), ((), ρ.val (σ m1.2)), ρ.val (σ e),
      trRounds ρ 1 (backRounds σ 1 τ')) = _
    rw [hσ, hσ, hσ, tr_back ρ σ hσ]
    rfl
  have hrow := fun w => row_iff K ρ nR 1 w pile1 fresh1 Ex (σ c)
    ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩ o hf ho
  have hfalse : ∀ a : K, ¬ Holds ρ (wit1 nR a) (⟨[{}], [zeroE], [], oneE⟩ : TensorRow) := by
    intro a hh
    have h1 : Alg.mle (colOf (wit1 nR a) (weights ρ nR [{}])) (rd ρ 1 [zeroE]) +
        formVal ρ (wit1 nR a).mask [] = ρ.val oneE := hh
    rw [mle_zero_mat, ρ.one] at h1
    simp [formVal] at h1
  obtain ⟨z, hz⟩ : ∃ z : (parOf ρ nR 1 pile1).par.Mid, z = outOf ρ nR pile1 Ex
      (trOf ρ nR pile1 Ex (σ c) ⟨σ m1.2, σ e, backRounds σ 1 τ', []⟩) := ⟨_, rfl⟩
  have hq : ∀ q : Fin pile1.length, (pile1.get q).masks = [] := by
    intro q
    have hm : pile1.get q ∈ pile1 := List.get_mem _ _
    rw [List.mem_singleton.1 hm]
  have hw := whole_eq ρ (wit1 nR z.fin) pile1 fresh1 (ρ.val (σ c)) (ρ.val (σ e))
    (pH (fmtOf K 1) (pdPlains K 2 1) z.pt)
  rw [hU_wit1] at hw
  simp only [mle_zero_mat, hq, formVal, List.map_nil, List.sum_nil, mul_zero,
    Finset.sum_const_zero, add_zero] at hw
  have hmid : (parOf ρ nR 1 pile1).par.MidHolds z (msgOf ρ (wit1 nR z.fin) pile1 fresh1) := by
    rw [hz] at hw ⊢
    exact hw
  rw [hz] at hmid
  exact hfalse _ (hbad (σ c) _ o htr ho _ ((hrow _).2 hmid) _ (List.mem_singleton.2 rfl))

/-- The same at the release's own reading, without a premise. -/
theorem not_free_gl (nR : ℕ) : ¬ FreeAt ρg nR 1 :=
  not_free ρg (fun a => E.ofTriple (OnBytes.Slice.ofE a)) gl_section nR gl_three extNone ()

end VerifiableInference.Desc.K13.Law
