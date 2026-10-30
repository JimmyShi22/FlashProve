--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/LibBackNorm.lean: THE WAY BACK, THE FINAL NORMALISATION's HALF: from the
clause on keys of the library's field relation of the head with the cost ledger
(Policy/Rel/LedgerHead.lean: RF.keys), at the library's record made of the kind's cells (cellsN c,
Law/LibJoinNorm.lean), to the four fields of the kind's relation CellRelN (HeadNormLaw.lean) that
speak of keys. Statements and proofs. NO ACCEPTANCE OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Law/LibJoinNorm.lean's normOwn_of_cellRelN leads from CellRelN to the library's clauses: what
soundness spends; its head lists the converse under what it does not say. Whoever wants to show that
honest cells stand in the kind's relation needs the other way. That file's identities between
integers (xv_eq, Dv_eq, nw_eq, rn_eq, nrm_eq, Dv_at) and Law/NormProof.lean's values of the four
keys (rd_keyN_remLow, rd_keyN_remHigh, rd_keyN_clamp, rd_keyN_digits) are equations: here they are
read backwards. No integer's range is wanted: a key that is read as a number's image IS that image
(Law/TableTie.lean: eq_natCast_of_rd).

Main names.
  remLow_back, remHigh_back, clamp_back, digits_back   field by field.
  normKeys_back   the four together.

Limits. ONE WAY: from the library's clause to the kind's four fields. The fields small, smallS and
rows of CellRelN are not spoken of. T = 1024, d = 5120 and "a block's size divides d" are premises:
the full size alone. H and Y are letters: these four keys read neither. That cellsN c is what any
committed integers spell is not said. No chance in it.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Kinds.Law.LibJoinNorm
import Johnson.Desc.Kinds.Law.TableTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.HeadJoin

open Finset
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open Inst.Model (NormPar)

section Field
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] {c : Law.NCells}
  {H : ℕ → ℕ → ℤ} {Y : Inst.Model.Head.Req}

/-- The low key of the rounding. -/
theorem remLow_back (hT : Norm.T = 1024) (hd : Norm.d = 5120) (hS : Norm.S2 ∣ Norm.d)
    (R : Policy.LedgerHead.RF Law.npOf (fun j v => ((H j v : ℤ) : Law.K)) Y (cellsN c)) :
    ∀ t, t < Norm.T → ∀ x, x < Norm.d → Law.InBits 16 (Law.keyNAt c (Law.cornerN x t) .remLow) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← hT]; exact ht
  have hx5 : x < 5120 := by rw [← hd]; exact hx
  have k := R.keys .NF x t hx5 hi
  rw [keyN_cast] at k
  obtain ⟨n, hn, e⟩ := k
  have e0 : ((Inst.Model.Head.xv (cellsN c) x t *
      Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv (cellsN c) n t) +
      2 ^ (FinalNorm.KF - 1) - 2 ^ FinalNorm.KF * Inst.Model.Head.nw (cellsN c) x t -
      2 ^ 16 * Inst.Model.Head.rn (cellsN c) x t : ℤ) : Law.K) = (((n : ℕ) : ℤ) : Law.K) := e
  rw [xv_eq hd, Dv_eq, nw_eq hd, rn_eq hd, Int.cast_natCast] at e0
  refine ⟨n, hn, Law.Came.eq_natCast_of_rd (Law.Came.okE_keyNAt _ _ _) ?_⟩
  rw [Law.rd_keyN_remLow ht hS hx]
  exact e0

/-- The high key of the rounding. -/
theorem remHigh_back (hT : Norm.T = 1024) (hd : Norm.d = 5120) (hS : Norm.S2 ∣ Norm.d)
    (R : Policy.LedgerHead.RF Law.npOf (fun j v => ((H j v : ℤ) : Law.K)) Y (cellsN c)) :
    ∀ t, t < Norm.T → ∀ x, x < Norm.d →
      Law.InBits 16 (Law.keyNAt c (Law.cornerN x t) .remHigh) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← hT]; exact ht
  have hx5 : x < 5120 := by rw [← hd]; exact hx
  have k := R.keys .NFH x t hx5 hi
  rw [keyN_cast] at k
  obtain ⟨n, hn, e⟩ := k
  have e0 : ((((2 ^ (32 - FinalNorm.KF) : ℕ) : ℤ) * Inst.Model.Head.rn (cellsN c) x t : ℤ) :
      Law.K) = (((n : ℕ) : ℤ) : Law.K) := e
  have e2 : ((2 ^ (32 - FinalNorm.KF) : ℕ) : ℤ) * Law.remZ c t x =
      Inst.Model.Site.high (Law.remZ c t x) FinalNorm.KF 32 := by
    simp [Inst.Model.Site.high]
  rw [rn_eq hd, e2, Int.cast_natCast] at e0
  refine ⟨n, hn, Law.Came.eq_natCast_of_rd (Law.Came.okE_keyNAt _ _ _) ?_⟩
  rw [Law.rd_keyN_remHigh ht hS hx]
  exact e0

/-- The clamp's key. -/
theorem clamp_back (hT : Norm.T = 1024) (hd : Norm.d = 5120) (hS : Norm.S2 ∣ Norm.d)
    (R : Policy.LedgerHead.RF Law.npOf (fun j v => ((H j v : ℤ) : Law.K)) Y (cellsN c)) :
    ∀ t, t < Norm.T → ∀ x, x < Norm.d → Law.IsClampRow (Law.keyNAt c (Law.cornerN x t) .clamp) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← hT]; exact ht
  have hx5 : x < 5120 := by rw [← hd]; exact hx
  have k := R.keys .CNF x t hx5 hi
  rw [keyN_cast] at k
  obtain ⟨u, hu, e⟩ := k
  have e0 : (((Inst.Model.Head.nw (cellsN c) x t + 2 ^ 15) +
      2 ^ 28 * (Inst.Model.Head.nrm (cellsN c) x t + 2 ^ 11) : ℤ) : Law.K) =
      (((u : ℤ) + 2 ^ 28 * (Inst.Model.clamp 2047 ((u : ℤ) - 2 ^ 15) + 2 ^ 11) : ℤ) : Law.K) := e
  rw [nw_eq hd, nrm_eq hd] at e0
  have hz : (0 : ℤ) ≤ Law.clampZ ((u : ℤ) - 2 ^ 15) + 2 ^ 11 := by
    have h1 : (-2047 : ℤ) ≤ Law.clampZ ((u : ℤ) - 2 ^ 15) :=
      le_min (le_max_right _ _) (by norm_num)
    linarith
  have e2 : (((Law.clampZ ((u : ℤ) - 2 ^ 15) + 2 ^ 11).toNat : ℕ) : ℤ) =
      Inst.Model.clamp 2047 ((u : ℤ) - 2 ^ 15) + 2 ^ 11 := Int.toNat_of_nonneg hz
  refine ⟨u, hu, Law.Came.eq_natCast_of_rd (Law.Came.okE_keyNAt _ _ _) ?_⟩
  rw [Law.rd_keyN_clamp ht hS hx, e0, ← e2]
  push_cast
  rfl

/-- The key of the row's digits: the normalisation's 99 and the head's 21. -/
theorem digits_back (hT : Norm.T = 1024)
    (R : Policy.LedgerHead.RF Law.npOf (fun j v => ((H j v : ℤ) : Law.K)) Y (cellsN c)) :
    ∀ t, t < Norm.T → ∀ j, j < NR + 21 → Law.InBits 8 (Law.keyNAt c (Law.cornerN j t) .digits) := by
  intro t ht j hj
  have hi : t < 1024 := by rw [← hT]; exact ht
  have hj' : j < 120 := by
    have h := hj
    unfold NR at h
    omega
  have k := R.keys .ROW j t hj' hi
  rw [keyN_cast] at k
  obtain ⟨u, hu, e⟩ := k
  have e0 : (((Inst.Model.Ledger.mu j : ℤ) * Inst.Model.Head.Dv (cellsN c) j t : ℤ) : Law.K) =
      (((u : ℕ) : ℤ) : Law.K) := e
  rw [Dv_at, Int.cast_natCast] at e0
  refine ⟨u, hu, Law.Came.eq_natCast_of_rd (Law.Came.okE_keyNAt _ _ _) ?_⟩
  rw [Law.rd_keyN_digits ht hj, Law.mul_eq_mu]
  exact e0

/-- **The four fields of CellRelN that speak of keys**, from the library's clause on keys. -/
theorem normKeys_back (hT : Norm.T = 1024) (hd : Norm.d = 5120) (hS : Norm.S2 ∣ Norm.d)
    (R : Policy.LedgerHead.RF Law.npOf (fun j v => ((H j v : ℤ) : Law.K)) Y (cellsN c)) :
    (∀ t, t < Norm.T → ∀ x, x < Norm.d →
      Law.InBits 16 (Law.keyNAt c (Law.cornerN x t) .remLow)) ∧
    (∀ t, t < Norm.T → ∀ x, x < Norm.d →
      Law.InBits 16 (Law.keyNAt c (Law.cornerN x t) .remHigh)) ∧
    (∀ t, t < Norm.T → ∀ x, x < Norm.d →
      Law.IsClampRow (Law.keyNAt c (Law.cornerN x t) .clamp)) ∧
    ∀ t, t < Norm.T → ∀ j, j < NR + 21 →
      Law.InBits 8 (Law.keyNAt c (Law.cornerN j t) .digits) :=
  ⟨remLow_back hT hd hS R, remHigh_back hT hd hS R, clamp_back hT hd hS R, digits_back hT R⟩

end Field

end VerifiableInference.Desc.Kinds.HeadJoin

#print axioms VerifiableInference.Desc.Kinds.HeadJoin.remLow_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.remHigh_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.clamp_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.digits_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.normKeys_back
