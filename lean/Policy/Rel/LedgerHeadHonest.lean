-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerHeadHonest.lean

Under `N.HonIn` the honest cells of the head with the cost ledger meet its field relation modulo
every p.

The honest cells are `N.honCells` (Inst/Model/Head/HonestN.lean). The hypothesis is `N.HonIn` of
that file: the final normalisation is valid and runs at every position; the output matrix has
entries at most 2^12 in absolute value; every checked token is below V; the policy's clauses hold of
the logits; C, θ < 2^40, cap < 2^16. Every key of the honest cells is an entry of its table, and
every identity and clause is 0, over the integers; so the statements have no condition on p.

* `hon_rfz`: under `N.HonIn`, `RFz p np H y (N.honCells np x H y)`.
* `hon_rf`: the same for `RF` over `ZMod p`.

Under `N.HonIn` the honest cells are at most 128 in absolute value at every position:
`N.hon_cells_le` (Inst/Model/Head/HonestN.lean).

Limits: outside `N.HonIn` the cells are defined, and nothing is said of them. What the head of
Inst/Model/Head/HonestN.lean lists as not said is not said here either.
-/
import Inst.Model.Head.HonestN
import Cm.TargetPHeadHonest
import Policy.Rel.LedgerHeadInt

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerHead

open Inst.Model Inst.Model.Head Inst.Model.Head.Policy Finset
open Cm.Plain.TP (inLut_eq inR16 inR8)

variable {p : ℕ} {np : NormPar} {x : ℕ → Vec} {H : Mat} {y : Req}

/-! ## The arrays of the final normalisation, at the honest cells -/

theorem c_xv {j : ℕ} (hj : j < nD) (i : ℕ) : xv (N.honCells np x H y) j i = x i j :=
  N.hon_xv np x H (N.req0 y) hj i

theorem c_bl {l j : ℕ} (hj : j < nD) (i : ℕ) : bl (N.honCells np x H y) l j i = N.bX x i l j :=
  N.hon_bl np x H (N.req0 y) hj i

theorem c_nrm {j : ℕ} (hj : j < nD) (i : ℕ) :
    nrm (N.honCells np x H y) j i = N.outv np x i j :=
  N.hon_nrm np x H (N.req0 y) hj i

theorem c_nw {j : ℕ} (hj : j < nD) (i : ℕ) : nw (N.honCells np x H y) j i = N.ywv np x i j := by
  rw [N.t_nw hj, N.hon_nw np x H (N.req0 y) hj]

theorem c_rn {j : ℕ} (hj : j < nD) (i : ℕ) : rn (N.honCells np x H y) j i = N.rnv np x i j := by
  rw [N.t_rn hj, N.hon_rn np x H (N.req0 y) hj]

theorem c_led {i : ℕ} :
    ∀ n < 99, Dv (N.honCells np x H y) n i = Ledger.hon np nD (N.bX x i) n := fun n hn => by
  rw [N.t_Dv n hn, N.hon_led n hn]

theorem c_Rz (h : N.HonIn np x H y) {i : ℕ} (hi : i < nT) :
    Ledger.R (fun n => Dv (N.honCells np x H y) n i) = N.Rz np x i := by
  rw [N.R_congr N.t_Dv]
  exact N.hon_Rz h.base hi

/-! ## The relation -/

/-- Under `N.HonIn` the honest cells satisfy the field relation of the head, modulo every p. -/
theorem hon_rfz (h : N.HonIn np x H y) : RFz p np H y (N.honCells np x H y) where
  small := N.hon_small h
  keys := fun s x' i hx hi => by
    cases s
    · -- NF
      have hj : x' < nD := hx
      show ∃ u < R16.rows,
        Site.site (xv (N.honCells np x H y) x' i *
              Ledger.R (fun n => Dv (N.honCells np x H y) n i))
            (nw (N.honCells np x H y) x' i) (rn (N.honCells np x H y) x' i) np.K ≡
          R16.row u [ZMOD (p : ℤ)]
      rw [c_xv hj, c_Rz h hi, c_nw hj, c_rn hj]
      have := Site.site_hon (x i x' * N.Rz np x i) np.K
      exact inR16 this.2.1 this.2.2
    · -- NFH
      have hj : x' < nD := hx
      obtain ⟨-, -, -, -, hK17, hK32, -⟩ := h.nf
      show ∃ u < R16.rows,
        (((2 ^ (32 - np.K) : ℕ) : ℤ)) * rn (N.honCells np x H y) x' i ≡ R16.row u [ZMOD (p : ℤ)]
      rw [c_rn hj]
      have :=
        Site.high_hon (x i x' * N.Rz np x i) (k := np.K) (top := 32) (w := 16) rfl (by omega) hK32
      have e : (((2 ^ (32 - np.K) : ℕ) : ℤ)) * N.rnv np x i x' =
          Site.high (Site.hd (x i x' * N.Rz np x i) np.K) np.K 32 := by
        unfold Site.high
        push_cast
        rfl
      rw [e]
      exact inR16 this.1 this.2
    · -- HD0
      have hv : x' < nV := hx
      obtain ⟨e, k0, k1⟩ := key_top h.pol h.fit i (show x' < ppref.V from hv)
      show ∃ u < Cm.Plain.TP.R23.rows,
        mg (N.honCells np x H y) H y x' i - 2 ^ 8 * K1 (N.honCells np x H y) y x' i -
            K2 (N.honCells np x H y) y x' i ≡
          Cm.Plain.TP.R23.row u [ZMOD (p : ℤ)]
      rw [N.t_mg h x' hi, N.t_K1 hv hi, N.t_K2 hv hi, e]
      refine inLut_eq ((Honest.honD (N.lgv np x H) y.pol y.inst).K0 x' i).toNat
        (by show _ < 2 ^ 16; omega) ?_
      show _ = 2 ^ 23 * ((((Honest.honD (N.lgv np x H) y.pol y.inst).K0 x' i).toNat : ℕ) : ℤ)
      rw [Int.toNat_of_nonneg k0]
    · -- HD1
      have hv : x' < nV := hx
      show ∃ u < R16.rows, K1 (N.honCells np x H y) y x' i ≡ R16.row u [ZMOD (p : ℤ)]
      rw [N.t_K1 hv hi]
      have := key_mid h.pol h.fit i x'
      exact inR16 this.1 this.2
    · -- ROW
      show ∃ u < R8.rows,
        ((Ledger.mu x' : ℤ) : ℤ) * Dv (N.honCells np x H y) x' i ≡ R8.row u [ZMOD (p : ℤ)]
      by_cases c : x' < 99
      · rw [c_led x' c]
        have := Ledger.hon_typed (N.honHyp h.base hi) x' c
        exact inR8 this.1 (by omega)
      · have e : Dv (N.honCells np x H y) x' i =
            hidByte (Honest.honH (N.lgv np x H) y.pol y.inst) x' i := by
          unfold Dv
          rw [show (N.honCells np x H y).hr x' i = phr (N.lgv np x H) y.pol y.inst x' i
                from N.honP_hr np x H y.pol y.inst (by omega) i, phr_byte]
        have m : Ledger.mu x' = 1 := by
          unfold Ledger.mu
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
        have b := hidByte_bounds (Honest.honH (N.lgv np x H) y.pol y.inst) x' i
        rw [e, m]
        exact inR8 (by omega) (by omega)
    · -- HD2
      have hv : x' < nV := hx
      show ∃ u < R8.rows, K2 (N.honCells np x H y) y x' i ≡ R8.row u [ZMOD (p : ℤ)]
      rw [N.t_K2 hv hi]
      have := key_low h.pol h.fit i x'
      exact inR8 this.1 this.2
    · -- HE0
      have hv : x' < nV := by simp only [len] at hx; unfold nV; omega
      show ∃ u < FE.rows,
        K1 (N.honCells np x H y) y x' i + 2 ^ 16 * ex (N.honCells np x H y) x' i ≡
          FE.row u [ZMOD (p : ℤ)]
      rw [N.t_K1 hv hi, N.t_ex hv]
      obtain ⟨a, e⟩ := key_ex h.pol h.fit i x'
      exact inLut_eq _ a e
    · -- HE1
      have hv : 131072 + x' < nV := by simp only [len] at hx; unfold nV; omega
      show ∃ u < FE.rows, K1 (N.honCells np x H y) y (131072 + x') i +
          2 ^ 16 * ex (N.honCells np x H y) (131072 + x') i ≡
        FE.row u [ZMOD (p : ℤ)]
      rw [N.t_K1 hv hi, N.t_ex hv]
      obtain ⟨a, e⟩ := key_ex h.pol h.fit i (131072 + x')
      exact inLut_eq _ a e
    · -- CNF
      have hj : x' < nD := hx
      show ∃ u < FC.rows, (nw (N.honCells np x H y) x' i + 2 ^ 15) +
          2 ^ 28 * (nrm (N.honCells np x H y) x' i + 2 ^ 11) ≡
        FC.row u [ZMOD (p : ℤ)]
      rw [c_nw hj, c_nrm hj]
      have f := N.yw_fits h.base hi hj
      unfold Fits16 at f
      refine inLut_eq (N.ywv np x i x' + 2 ^ 15).toNat
        (by show (N.ywv np x i x' + 2 ^ 15).toNat < 2 ^ 16; omega) ?_
      show _ = (((N.ywv np x i x' + 2 ^ 15).toNat : ℕ) : ℤ) +
          2 ^ 28 * (clamp 2047 ((((N.ywv np x i x' + 2 ^ 15).toNat : ℕ) : ℤ) - 2 ^ 15) + 2 ^ 11)
      rw [Int.toNat_of_nonneg (by omega), add_sub_cancel_right]
      rfl
  idns := fun i hi k hk => by
    have e : N.idn np (N.honCells np x H y) i k =
        Ledger.idn np (Ledger.Wsum nD (N.bX x i)) (Ledger.hon np nD (N.bX x i)) k := by
      unfold N.idn
      rw [N.idn_congr c_led np _ hk]
      have hW : Ledger.Wsum nD (fun l j => bl (N.honCells np x H y) l j i) =
          Ledger.Wsum nD (N.bX x i) := by
        funext s
        unfold Ledger.Wsum
        exact sum_congr rfl fun j hj => sum_congr rfl fun l _ => sum_congr rfl fun l' _ => by
          simp only [c_bl (mem_range.1 hj)]
      rw [hW]
    rw [e, Ledger.hon_idn (N.honHyp h.base hi) k hk]
  jc := fun i _ => by
    have R := Honest.honest_rel h.pol h.fit
    have e := N.t_hid h
    have ec : hidC (N.honCells np x H y) i = (Honest.honH (N.lgv np x H) y.pol y.inst).c i :=
      congrFun (congrArg Hid.c e) i
    have ek : hidK (N.honCells np x H y) i = (Honest.honH (N.lgv np x H) y.pol y.inst).k i :=
      congrFun (congrArg Hid.k e) i
    have es : hidS (N.honCells np x H y) i = (Honest.honH (N.lgv np x H) y.pol y.inst).zs i :=
      congrFun (congrArg Hid.zs e) i
    have ex' : ∑ v ∈ range nV, ex (N.honCells np x H y) v i =
        ∑ v ∈ range ppref.V, (Honest.honD (N.lgv np x H) y.pol y.inst).ex v i :=
      sum_congr rfl fun v hv => N.t_ex (mem_range.1 hv) i
    unfold dB4 dZ
    rw [ec, ek, es, ex', y.rhoC_inst]
    by_cases c : i ∈ y.inst.cnt
    · rw [if_pos c, R.B4 i c, R.Z i c]
      simp
    · rw [if_neg c]
      simp
  sums := by
    have R := Honest.honest_rel h.pol h.fit
    have e := N.t_hid h
    have ec : hidC (N.honCells np x H y) = (Honest.honH (N.lgv np x H) y.pol y.inst).c :=
      congrArg Hid.c e
    have eb : hidB (N.honCells np x H y) = (Honest.honH (N.lgv np x H) y.pol y.inst).b :=
      congrArg Hid.b e
    have eu : hidU (N.honCells np x H y) = (Honest.honH (N.lgv np x H) y.pol y.inst).u :=
      congrArg Hid.u e
    have ez : hidZ (N.honCells np x H y) = (Honest.honH (N.lgv np x H) y.pol y.inst).z :=
      congrArg Hid.z e
    unfold sB2 sB3
    simp only [Int.cast_id, ec, eb, eu, ez]
    rw [N.sum_rhoC, N.sum_rhoC, R.B2, R.B3, y.inst_NB]
    simp

/-- Under `N.HonIn` the honest cells satisfy the field relation of the head over `ZMod p`, for
every p. -/
theorem hon_rf (p : ℕ) (h : N.HonIn np x H y) :
    RF (F := ZMod p) np (fun j v => (H j v : ZMod p)) y (N.honCells np x H y) :=
  rf_of_rfz (hon_rfz h)

end Policy.LedgerHead
