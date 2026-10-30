-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPHeadHonest.lean: the plain head with the scaled table: the honest cells
(Cm/HeadHonest.lean: `hon`, unchanged) satisfy its relation, modulo every number p, under the
hypothesis below.

This is completeness of the head's constraints: under `h` below, the honest cells meet them.
This file has `hon_rfz` for the relation `RFz p` of Cm/TargetPHeadNoWrap.lean, with three small
lemmas (an integer that is an entry of a table is congruent to it modulo every p).

Main names:
  `hon_rfz`: under `h : N.HonIn0 np x H y` (Inst/Model/Head/HonestBase.lean: the final
    normalisation is lawful and does not halt at any position, every entry of H is at most 2^12 in
    absolute value, and every margin at a covered position is at least 0), the honest cells
    `hon np x H y` satisfy `RFz p np H y`, for every number p.

Limits: no size condition on p is used here. The namespace is `Cm.Plain.TP`; the honest cells are
Cm/HeadHonest.lean's, whose head tells them. (The limits of the conditions (`Cm.TP.Cond`) that this
file serves: the head of Cm/TargetPRel.lean, "Limits:".)
Terms: lean/GLOSSARY.md.
-/
import Cm.HeadHonest
import Cm.TargetPHeadNoWrap


set_option autoImplicit false

namespace Cm.Plain.TP

open Cm.TI

open Inst.Model Inst.Model.Head Finset

variable {p : ℕ}

theorem inLut_eq {T : Lut} {a : ℤ} (u : ℕ) (hu : u < T.rows) (e : a = T.row u) :
    ∃ u < T.rows, a ≡ T.row u [ZMOD (p : ℤ)] :=
  ⟨u, hu, by rw [e]⟩

theorem inR16 {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 ^ 16) :
    ∃ u < R16.rows, a ≡ R16.row u [ZMOD (p : ℤ)] :=
  inLut_eq a.toNat (by show a.toNat < 2 ^ 16; omega) (by show a = ((a.toNat : ℕ) : ℤ); omega)

theorem inR8 {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 ^ 8) : ∃ u < R8.rows, a ≡ R8.row u [ZMOD (p : ℤ)] :=
  inLut_eq a.toNat (by show a.toNat < 2 ^ 8; omega) (by show a = ((a.toNat : ℕ) : ℤ); omega)

section Main
variable {np : NormPar} {x : ℕ → Vec} {H : Mat} {y : Req} (h : N.HonIn0 np x H y)
include h

/-- Under `h`, the honest cells satisfy the relation of the plain head. -/
theorem hon_rfz : RFz p np H y (hon np x H y) where
  small := fun i hi => by
    obtain ⟨a, b, c, d⟩ := hon_cells_le h hi
    exact ⟨fun φ hφ => lt_of_le_of_lt (a φ hφ) (by norm_num),
      fun φ hφ => lt_of_le_of_lt (b φ hφ) (by norm_num),
      fun φ hφ => lt_of_le_of_lt (c φ hφ) (by norm_num),
      fun φ hφ => lt_of_le_of_lt (d φ hφ) (by norm_num)⟩
  keys := fun s x' i hx hi => by
    cases s
    · -- NF
      have hj : x' < nD := hx
      show ∃ u < R16.rows,
        Site.site (xv (hon np x H y) x' i * Ledger.R (fun n => Dv (hon np x H y) n i))
            (nw (hon np x H y) x' i) (rn (hon np x H y) x' i) np.K ≡
          R16.row u [ZMOD (p : ℤ)]
      rw [hon_xv np x H y hj, hon_Rz h hi, hon_nw np x H y hj, hon_rn np x H y hj]
      have := Site.site_hon (x i x' * N.Rz np x i) np.K
      exact inR16 this.2.1 this.2.2
    · -- NFH
      have hj : x' < nD := hx
      obtain ⟨-, -, -, -, hK17, hK32, -⟩ := h.nf
      show ∃ u < R16.rows,
        (((2 ^ (32 - np.K) : ℕ) : ℤ)) * rn (hon np x H y) x' i ≡ R16.row u [ZMOD (p : ℤ)]
      rw [hon_rn np x H y hj]
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
      show ∃ u < R23.rows, mg (hon np x H y) H y x' i -
          2 ^ 8 * K1 (hon np x H y) y x' i - K2 (hon np x H y) y x' i ≡
        R23.row u [ZMOD (p : ℤ)]
      rw [hon_mg, hon_K1 np x H y hv, hon_K2 np x H y hv]
      split_ifs with hc
      · obtain ⟨-, -, K0, k0, k1, e⟩ := N.digits h hi hc hv
        rw [e]
        refine ⟨K0.toNat, by show K0.toNat < 2 ^ 16; omega, ?_⟩
        show 2 ^ 23 * K0 ≡ 2 ^ 23 * ((K0.toNat : ℕ) : ℤ) [ZMOD (p : ℤ)]
        have e2 : ((K0.toNat : ℕ) : ℤ) = K0 := Int.toNat_of_nonneg k0
        exact e2.symm ▸ Int.ModEq.refl _
      · exact inLut_eq 0 (by show 0 < 2 ^ 16; norm_num)
          (by show (0 : ℤ) - 2 ^ 8 * 0 - 0 = 2 ^ 23 * ((0 : ℕ) : ℤ); norm_num)
    · -- HD1
      have hv : x' < nV := hx
      show ∃ u < R16.rows, K1 (hon np x H y) y x' i ≡ R16.row u [ZMOD (p : ℤ)]
      rw [hon_K1 np x H y hv]
      split_ifs with hc
      · have := (N.digits h hi hc hv).2.1
        exact inR16 this.1 this.2
      · exact inR16 (by norm_num) (by norm_num)
    · -- ROW
      have hn : x' < 99 := hx
      show ∃ u < R8.rows,
        ((Ledger.mu x' : ℤ) : ℤ) * Dv (hon np x H y) x' i ≡ R8.row u [ZMOD (p : ℤ)]
      rw [hon_led np x H y x' hn]
      have := Ledger.hon_typed (N.honHyp h hi) x' hn
      exact inR8 this.1 (by omega)
    · -- HD2
      have hv : x' < nV := hx
      show ∃ u < R8.rows, K2 (hon np x H y) y x' i ≡ R8.row u [ZMOD (p : ℤ)]
      rw [hon_K2 np x H y hv]
      split_ifs with hc
      · have := (N.digits h hi hc hv).1
        exact inR8 this.1 this.2
      · exact inR8 (by norm_num) (by norm_num)
    · -- CNF
      have hj : x' < nD := hx
      show ∃ u < FC.rows, (nw (hon np x H y) x' i + 2 ^ 15) +
          2 ^ 28 * (nrm (hon np x H y) x' i + 2 ^ 11) ≡
        FC.row u [ZMOD (p : ℤ)]
      rw [hon_nw np x H y hj, hon_nrm np x H y hj]
      have f := N.yw_fits h hi hj
      unfold Fits16 at f
      refine inLut_eq (N.ywv np x i x' + 2 ^ 15).toNat
        (by show (N.ywv np x i x' + 2 ^ 15).toNat < 2 ^ 16; omega) ?_
      show _ = (((N.ywv np x i x' + 2 ^ 15).toNat : ℕ) : ℤ) +
          2 ^ 28 * (clamp 2047 ((((N.ywv np x i x' + 2 ^ 15).toNat : ℕ) : ℤ) - 2 ^ 15) + 2 ^ 11)
      rw [Int.toNat_of_nonneg (by omega), add_sub_cancel_right]
      rfl
  idns := fun i hi k hk => by
    have e : idn np (hon np x H y) i k =
        Ledger.idn np (Ledger.Wsum nD (N.bX x i)) (Ledger.hon np nD (N.bX x i)) k := by
      unfold idn
      rw [N.idn_congr (hon_led np x H y) np _ hk]
      have hW : Ledger.Wsum nD (fun l j => bl (hon np x H y) l j i) =
          Ledger.Wsum nD (N.bX x i) := by
        funext s
        unfold Ledger.Wsum
        exact sum_congr rfl fun j hj => sum_congr rfl fun l _ => sum_congr rfl fun l' _ => by
          simp only [hon_bl np x H y (mem_range.1 hj)]
      rw [hW]
    rw [e, Ledger.hon_idn (N.honHyp h hi) k hk]

end Main

end Cm.Plain.TP
