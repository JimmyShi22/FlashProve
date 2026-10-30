-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/LedgerForms.lean: the identities of a normalisation's ledger as affine claims.

The 17 identities (Inst/Model/Common/Ledger.lean) contain seven products of row values (the numbers
`Vlo`, .., `rq` of that file) and the nine sums W_s of products of cells. In the protocol the prover
names scalars for these (pv_n, W_s), and what is left of an identity is affine in the bytes, in the
W_s and in the pv_n. An affine function commutes with the multilinear extension over the positions
(its constant unchanged, since Σ_i eq(u, i) = 1) and can be written as a form (Blocks/Form.lean).
  `prodsOf a b l h`             the seven products as a function of four numbers, so that the same
                                expression serves at a position and at a point
  `ext_idn`                     the extension of identity k's value is `idnP` of the extensions of
                                W_s, bytes and products; `ext_Vlo`, .., `ext_R`: the same for every
                                row value
  `b256F`, `VloF`, .., `RF`     the row values as forms, from forms DF n for the values of the
                                bytes (cell + 128); `val_VloF`, ..
  `val_idnForm`                 the value of `idnForm`, identity number k as a form, is `idnP` of
                                the values
The sums of squares: Σ_s γ^s W_s = Σ_j (Σ_l γ^l b_l[j])² is `sum_pow_Wsum` of
Inst/Model/Common/LedgerSound.lean.
Notation:
  `ext g v pt`: "The multilinear extension of the vector v of length 2^g at the point pt (its first
    g coordinates)." (Blocks/Ext.lean); so g: a natural number, u: a point, `ℕ → E`.
  `D m i`: an element of E; D (in section 2): a map `ℕ → ℕ → E`, first the number m of a byte, then
    the position i (`fun m => D m i` stands where Inst/Model/Common/Ledger.lean has the bytes D).
  `N`, `y`: "N indexes the entries of vectors and pad vectors on which forms may depend, and y : N →
    E gives their contents." (the head of Blocks/Form.lean).
  `Form N E`: "A form: an affine function of the entries, given by its constant term (at none) and
    its coefficients."; `Form.val y f`: "The value of a form" (Blocks/Form.lean).
-/
import Inst.Model.Common.LedgerSound
import Blocks.Ext
import Blocks.LookupBlock

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Inst.Model.Ledger

open Finset Blocks

/-! ## 1. The seven products, and the identities without products -/

section Prods
variable {K : Type} [CommRing K]

/-- The seven products of the four numbers a = sa, b = sb, l = Rlo, h = Rhi (in this order: a², ab,
b², la, lb, ha, hb). -/
def prodsOf (a b l h : K) (n : ℕ) : K :=
  match n with
  | 0 => a ^ 2
  | 1 => a * b
  | 2 => b ^ 2
  | 3 => l * a
  | 4 => l * b
  | 5 => h * a
  | 6 => h * b
  | _ => 0

/-- the seven products of row values of a ledger -/
def prods (D : ℕ → K) : ℕ → K := prodsOf (sa D) (sb D) (Rlo D) (Rhi D)

/-- Identity number k with pv_n in the place of the n-th product: affine in Ws, D and pv. -/
def idnP (np : NormPar) (Ws D pv : ℕ → K) (k : ℕ) : K :=
  if k < 9 then Ws k + cs D k - D k - 256 * cs D (k + 1)
  else match k with
    | 9 => pv 1 - Blo D - 2 ^ 23 * Bhi D
    | 10 => Vlo D + (np.eps : K) - pv 0 - 2 ^ 25 * Blo D - l1 D + 2 ^ 48 * kc D
    | 11 => Vhi D - Bhi D - pv 2 - kc D
    | 12 => l1 D + h1 D - 2 * sig D
    | 13 => pv 4 + pv 5 - q1 D
    | 14 => pv 6
    | 15 => 2 ^ (np.M + 1) + sig D - s0 D - 2 * pv 3 - 2 ^ 25 * q1 D - 2 * rr D
    | 16 => rr D + rq D - sig D + 1
    | _ => 0

/-- With the true products it is the identity. -/
theorem idn_eq_idnP (np : NormPar) (Ws D : ℕ → K) (k : ℕ) :
    idn np Ws D k = idnP np Ws D (prods D) k := by
  by_cases hk9 : k < 9
  · rw [idn_j1 np _ _ hk9]
    exact (if_pos hk9).symm
  · by_cases hk17 : 17 ≤ k
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 17 := ⟨k - 17, by omega⟩
      rw [idn_of_le D np Ws hk17]
      unfold idnP
      rw [if_neg (by omega)]
      rfl
    · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem idnP_j1 (np : NormPar) (Ws D pv : ℕ → K) {k : ℕ} (hk : k < 9) :
    idnP np Ws D pv k = Ws k + cs D k - D k - 256 * cs D (k + 1) := if_pos hk

theorem idnP_of_le (np : NormPar) (Ws D pv : ℕ → K) {k : ℕ} (hk : 17 ≤ k) :
    idnP np Ws D pv k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 17 := ⟨k - 17, by omega⟩
  unfold idnP
  rw [if_neg (by omega)]
  rfl

end Prods

/-! ## 2. Extensions over the positions -/

section Ext
variable {E : Type} [Field E] (g : ℕ) (D : ℕ → ℕ → E) (u : ℕ → E)

theorem ext_b256 (a n : ℕ) :
    ext g (fun i => b256 (fun m => D m i) a n) u = b256 (fun m => ext g (D m) u) a n := by
  unfold b256
  rw [ext_sum]
  exact sum_congr rfl fun l _ => ext_smul g _ _ u

theorem ext_Vlo : ext g (fun i => Vlo fun m => D m i) u = Vlo fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_Vhi : ext g (fun i => Vhi fun m => D m i) u = Vhi fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_l1 : ext g (fun i => l1 fun m => D m i) u = l1 fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_h1 : ext g (fun i => h1 fun m => D m i) u = h1 fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_Blo : ext g (fun i => Blo fun m => D m i) u = Blo fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_Bhi : ext g (fun i => Bhi fun m => D m i) u = Bhi fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_Rlo : ext g (fun i => Rlo fun m => D m i) u = Rlo fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_Rhi : ext g (fun i => Rhi fun m => D m i) u = Rhi fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_q1 : ext g (fun i => q1 fun m => D m i) u = q1 fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_rr : ext g (fun i => rr fun m => D m i) u = rr fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_rq : ext g (fun i => rq fun m => D m i) u = rq fun m => ext g (D m) u :=
  ext_b256 g D u _ _
theorem ext_s0 : ext g (fun i => s0 fun m => D m i) u = s0 fun m => ext g (D m) u := rfl

theorem ext_sa : ext g (fun i => sa fun m => D m i) u = sa fun m => ext g (D m) u := by
  unfold sa
  rw [ext_add, ext_add, ext_add, ext_smul, ext_smul, ext_smul]

theorem ext_sb : ext g (fun i => sb fun m => D m i) u = sb fun m => ext g (D m) u := by
  unfold sb
  rw [ext_add, ext_smul]

theorem ext_sig : ext g (fun i => sig fun m => D m i) u = sig fun m => ext g (D m) u := by
  unfold sig
  rw [ext_add, ext_smul, ext_sa, ext_sb]

theorem ext_kc : ext g (fun i => kc fun m => D m i) u = kc fun m => ext g (D m) u := by
  unfold kc
  rw [ext_sub, ext_const]

theorem ext_R : ext g (fun i => R fun m => D m i) u = R fun m => ext g (D m) u := by
  unfold R
  rw [ext_add, ext_smul, ext_Rlo, ext_Rhi]

theorem ext_cs (s : ℕ) :
    ext g (fun i => cs (fun m => D m i) s) u = cs (fun m => ext g (D m) u) s := by
  unfold cs
  by_cases h0 : s = 0
  · simp only [if_pos h0]
    exact ext_const g 0 u
  · by_cases h9 : s = 9
    · simp only [if_neg h0, if_pos h9]
    · simp only [if_neg h0, if_neg h9]
      rw [ext_sub, ext_const, ext_b256]

/-- `idnP` commutes with the multilinear extension over the positions; its constants are
unchanged. -/
theorem ext_idnP (np : NormPar) (Ws pv : ℕ → ℕ → E) (k : ℕ) :
    ext g (fun i => idnP np (fun s => Ws s i) (fun m => D m i) (fun n => pv n i) k) u
      = idnP np (fun s => ext g (Ws s) u) (fun m => ext g (D m) u) (fun n => ext g (pv n) u) k := by
  by_cases hk9 : k < 9
  · simp only [idnP_j1 np _ _ _ hk9]
    rw [ext_sub, ext_sub, ext_add, ext_smul, ext_cs, ext_cs]
  · by_cases hk17 : 17 ≤ k
    · simp only [idnP_of_le np _ _ _ hk17]
      exact ext_const g 0 u
    · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show ext g (fun i => pv 1 i - Blo (fun m => D m i) - 2 ^ 23 * Bhi fun m => D m i) u = _
        rw [ext_sub, ext_sub, ext_smul, ext_Blo, ext_Bhi]
        rfl
      · show ext g (fun i =>
              Vlo (fun m => D m i) + (np.eps : E) - pv 0 i - 2 ^ 25 * Blo (fun m => D m i) -
                l1 (fun m => D m i) + 2 ^ 48 * kc fun m => D m i) u = _
        rw [ext_add, ext_sub, ext_sub, ext_sub, ext_add, ext_const, ext_smul, ext_smul, ext_Vlo,
          ext_Blo, ext_l1, ext_kc]
        rfl
      · show ext g
            (fun i => Vhi (fun m => D m i) - Bhi (fun m => D m i) - pv 2 i - kc fun m => D m i) u =
          _
        rw [ext_sub, ext_sub, ext_sub, ext_Vhi, ext_Bhi, ext_kc]
        rfl
      · show ext g (fun i => l1 (fun m => D m i) + h1 (fun m => D m i) - 2 * sig fun m => D m i) u =
          _
        rw [ext_sub, ext_add, ext_smul, ext_l1, ext_h1, ext_sig]
        rfl
      · show ext g (fun i => pv 4 i + pv 5 i - q1 fun m => D m i) u = _
        rw [ext_sub, ext_add, ext_q1]
        rfl
      · rfl
      · show ext g (fun i =>
              2 ^ (np.M + 1) + sig (fun m => D m i) - s0 (fun m => D m i) - 2 * pv 3 i -
                2 ^ 25 * q1 (fun m => D m i) - 2 * rr fun m => D m i) u = _
        rw [ext_sub, ext_sub, ext_sub, ext_sub, ext_add, ext_const, ext_smul, ext_smul, ext_smul,
          ext_sig, ext_s0, ext_q1, ext_rr]
        rfl
      · show ext g
            (fun i => rr (fun m => D m i) + rq (fun m => D m i) - sig (fun m => D m i) + 1) u = _
        rw [ext_add, ext_sub, ext_add, ext_const, ext_rr, ext_rq, ext_sig]
        rfl

/-- The extension of the value of an identity is `idnP` of the extensions, with those of the true
products. -/
theorem ext_idn (np : NormPar) (Ws : ℕ → ℕ → E) (k : ℕ) :
    ext g (fun i => idn np (fun s => Ws s i) (fun m => D m i) k) u =
        idnP np (fun s => ext g (Ws s) u) (fun m => ext g (D m) u)
          (fun n => ext g (fun i => prods (fun m => D m i) n) u) k := by
  simp only [idn_eq_idnP]
  exact ext_idnP g D u np Ws (fun n i => prods (fun m => D m i) n) k

/-- The products of the extensions of the factors: at a point u, the seven products of the row
values of the extended bytes are the products of the extensions of sa, sb, Rlo, Rhi. (They are not
the extensions of the products.) -/
theorem prods_ext (n : ℕ) :
    prods (fun m => ext g (D m) u) n =
      prodsOf (ext g (fun i => sa fun m => D m i) u) (ext g (fun i => sb fun m => D m i) u)
        (ext g (fun i => Rlo fun m => D m i) u) (ext g (fun i => Rhi fun m => D m i) u) n := by
  rw [ext_sa, ext_sb, ext_Rlo, ext_Rhi]
  rfl

end Ext

/-! ## 3. Row values and identities as forms -/

section Forms
variable {N E : Type} [Fintype N] [Field E] (y : N → E) (DF : ℕ → Form N E)

/-- n bytes from byte a on, as a form; DF m is a form for the value of byte m -/
def b256F (a n : ℕ) : Form N E := ∑ l ∈ range n, (256 ^ l : E) • DF (a + l)

theorem val_b256F (a n : ℕ) :
    Form.val y (b256F DF a n) = b256 (fun m => Form.val y (DF m)) a n := by
  simp [b256F, b256, map_sum, map_smul]

def VloF : Form N E := b256F DF 0 6
def VhiF : Form N E := b256F DF 6 4
def l1F : Form N E := b256F DF 64 5
def h1F : Form N E := b256F DF 69 5
def BloF : Form N E := b256F DF 74 3
def BhiF : Form N E := b256F DF 77 2
def RloF : Form N E := b256F DF 80 3
def RhiF : Form N E := b256F DF 83 3
def q1F : Form N E := b256F DF 86 3
def rrF : Form N E := b256F DF 89 5
def rqF : Form N E := b256F DF 94 5
def s0F : Form N E := DF 59
def saF : Form N E := (2 : E) • DF 58 + DF 59 + (2 ^ 8 : E) • DF 60 + (2 ^ 16 : E) • DF 61
def sbF : Form N E := DF 62 + (2 ^ 8 : E) • DF 63
def sigF : Form N E := saF DF + (2 ^ 24 : E) • sbF DF
def kcF : Form N E := DF 79 - Form.const 4
def RF : Form N E := RloF DF + (2 ^ 24 : E) • RhiF DF
def csF (s : ℕ) : Form N E :=
  if s = 0 then 0 else if s = 9 then DF 9 else b256F DF (10 + 6 * (s - 1)) 6 - Form.const (2 ^ 47)

theorem val_VloF : Form.val y (VloF DF) = Vlo fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_VhiF : Form.val y (VhiF DF) = Vhi fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_l1F : Form.val y (l1F DF) = l1 fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_h1F : Form.val y (h1F DF) = h1 fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_BloF : Form.val y (BloF DF) = Blo fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_BhiF : Form.val y (BhiF DF) = Bhi fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_RloF : Form.val y (RloF DF) = Rlo fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_RhiF : Form.val y (RhiF DF) = Rhi fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_q1F : Form.val y (q1F DF) = q1 fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_rrF : Form.val y (rrF DF) = rr fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_rqF : Form.val y (rqF DF) = rq fun m => Form.val y (DF m) := val_b256F y DF _ _
theorem val_s0F : Form.val y (s0F DF) = s0 fun m => Form.val y (DF m) := rfl
theorem val_saF : Form.val y (saF DF) = sa fun m => Form.val y (DF m) := by simp [saF, sa]
theorem val_sbF : Form.val y (sbF DF) = sb fun m => Form.val y (DF m) := by simp [sbF, sb]
theorem val_sigF : Form.val y (sigF DF) = sig fun m => Form.val y (DF m) := by
  simp [sigF, sig, val_saF, val_sbF]
theorem val_kcF : Form.val y (kcF DF) = kc fun m => Form.val y (DF m) := by simp [kcF, kc]
theorem val_RF : Form.val y (RF DF) = R fun m => Form.val y (DF m) := by
  simp [RF, R, val_RloF, val_RhiF]

theorem val_csF (s : ℕ) : Form.val y (csF DF s) = cs (fun m => Form.val y (DF m)) s := by
  unfold csF cs
  split_ifs
  · exact map_zero _
  · rfl
  · simp [val_b256F]

/-- Identity number k as a form, from forms for the W_s, for the values of the bytes and for the
pv_n. -/
def idnForm (np : NormPar) (WsF pvF : ℕ → Form N E) (k : ℕ) : Form N E :=
  if k < 9 then WsF k + csF DF k - DF k - (256 : E) • csF DF (k + 1)
  else match k with
    | 9 => pvF 1 - BloF DF - (2 ^ 23 : E) • BhiF DF
    | 10 => VloF DF + Form.const (np.eps : E) - pvF 0 - (2 ^ 25 : E) • BloF DF - l1F DF + (2 ^ 48 : E) • kcF DF
    | 11 => VhiF DF - BhiF DF - pvF 2 - kcF DF
    | 12 => l1F DF + h1F DF - (2 : E) • sigF DF
    | 13 => pvF 4 + pvF 5 - q1F DF
    | 14 => pvF 6
    | 15 => Form.const (2 ^ (np.M + 1)) + sigF DF - s0F DF - (2 : E) • pvF 3 - (2 ^ 25 : E) • q1F DF - (2 : E) • rrF DF
    | 16 => rrF DF + rqF DF - sigF DF + Form.const 1
    | _ => 0

/-- The value of the form is `idnP` of the values. -/
theorem val_idnForm (np : NormPar) (WsF pvF : ℕ → Form N E) (k : ℕ) :
    Form.val y (idnForm DF np WsF pvF k) =
      idnP np (fun s => Form.val y (WsF s)) (fun m => Form.val y (DF m))
        (fun n => Form.val y (pvF n)) k := by
  by_cases hk9 : k < 9
  · rw [idnP_j1 np _ _ _ hk9]
    unfold idnForm
    rw [if_pos hk9]
    simp [val_csF]
  · by_cases hk17 : 17 ≤ k
    · rw [idnP_of_le np _ _ _ hk17]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 17 := ⟨k - 17, by omega⟩
      unfold idnForm
      rw [if_neg (by omega)]
      exact map_zero _
    · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show Form.val y (pvF 1 - BloF DF - (2 ^ 23 : E) • BhiF DF) = _
        simp [val_BloF, val_BhiF]
        rfl
      · show Form.val y
            (VloF DF + Form.const (np.eps : E) - pvF 0 - (2 ^ 25 : E) • BloF DF -
              l1F DF + (2 ^ 48 : E) • kcF DF) = _
        simp [val_VloF, val_BloF, val_l1F, val_kcF]
        rfl
      · show Form.val y (VhiF DF - BhiF DF - pvF 2 - kcF DF) = _
        simp [val_VhiF, val_BhiF, val_kcF]
        rfl
      · show Form.val y (l1F DF + h1F DF - (2 : E) • sigF DF) = _
        simp [val_l1F, val_h1F, val_sigF]
        rfl
      · show Form.val y (pvF 4 + pvF 5 - q1F DF) = _
        simp [val_q1F]
        rfl
      · rfl
      · show Form.val y
            (Form.const (2 ^ (np.M + 1)) + sigF DF - s0F DF - (2 : E) • pvF 3 -
              (2 ^ 25 : E) • q1F DF - (2 : E) • rrF DF) = _
        simp [val_sigF, val_s0F, val_q1F, val_rrF]
        rfl
      · show Form.val y (rrF DF + rqF DF - sigF DF + Form.const 1) = _
        simp [val_rrF, val_rqF, val_sigF]
        rfl


end Forms

end Inst.Model.Ledger
