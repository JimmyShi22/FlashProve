-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/LayoutSplit.lean: factors of a tensor claim that are products over the split of a
coordinate. Definitions of the two halves of a factor, and theorems; to audit the relation `RinfPP`
(Inst/Model/Scales.lean), nothing of this file need be read.

A tensor claim (`TClaim`, Inst/Model/Common/TensorClaim.lean) has one factor f_g for each coordinate
of its unit. The layout splits an index i of a coordinate into a column part iᶜ and a row part iʳ
(`split`, Inst/Model/Layout.lean). The factors are products over the split if f_g[i] = fʳ_g[iʳ]
fᶜ_g[iᶜ] for all i < R_g (`Tensor.SplitOK`, Inst/Model/LayoutTensor.lean); fᶜ_g and fʳ_g are the two
halves of f_g.
For each of the three kinds of coordinates this file gives the two halves of the factors that occur
in the segments, on numbers, in the form that `Tensor.SplitOK` (Inst/Model/LayoutTensor.lean)
requires:
    low     f[i] = eq(u, i), u a point of w coordinates, R ≤ 2^w:         `lowC`, `lowR`, `low_ok`
    high    f[i] = eq(u, φ(i)), u of w ≥ s_g coordinates, for a map φ that is aligned at 2^s, s =
            s_g: an aligned run of 2^s indices goes to 2^s consecutive numbers, which start at a
            multiple of 2^s; φ = id gives f[i] = eq(u, i):   `highC`, `highR`, `Aligned`, `high_ok`
    whole   any factor: `wholeC`, `wholeR`, `whole_ok`
-/
import Inst.Model.LayoutTensor
import Blocks.EqN

set_option autoImplicit false

namespace Inst.Model.Layout.Tensor

open Finset Blocks Inst.Model.Layout.Bridge

variable {E : Type} [Field E]

theorem two_pow_sOf_dvd (R : ℕ) : 2 ^ sOf R ∣ R := pow_sAux_dvd _ _

theorem sOf_le_of_le {R w : ℕ} (hR : 0 < R) (h : R ≤ 2 ^ w) : sOf R ≤ w :=
  (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    (le_trans (Nat.le_of_dvd hR (two_pow_sOf_dvd R)) h)

/-! ## Kind low -/

/-- the half on the column part: eq(the last t coordinates of u, iᶜ) -/
def lowC (w off t : ℕ) (u : ℕ → E) : ℕ → E := fun ic => eqN t (off + (w - t)) u ic
/-- the half on the row part: eq(the first w − t coordinates of u, iʳ) -/
def lowR (w off t : ℕ) (u : ℕ → E) : ℕ → E := fun ir => eqN (w - t) off u ir

theorem low_eq {w t : ℕ} (ht : t ≤ w) (off : ℕ) (u : ℕ → E) (i : ℕ) :
    eqN w off u i = lowR w off t u (i / 2 ^ t) * lowC w off t u (i % 2 ^ t) := by
  have h := eqN_append' (w - t) t off u (i / 2 ^ t) (Nat.mod_lt i (Nat.two_pow_pos t))
  rwa [Nat.sub_add_cancel ht, Nat.div_add_mod'] at h

/-- Kind low, R ≤ 2^w, u of w coordinates: eq(u, ·) is the product of its halves. -/
theorem low_ok {R w : ℕ} (hw : R ≤ 2 ^ w) (off left : ℕ) (u : ℕ → E) :
    ∀ i < R, eqN w off u i =
      lowR w off (tOf ⟨R, .low⟩ left) u (split ⟨R, .low⟩ (tOf ⟨R, .low⟩ left) i).2 *
        lowC w off (tOf ⟨R, .low⟩ left) u (split ⟨R, .low⟩ (tOf ⟨R, .low⟩ left) i).1 := fun i hi =>
  low_eq (le_trans (Nat.min_le_left _ _) (sOf_le_of_le (lt_of_le_of_lt (Nat.zero_le _) hi) hw))
    off u i

/-! ## Kind high -/

/-- φ is aligned at 2^s on the indices below R -/
def Aligned (s R : ℕ) (φ : ℕ → ℕ) : Prop :=
  ∀ i < R, φ i = φ (i / 2 ^ s * 2 ^ s) + i % 2 ^ s ∧ 2 ^ s ∣ φ (i / 2 ^ s * 2 ^ s)

/-- the half on the column part iᶜ = b (a, b, e as in `split`, s_g = `sOf R`:
Inst/Model/Layout.lean) -/
def highC (w off s t : ℕ) (u : ℕ → E) : ℕ → E := fun ic => eqN t (off + (w - s)) u ic
/-- the half on the row part iʳ = a 2^(s−t) + e -/
def highR (w off s t : ℕ) (u : ℕ → E) (φ : ℕ → ℕ) : ℕ → E := fun ir =>
  eqN (w - s) off u (φ (ir / 2 ^ (s - t) * 2 ^ s) / 2 ^ s) *
    eqN (s - t) (off + (w - s) + t) u (ir % 2 ^ (s - t))

theorem high_eq {w s t : ℕ} (ht : t ≤ s) (hs : s ≤ w) (off : ℕ) (u : ℕ → E) (φ : ℕ → ℕ) (i : ℕ)
    (h1 : φ i = φ (i / 2 ^ s * 2 ^ s) + i % 2 ^ s) (h2 : 2 ^ s ∣ φ (i / 2 ^ s * 2 ^ s)) :
    eqN w off u (φ i) =
      highR w off s t u φ (i / 2 ^ s * 2 ^ (s - t) + i % 2 ^ (s - t)) *
        highC w off s t u (i / 2 ^ (s - t) % 2 ^ t) := by
  have hp : (2 : ℕ) ^ s = 2 ^ (s - t) * 2 ^ t := by rw [← pow_add, Nat.sub_add_cancel ht]
  have hlt : i % 2 ^ (s - t) < 2 ^ (s - t) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have a1 :=
    eqN_append' (w - s) s off u (φ (i / 2 ^ s * 2 ^ s) / 2 ^ s) (Nat.mod_lt i (Nat.two_pow_pos s))
  rw [Nat.sub_add_cancel hs, Nat.div_mul_cancel h2, ← h1] at a1
  have a2 := eqN_append' t (s - t) (off + (w - s)) u (i / 2 ^ (s - t) % 2 ^ t) hlt
  have e1 : i / 2 ^ (s - t) % 2 ^ t * 2 ^ (s - t) + i % 2 ^ (s - t) = i % 2 ^ s := by
    rw [hp, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]
  rw [Nat.add_sub_cancel' ht, e1] at a2
  unfold highR highC
  rw [a1, a2, Nat.add_comm (i / 2 ^ s * 2 ^ (s - t)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  ring

/-- Kind high, φ aligned at 2^(s_g), u of w ≥ s_g coordinates: eq(u, φ(·)) is the product of its
halves. -/
theorem high_ok {R w : ℕ} (hw : sOf R ≤ w) (off left : ℕ) (u : ℕ → E)
    (φ : ℕ → ℕ) (hφ : Aligned (sOf R) R φ) :
    ∀ i < R, eqN w off u (φ i) =
      highR w off (sOf R) (tOf ⟨R, .high⟩ left) u φ (split ⟨R, .high⟩ (tOf ⟨R, .high⟩ left) i).2 *
        highC w off (sOf R) (tOf ⟨R, .high⟩ left) u
          (split ⟨R, .high⟩ (tOf ⟨R, .high⟩ left) i).1 := fun i hi =>
  high_eq (Nat.min_le_left _ _) hw off u φ i (hφ i hi).1 (hφ i hi).2

theorem aligned_id (s R : ℕ) : Aligned s R id := fun i _ =>
  ⟨(Nat.div_add_mod' i (2 ^ s)).symm, Nat.dvd_mul_left _ _⟩

/-! ## Kind whole -/

def wholeC (t : ℕ) (f : ℕ → E) : ℕ → E := fun x => if 0 < t then f x else 1
def wholeR (t : ℕ) (f : ℕ → E) : ℕ → E := fun x => if 0 < t then 1 else f x

theorem whole_ok (R left : ℕ) (f : ℕ → E) :
    ∀ i < R, f i =
      wholeR (tOf ⟨R, .whole⟩ left) f (split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i).2 *
        wholeC (tOf ⟨R, .whole⟩ left) f
          (split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i).1 := fun i _ => by
  unfold wholeR wholeC
  by_cases h : 0 < tOf ⟨R, .whole⟩ left
  · rw [show split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i = (i, 0) from if_pos h,
      if_pos h, if_pos h, one_mul]
  · rw [show split ⟨R, .whole⟩ (tOf ⟨R, .whole⟩ left) i = (0, i) from if_neg h,
      if_neg h, if_neg h, mul_one]

/-! ## Factors by description -/

/-- How a factor is given: eq(u, ·) on a coordinate of kind low; eq(u, φ(·)) on a coordinate of kind
high; any function on a coordinate of kind whole. u is read from the coordinate off on and has w
coordinates. -/
inductive FD (E : Type)
  | low (w off : ℕ) (u : ℕ → E)
  | high (w off : ℕ) (u : ℕ → E) (φ : ℕ → ℕ)
  | whole (f : ℕ → E)

/-- the factor -/
def FD.f : FD E → ℕ → E
  | .low w off u => eqN w off u
  | .high w off u φ => fun i => eqN w off u (φ i)
  | .whole f => f
/-- its half on the column part, for the coordinate c when `left` bits are left -/
def FD.g (c : Coord) (left : ℕ) : FD E → ℕ → E
  | .low w off u => lowC w off (tOf c left) u
  | .high w off u _ => highC w off (sOf c.R) (tOf c left) u
  | .whole f => wholeC (tOf c left) f
/-- its half on the row part -/
def FD.r (c : Coord) (left : ℕ) : FD E → ℕ → E
  | .low w off u => lowR w off (tOf c left) u
  | .high w off u φ => highR w off (sOf c.R) (tOf c left) u φ
  | .whole f => wholeR (tOf c left) f
/-- the description fits the coordinate -/
def FD.OK (c : Coord) : FD E → Prop
  | .low w _ _ => c.kind = .low ∧ c.R ≤ 2 ^ w
  | .high w _ _ φ => c.kind = .high ∧ sOf c.R ≤ w ∧ Aligned (sOf c.R) c.R φ
  | .whole _ => c.kind = .whole

theorem FD.split_ok (c : Coord) (left : ℕ) (d : FD E) (h : d.OK c) :
    ∀ i < c.R,
      d.f i = d.r c left (split c (tOf c left) i).2 * d.g c left (split c (tOf c left) i).1 := by
  obtain ⟨R, kind⟩ := c
  cases d with
  | low w off u =>
    obtain ⟨h1, h2⟩ := h
    have h1 : kind = .low := h1
    subst h1
    exact low_ok h2 off left u
  | high w off u φ =>
    obtain ⟨h1, h2, h3⟩ := h
    have h1 : kind = .high := h1
    subst h1
    exact high_ok h2 off left u φ h3
  | whole f =>
    have h1 : kind = .whole := h
    subst h1
    exact whole_ok R left f

/-- the halves on the column parts, coordinate by coordinate -/
def gsOf : List Coord → ℕ → List (FD E) → List (ℕ → E)
  | c :: cs, left, d :: ds => d.g c left :: gsOf cs (left - tOf c left) ds
  | _, _, _ => []
/-- the halves on the row parts -/
def rsOf : List Coord → ℕ → List (FD E) → List (ℕ → E)
  | c :: cs, left, d :: ds => d.r c left :: rsOf cs (left - tOf c left) ds
  | _, _, _ => []
/-- one description for each coordinate, and each fits -/
def AllOK : List Coord → List (FD E) → Prop
  | [], _ => True
  | c :: cs, d :: ds => d.OK c ∧ AllOK cs ds
  | _ :: _, [] => False

theorem splitOK_of :
    ∀ (cs : List Coord) (left : ℕ) (ds : List (FD E)),
      AllOK cs ds → SplitOK cs left (ds.map FD.f) (gsOf cs left ds) (rsOf cs left ds)
  | [], _, _, _ => trivial
  | c :: cs, left, d :: ds, h => ⟨d.split_ok c left h.1, splitOK_of cs (left - tOf c left) ds h.2⟩
  | _ :: _, _, [], h => h.elim

/-- If the rows of the unit are inside the matrix (`hr`), a tensor claim whose factors are given by
descriptions that fit (`FD`, `AllOK`) is a tensor claim of the merge: its functional `TClaim.Tn`
equals `MG.TLay.Tn` of the unit's layout at the products of the halves, the form in which the merge
of tensor claims takes a claim (`MG.TLay`, Blocks/MergeBlock.lean). -/
theorem Tn_eq_tlay_of (P : Params) (k h : ℕ) (W : ℕ → ℕ → E) (n : ℕ) (U : UnitS) (ds : List (FD E))
    (hr : off k (units P) n + rows k U ≤ h) (hd : AllOK U.coords ds) :
    (⟨n, U, ds.map FD.f⟩ : TClaim E).Tn P k W =
      (lunit k h (units P) n U hr).toTLay.Tn (Blocks.Layout.prodC _ (facCOf _ (gsOf U.coords k ds)))
        (Blocks.Layout.prodR _ (facROf _ (rsOf U.coords k ds))) (matOf W) :=
  Tn_eq_tlay P k h W ⟨n, U, ds.map FD.f⟩ hr _ _ (splitOK_of U.coords k ds hd)

end Inst.Model.Layout.Tensor
