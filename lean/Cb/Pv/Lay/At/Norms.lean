-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Norms.lean: the records of the norms' stages of a layers' sub-proof's own rounds
(Cb/Pv/Lay/Squares.lean, Cb/Pv/Lay/Rows.lean) at a value: the library's description of a
feed-forward segment (Inst/Model/FF/Objects.lean, Inst/Model/Common/Ledger.lean, LedgerForms.lean).

Main names:
  `NormPar0`: what stays free: the sizes D; the entries J; how the entries are read as cells (rd);
    that 2 is not 0; the order of the squares' rounds; the places of the mask entries.
  `NormPar0.sq`: the sums of squares. The vector is Pv, the limbs under the powers of the drawn
    element; conv is Wt, the extension of the convolution sums W_s at the token point; rhs is the
    digit row's side of identity (J1) number s. The feature's variables are summed plainly, written
    as an equality-weighted sum at 1/2, whence scale = 2^-(bits of a feature).
  `NormPar0.rows`: the products of the rows. The shown vectors are sa, sb, Rlo, Rhi of every norm;
    the seven products stand in the order of Ledger.prodsOf; led says that the identities (J2) to
    (J9), with the vector's members in the place of the products (Ledger.idnP), vanish at the
    extensions of the digits.
  `sq_law`: the record's condition law, from the library's sum_pow_Wsum.
  `rows_pA`: a sum of the record is the extension of the library's product.
  `norms_atPt`: the squares' identities and the rows' claim at a token point p give that the
    extension at p of each of the 17 identities' defects (dJ) of every norm vanishes.

Limits: that the programs' vectors, scalars and lines are these is not said here. Nothing is said on
an honest prover, on completeness or on hiding.


-/
import Cb.Pv.Lay.OwnAll
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS Pv Wt dJ npOf lDd)

noncomputable section

/-! ### Small tools -/

section Tools
variable {E : Type} [Field E]

/-- The equality weight at a point whose coordinates are all 1/2. -/
theorem eqN_half (h2 : (2 : E) ≠ 0) (g off : ℕ) (a : ℕ → E) (ha : ∀ t < g, a (off + t) = 2⁻¹)
    (x : ℕ) : Blocks.eqN g off a x = (2⁻¹ : E) ^ g := by
  have e : (1 : E) - 2⁻¹ = 2⁻¹ := by
    field_simp
    norm_num
  have h : ∀ t ∈ range g,
      (if x.testBit (g - 1 - t) then a (off + t) else 1 - a (off + t)) = (2⁻¹ : E) := by
    intro t ht
    rw [ha t (mem_range.1 ht)]
    split_ifs
    · rfl
    · exact e
  unfold Blocks.eqN
  rw [prod_congr rfl h, prod_const, card_range]

/-- An extension on g + k variables whose first g coordinates are 1/2 is the plain sum over the
first part of the index, times 2^-g. -/
theorem ext_half (h2 : (2 : E) ≠ 0) (g k : ℕ) (v : ℕ → E) (p : Fin k → E) :
    Blocks.ext (g + k) v (Blocks.nat (Fin.append (fun _ : Fin g => (2⁻¹ : E)) p)) =
      (2⁻¹ : E) ^ g *
        ∑ j ∈ range (2 ^ g), Blocks.ext k (fun y => v (j * 2 ^ k + y)) (Blocks.nat p) := by
  rw [Blocks.ext_two, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  unfold Blocks.ext
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [eqN_half h2 g 0 _ (fun t ht => by
      rw [Nat.zero_add, nat_append_left g k _ p t ht]
      unfold Blocks.nat
      rw [dif_pos ht]) j,
    eqN_congr' (off' := 0) (a' := Blocks.nat p) (fun t ht => by
      rw [nat_append_right g k _ p t ht, Nat.zero_add]) y]
  ring

/-- The four row values that are shown: sa, sb, Rlo, Rhi. -/
def rowVal (Dg : ℕ → E) : Fin 4 → E
  | 0 => Inst.Model.Ledger.sa Dg
  | 1 => Inst.Model.Ledger.sb Dg
  | 2 => Inst.Model.Ledger.Rlo Dg
  | 3 => Inst.Model.Ledger.Rhi Dg

/-- The two factors of the seven products, in the order of Ledger.prodsOf. -/
def facs : Fin 7 → Fin 4 × Fin 4
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (1, 1)
  | 3 => (2, 0)
  | 4 => (2, 1)
  | 5 => (3, 0)
  | 6 => (3, 1)

theorem facs_prods (Dg : ℕ → E) (n : Fin 7) :
    rowVal Dg (facs n).1 * rowVal Dg (facs n).2 = Inst.Model.Ledger.prods Dg n := by
  fin_cases n <;> simp [facs, rowVal, Inst.Model.Ledger.prods, Inst.Model.Ledger.prodsOf, pow_two]

/-- From number 9 on an identity does not read the convolution sums. -/
theorem idnP_ws (np : Inst.Model.NormPar) (Ws Ws' Dg pv : ℕ → E) {k : ℕ} (hk : 9 ≤ k) :
    Inst.Model.Ledger.idnP np Ws Dg pv k = Inst.Model.Ledger.idnP np Ws' Dg pv k := by
  unfold Inst.Model.Ledger.idnP
  rw [if_neg (by omega), if_neg (by omega)]

end Tools

/-! ### What stays free -/

/-- The letters of the norms' stages that stay free. -/
structure NormPar0 (E : Type) [Field E] [Fintype E] [scl : Scl] where
  /-- the sizes -/
  D : Dim
  /-- the entries; how they are read as cells -/
  J : Type
  [finJ : Fintype J]
  rd : (J → E) → Cell → E
  two : (2 : E) ≠ 0
  /-- the order in which the squares' variables are bound -/
  eS : Fin (D.lL + 1 + (lDd D + D.lT)) ≃ Fin (D.lL + 1 + (lDd D + D.lT))
  /-- the squares' masks: the sent scalars'; the sumcheck's -/
  mkS : Fin D.nNu → Fin 9 → J
  wS : PIdx (ldPartFmt E (D.lL + 1 + (lDd D + D.lT)) (fun _ => 2) ++ [pDummy E 2]) → J
  cS : Bool → J
  /-- the rows' masks: the sent sums'; the sumcheck's -/
  mkP : Fin (D.nNu * 7) → J
  rP : J
  wP : PIdx (ldPartFmt E D.lT (fun _ => 2) ++ [pDummy E 2]) → J
  cP : Fin D.nNu × Fin 4 → J

attribute [instance] NormPar0.finJ

variable {E : Type} [Field E] [Fintype E] [scl : Scl]

/-- The extension of digit mm of norm ν's row at a point. -/
def digU (D : Dim) (t : Cell → E) (ν : ℕ) (u : ℕ → E) (mm : ℕ) : E :=
  Blocks.ext D.lT (fun i => led t ν i mm) u

namespace NormPar0
variable (P : NormPar0 E)

/-! ### The sums of squares -/

/-- The index of the vector of limbs, cut. -/
theorem pv_at (t : Cell → E) (c : E) (ν j y : ℕ) (hj : j < 2 ^ lDd P.D) (hy : y < 2 ^ P.D.lT) :
    Pv P.D t c (ν * 2 ^ (lDd P.D + P.D.lT) + (j * 2 ^ P.D.lT + y)) =
      if j < P.D.d then ∑ l ∈ range 5, c ^ l * bS P.D t ν l j y else 0 := by
  have hT : 0 < 2 ^ P.D.lT := Nat.pos_of_ne_zero (by positivity)
  have e0 : ν * 2 ^ (lDd P.D + P.D.lT) + (j * 2 ^ P.D.lT + y) =
      (ν * 2 ^ lDd P.D + j) * 2 ^ P.D.lT + y := by
    rw [pow_add]
    ring
  have e1 : ((ν * 2 ^ lDd P.D + j) * 2 ^ P.D.lT + y) / 2 ^ P.D.lT = ν * 2 ^ lDd P.D + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hy, Nat.zero_add]
  have e2 : ((ν * 2 ^ lDd P.D + j) * 2 ^ P.D.lT + y) % 2 ^ P.D.lT = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have e3 : (ν * 2 ^ lDd P.D + j) / 2 ^ lDd P.D = ν := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero (by positivity)),
      Nat.div_eq_of_lt hj, Nat.zero_add]
  have e4 : (ν * 2 ^ lDd P.D + j) % 2 ^ lDd P.D = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  unfold Pv Dim.T
  rw [e0, e1, e2, e3, e4]

/-- **The squares' law**: under the powers of c the convolution sums of a norm add up to the sum of
the squares of the limbs' vector. -/
theorem sq_law (p : Fin P.D.lT → E) (c : E) (t : Cell → E) (ν : ℕ) :
    (2⁻¹ : E) ^ lDd P.D * ∑ s : Fin 9, c ^ (s : ℕ) * Wt P.D t (Blocks.nat p) ν s =
      Blocks.ext (lDd P.D + P.D.lT)
        (fun x => Pv P.D t c (ν * 2 ^ (lDd P.D + P.D.lT) + x) *
          Pv P.D t c (ν * 2 ^ (lDd P.D + P.D.lT) + x))
        (Blocks.nat (Fin.append (fun _ : Fin (lDd P.D) => (2⁻¹ : E)) p)) := by
  rw [ext_half P.two]
  congr 1
  have hd : P.D.d ≤ 2 ^ lDd P.D := Nat.le_pow_clog (by norm_num) _
  have h1 : ∀ j ∈ range (2 ^ lDd P.D),
      Blocks.ext P.D.lT (fun y => Pv P.D t c (ν * 2 ^ (lDd P.D + P.D.lT) + (j * 2 ^ P.D.lT + y)) *
          Pv P.D t c (ν * 2 ^ (lDd P.D + P.D.lT) + (j * 2 ^ P.D.lT + y))) (Blocks.nat p) =
        if j < P.D.d then
          Blocks.ext P.D.lT (fun y => (∑ l ∈ range 5, c ^ l * bS P.D t ν l j y) ^ 2) (Blocks.nat p)
        else 0 := by
    intro j hj
    split_ifs with hjd
    · refine Blocks.ext_congr (fun y hy => ?_) _
      rw [P.pv_at t c ν j y (mem_range.1 hj) hy, if_pos hjd, pow_two]
    · refine Blocks.ext_zero_of_forall (fun y hy => ?_) _
      rw [P.pv_at t c ν j y (mem_range.1 hj) hy, if_neg hjd, mul_zero]
  rw [sum_congr rfl h1, ← sum_filter,
    show (range (2 ^ lDd P.D)).filter (· < P.D.d) = range P.D.d from by
      ext j
      simp only [mem_filter, mem_range]
      omega,
    ← Blocks.ext_sum, Fin.sum_univ_eq_sum_range (fun s => c ^ s * Wt P.D t (Blocks.nat p) ν s) 9]
  unfold Wt
  simp only [← Blocks.ext_smul]
  rw [← Blocks.ext_sum]
  exact Blocks.ext_congr (fun y _ => Inst.Model.Ledger.sum_pow_Wsum c P.D.d _) _

/-- The sums of squares, at the value. The state is the token point. -/
def sq : SquaresL E where
  J := P.J
  g := P.D.lL + 1
  k' := lDd P.D + P.D.lT
  n := P.D.nNu
  hn := by
    unfold Dim.nNu Dim.nl
    rw [pow_succ, Nat.mul_comm]
  ns := 9
  e := P.eS
  St := Fin P.D.lT → E
  vx := fun _ c m X => Pv P.D (P.rd m) c X
  pnt := fun p => Fin.append (fun _ => (2⁻¹ : E)) p
  scale := (2⁻¹ : E) ^ lDd P.D
  hs := pow_ne_zero _ (inv_ne_zero P.two)
  conv := fun p m ν s => Wt P.D (P.rd m) (Blocks.nat p) ν s
  rhs := fun p m ν s =>
    digU P.D (P.rd m) ν (Blocks.nat p) s +
      256 * Inst.Model.Ledger.cs (digU P.D (P.rd m) ν (Blocks.nat p)) (s + 1) -
      Inst.Model.Ledger.cs (digU P.D (P.rd m) ν (Blocks.nat p)) s
  law := fun p c m ν => P.sq_law p c (P.rd m) ν
  mkS := P.mkS
  wAt := P.wS
  cAt := P.cS
  Rd := fun _ _ => True

/-! ### The products of the rows -/

/-- A vector of nNu * 7 numbers, as norm ν's seven; 0 from number 7 on. -/
def pvOf (v : Fin (P.D.nNu * 7) → E) (ν : Fin P.D.nNu) (n : ℕ) : E :=
  if h : n < 7 then v (finProdFinEquiv (ν, ⟨n, h⟩)) else 0

/-- The products of the rows, at the value. The state is the token point. -/
def rows : RowsL E where
  J := P.J
  k := P.D.lT
  np := P.D.nNu * 7
  St := Fin P.D.lT → E
  A := Fin P.D.nNu × Fin 4
  vA := fun _ m a i => rowVal (led (P.rd m) a.1 i) a.2
  pr := fun n => (((finProdFinEquiv.symm n).1, (facs (finProdFinEquiv.symm n).2).1),
    ((finProdFinEquiv.symm n).1, (facs (finProdFinEquiv.symm n).2).2))
  pnt := fun p => p
  led := fun p m v => ∀ ν : Fin P.D.nNu, ∀ k, 9 ≤ k →
    Inst.Model.Ledger.idnP (npOf P.D ν) (fun _ => 0) (digU P.D (P.rd m) ν (Blocks.nat p))
      (P.pvOf v ν) k = 0
  mkAt := P.mkP
  rJ := P.rP
  wAt := P.wP
  cAt := P.cP
  Rd := fun _ _ => True

/-- A sum of the record is the extension of the library's product. -/
theorem rows_pA (p : Fin P.D.lT → E) (m : P.J → E) (ν : Fin P.D.nNu) (n : ℕ) :
    P.pvOf (P.rows.pA p m) ν n =
      Blocks.ext P.D.lT (fun i => Inst.Model.Ledger.prods (led (P.rd m) ν i) n) (Blocks.nat p) := by
  unfold pvOf
  split_ifs with h
  · unfold RowsL.pA
    refine Blocks.ext_congr (fun i _ => ?_) _
    simp only [rows, Equiv.symm_apply_apply]
    exact facs_prods _ ⟨n, h⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
    exact (Blocks.ext_zero_of_forall (fun _ _ => rfl) _).symm

/-- **What is claimed behind the token point gives that the defects' extensions vanish at it.** -/
theorem norms_atPt (p : Fin P.D.lT → E) (m : P.J → E) (h1 : P.sq.Phi p m) (h2 : P.rows.Idn p m)
    (k : ℕ) (ν : Fin P.D.nNu) :
    Blocks.ext P.D.lT (dJ P.D (P.rd m) k ν) (Blocks.nat p) = 0 := by
  have e := Inst.Model.Ledger.ext_idn P.D.lT (fun mm i => led (P.rd m) ν i mm) (Blocks.nat p)
    (npOf P.D ν)
    (fun s i => Inst.Model.Ledger.Wsum P.D.d (fun l j => bS P.D (P.rd m) ν l j i) s) k
  have e' : Blocks.ext P.D.lT (dJ P.D (P.rd m) k ν) (Blocks.nat p) = _ := e
  rw [e']
  by_cases hk : k < 9
  · rw [Inst.Model.Ledger.idnP_j1 _ _ _ _ hk]
    have h := h1 ν ⟨k, hk⟩
    have h' : Wt P.D (P.rd m) (Blocks.nat p) ν k =
        digU P.D (P.rd m) ν (Blocks.nat p) k +
          256 * Inst.Model.Ledger.cs (digU P.D (P.rd m) ν (Blocks.nat p)) (k + 1) -
          Inst.Model.Ledger.cs (digU P.D (P.rd m) ν (Blocks.nat p)) k := h
    have h'' : Blocks.ext P.D.lT
        (fun i => Inst.Model.Ledger.Wsum P.D.d (fun l j => bS P.D (P.rd m) ν l j i) k)
        (Blocks.nat p) = Wt P.D (P.rd m) (Blocks.nat p) ν k := rfl
    rw [h'', h']
    unfold digU
    ring
  · have h := h2 ν k (by omega)
    rw [idnP_ws _ _ (fun _ => 0) _ _ (by omega : 9 ≤ k)]
    have e2 : (fun n => Blocks.ext P.D.lT
        (fun i => Inst.Model.Ledger.prods (fun mm => led (P.rd m) ν i mm) n) (Blocks.nat p)) =
        P.pvOf (P.rows.pA p m) ν := funext fun n => (P.rows_pA p m ν n).symm
    rw [e2]
    exact h

end NormPar0
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.NormPar0.sq_law
#print axioms Cb.Pv.Lay.At.NormPar0.rows_pA
#print axioms Cb.Pv.Lay.At.NormPar0.norms_atPt
