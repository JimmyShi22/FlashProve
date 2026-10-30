-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/AddrFacts.lean: the addresses of an attention segment: under `Dim.OK`, every cell
  is inside its matrix, and no two cells have the same address. Proofs of the statements of
  Inst/Model/Att/Trace.lean on addresses, for all sizes.

  All is arithmetic of numbers written in mixed radices: n a + r with r < n determines a and r. The
  features of a matrix are cut into ranges, one for each kind of cell; in its range a kind is a
  mixed-radix number of its indices. (Feature: `featAt`, Inst/Model/Att/Trace.lean; a kind is a
  constructor of `Raw`.)

  Main names (statements and hypotheses: Inst/Model/Att/Trace.lean):
    `addrRange`: every cell inside its matrix.
    `addrInj`: no two cells at the same address.
    `addrBFacts`: the multiplicity bits B[t, θ, π] in the matrix b: each inside it, no two at one
      address, one at every address.

  Notation (Inst/Model/Att/Trace.lean, where no other file is named): `D` : `Dim`: the sizes of an
  attention segment (Inst/Model/Att/Index.lean); `K` : `Cols`: a column of ah holds 2^fh features;
  `C` : `Calls`: the numbers of the main lookup argument; `c` : `Raw`: the names of the cells
  (without the multiplicity bits); which names are cells: `Raw.Valid`; `Raw.c ρ jj b x`, a cell of
  an entry: cell number jj < 5 of the entry x of the region, for the pair b; k: the number of the
  cell in a value of several cells; `addr D K c` : `Mx` × ℕ × ℕ: the address of a cell: its matrix,
  row and column.
-/
import Inst.Model.Att.Trace

set_option autoImplicit false

namespace Inst.Model.AttSeg.AddrFacts

/-! ## Mixed radices -/

theorem mr_inj {n a a' r r' : ℕ} (hr : r < n) (hr' : r' < n) (h : n * a + r = n * a' + r') :
    a = a' ∧ r = r' := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have h1 := congrArg (· / n) h
  have h2 := congrArg (· % n) h
  simp only [Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.div_eq_of_lt hr', Nat.add_zero] at h1
  simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] at h2
  exact ⟨h1, h2⟩

theorem mr_lt {n m a r : ℕ} (ha : a < m) (hr : r < n) : n * a + r < n * m :=
  calc n * a + r < n * a + n := Nat.add_lt_add_left hr _
    _ = n * (a + 1) := (Nat.mul_succ n a).symm
    _ ≤ n * m := Nat.mul_le_mul_left n ha

theorem mr_dec {n m x : ℕ} (h : x < n * m) : x / n < m ∧ x % n < n ∧ n * (x / n) + x % n = x := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, Nat.zero_mul] at h; exact absurd h (Nat.not_lt_zero x)
    · exact h0
  exact ⟨Nat.div_lt_of_lt_mul h, Nat.mod_lt x hn, Nat.div_add_mod x n⟩

/-! ## A feature at a position -/

variable (D : Dim)

theorem T_pos : 0 < D.T := by rw [D.T_eq]; exact Nat.two_pow_pos _

theorem featAt_inj {f φ φ' i i' : ℕ} (hi : i < D.T) (hi' : i' < D.T)
    (h : featAt D f φ i = featAt D f φ' i') : φ = φ' ∧ i = i' := by
  unfold featAt at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  rw [Nat.mul_comm _ D.T, Nat.mul_comm _ D.T] at h1
  obtain ⟨h3, h4⟩ := mr_inj hi hi' h1
  refine ⟨?_, h4⟩
  rw [← Nat.div_add_mod φ (2 ^ f), ← Nat.div_add_mod φ' (2 ^ f), h2, h3]

theorem featAt_range {f Φ φ i : ℕ} (hd : 2 ^ f ∣ Φ) (hφ : φ < Φ) (hi : i < D.T) :
    (featAt D f φ i).1 < 2 ^ (f + D.lT) ∧ (featAt D f φ i).2 < Φ / 2 ^ f := by
  unfold featAt
  refine ⟨?_, ?_⟩
  · show φ % 2 ^ f * D.T + i < 2 ^ (f + D.lT)
    rw [pow_add, ← D.T_eq, Nat.mul_comm _ D.T, Nat.mul_comm _ D.T]
    exact mr_lt (Nat.mod_lt _ (Nat.two_pow_pos f)) hi
  · show φ / 2 ^ f < Φ / 2 ^ f
    obtain ⟨q, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos f)]
    exact Nat.div_lt_of_lt_mul hφ

theorem featAt_onto {f Φ row col : ℕ} (hr : row < 2 ^ (f + D.lT)) (hc : col < Φ / 2 ^ f) :
    ∃ φ i, φ < Φ ∧ i < D.T ∧ featAt D f φ i = (row, col) := by
  rw [pow_add, ← D.T_eq, Nat.mul_comm] at hr
  obtain ⟨h1, h2, h3⟩ := mr_dec hr
  refine ⟨2 ^ f * col + row / D.T, row % D.T, ?_, h2, ?_⟩
  · calc 2 ^ f * col + row / D.T < 2 ^ f * (Φ / 2 ^ f) := mr_lt hc h1
      _ ≤ Φ := Nat.mul_div_le Φ (2 ^ f)
  · unfold featAt
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h1, Nat.mul_add_div (Nat.two_pow_pos f),
      Nat.div_eq_of_lt h1, Nat.add_zero, Nat.mul_comm, h3]

/-! ## Pairs b, key/value heads g, query heads -/

theorem na_pos {b : ℕ} (hb : b < D.nb) : 0 < D.na := by
  unfold Dim.nb at hb
  rcases Nat.eq_zero_or_pos D.na with h | h
  · rw [h, Nat.mul_zero] at hb; exact absurd hb (Nat.not_lt_zero b)
  · exact h

theorem lam_lt {b : ℕ} (hb : b < D.nb) : D.lamOf b < D.nl := by
  unfold Dim.lamOf
  unfold Dim.nb at hb
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)

theorem head_lt {b g : ℕ} (hb : b < D.nb) (hg : g < D.nG) : D.head g b < D.nH := by
  unfold Dim.head Dim.nH Dim.aOf
  rw [Nat.mul_comm D.nG]
  exact mr_lt hg (Nat.mod_lt b (na_pos D hb))

theorem bg_inj {b b' g g' : ℕ} (hb : b < D.nb)
    (h1 : D.lamOf b = D.lamOf b') (h2 : D.head g b = D.head g' b') : b = b' ∧ g = g' := by
  have hna := na_pos D hb
  unfold Dim.head Dim.aOf at h2
  obtain ⟨h3, h4⟩ := mr_inj (Nat.mod_lt b hna) (Nat.mod_lt b' hna) h2
  unfold Dim.lamOf at h1
  exact ⟨by rw [← Nat.div_add_mod b D.na, ← Nat.div_add_mod b' D.na, h1, h4], h3⟩

theorem bg_onto {lam h : ℕ} (hl : lam < D.nl) (hh : h < D.nH) :
    ∃ b g, b < D.nb ∧ g < D.nG ∧ D.lamOf b = lam ∧ D.head g b = h := by
  unfold Dim.nH at hh
  rw [Nat.mul_comm] at hh
  obtain ⟨h1, h2, h3⟩ := mr_dec hh
  have hna : 0 < D.na := Nat.lt_of_le_of_lt (Nat.zero_le _) h2
  refine ⟨D.na * lam + h % D.na, h / D.na, ?_, h1, ?_, ?_⟩
  · unfold Dim.nb; rw [Nat.mul_comm D.nl]; exact mr_lt hl h2
  · unfold Dim.lamOf; rw [Nat.mul_add_div hna, Nat.div_eq_of_lt h2, Nat.add_zero]
  · unfold Dim.head Dim.aOf; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h2, h3]

/-! ## The four forms of a number of a feature without channels

(k | λ | h): a number in mixed radices, most significant part first. -/

/-- (k | λ | h) -/
def fK (k b g : ℕ) : ℕ := D.nH * (D.nl * k + D.lamOf b) + D.head g b
/-- (λ | k | h), k < lT -/
def fI (k b g : ℕ) : ℕ := D.nH * (D.lT * D.lamOf b + k) + D.head g b
/-- (λ | h) -/
def fL (b g : ℕ) : ℕ := D.nH * D.lamOf b + D.head g b
/-- (k | λ | g) -/
def fG (k lam g : ℕ) : ℕ := D.nG * (D.nl * k + lam) + g

theorem fK_inj {k k' b b' g g' : ℕ} (hb : b < D.nb) (hb' : b' < D.nb) (hg : g < D.nG)
    (hg' : g' < D.nG) (h : fK D k b g = fK D k' b' g') : k = k' ∧ b = b' ∧ g = g' := by
  obtain ⟨h1, h2⟩ := mr_inj (head_lt D hb hg) (head_lt D hb' hg') h
  obtain ⟨h3, h4⟩ := mr_inj (lam_lt D hb) (lam_lt D hb') h1
  exact ⟨h3, bg_inj D hb h4 h2⟩

theorem fK_lt {m k b g : ℕ} (hk : k < m) (hb : b < D.nb) (hg : g < D.nG) :
    fK D k b g < D.nH * (D.nl * m) :=
  mr_lt (mr_lt hk (lam_lt D hb)) (head_lt D hb hg)

theorem fK_onto {m x : ℕ} (hx : x < D.nH * (D.nl * m)) :
    ∃ k b g, k < m ∧ b < D.nb ∧ g < D.nG ∧ fK D k b g = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨h4, h5, h6⟩ := mr_dec h1
  obtain ⟨b, g, hb, hg, e1, e2⟩ := bg_onto D h5 h2
  exact ⟨x / D.nH / D.nl, b, g, h4, hb, hg, by unfold fK; rw [e1, e2, h6, h3]⟩

theorem fI_inj {k k' b b' g g' : ℕ} (hk : k < D.lT) (hk' : k' < D.lT) (hb : b < D.nb)
    (hb' : b' < D.nb) (hg : g < D.nG) (hg' : g' < D.nG) (h : fI D k b g = fI D k' b' g') :
    k = k' ∧ b = b' ∧ g = g' := by
  obtain ⟨h1, h2⟩ := mr_inj (head_lt D hb hg) (head_lt D hb' hg') h
  obtain ⟨h3, h4⟩ := mr_inj hk hk' h1
  exact ⟨h4, bg_inj D hb h3 h2⟩

theorem fI_lt {k b g : ℕ} (hk : k < D.lT) (hb : b < D.nb) (hg : g < D.nG) :
    fI D k b g < D.nH * (D.lT * D.nl) :=
  mr_lt (mr_lt (lam_lt D hb) hk) (head_lt D hb hg)

theorem fI_onto {x : ℕ} (hx : x < D.nH * (D.lT * D.nl)) :
    ∃ k b g, k < D.lT ∧ b < D.nb ∧ g < D.nG ∧ fI D k b g = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨h4, h5, h6⟩ := mr_dec h1
  obtain ⟨b, g, hb, hg, e1, e2⟩ := bg_onto D h4 h2
  exact ⟨x / D.nH % D.lT, b, g, h5, hb, hg, by unfold fI; rw [e1, e2, h6, h3]⟩

theorem fL_inj {b b' g g' : ℕ} (hb : b < D.nb) (hb' : b' < D.nb) (hg : g < D.nG)
    (hg' : g' < D.nG) (h : fL D b g = fL D b' g') : b = b' ∧ g = g' := by
  obtain ⟨h1, h2⟩ := mr_inj (head_lt D hb hg) (head_lt D hb' hg') h
  exact bg_inj D hb h1 h2

theorem fL_lt {b g : ℕ} (hb : b < D.nb) (hg : g < D.nG) : fL D b g < D.nH * D.nl :=
  mr_lt (lam_lt D hb) (head_lt D hb hg)

theorem fL_onto {x : ℕ} (hx : x < D.nH * D.nl) : ∃ b g, b < D.nb ∧ g < D.nG ∧ fL D b g = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨b, g, hb, hg, e1, e2⟩ := bg_onto D h1 h2
  exact ⟨b, g, hb, hg, by unfold fL; rw [e1, e2, h3]⟩

theorem fG_inj {k k' lam lam' g g' : ℕ} (hl : lam < D.nl) (hl' : lam' < D.nl) (hg : g < D.nG)
    (hg' : g' < D.nG) (h : fG D k lam g = fG D k' lam' g') :
    k = k' ∧ lam = lam' ∧ g = g' := by
  obtain ⟨h1, h2⟩ := mr_inj hg hg' h
  obtain ⟨h3, h4⟩ := mr_inj hl hl' h1
  exact ⟨h3, h4, h2⟩

theorem fG_lt {m k lam g : ℕ} (hk : k < m) (hl : lam < D.nl) (hg : g < D.nG) :
    fG D k lam g < D.nG * (D.nl * m) :=
  mr_lt (mr_lt hk hl) hg

theorem fG_onto {m x : ℕ} (hx : x < D.nG * (D.nl * m)) :
    ∃ k lam g, k < m ∧ lam < D.nl ∧ g < D.nG ∧ fG D k lam g = x := by
  obtain ⟨h1, h2, h3⟩ := mr_dec hx
  obtain ⟨h4, h5, h6⟩ := mr_dec h1
  exact ⟨x / D.nG / D.nl, x / D.nG % D.nl, x % D.nG, h4, h5, h2, by unfold fG; rw [h6, h3]⟩

/-! ## With channels -/

theorem ch_inj {u u' n n' : ℕ} (hn : n < D.ch)
    (hn' : n' < D.ch) (h : D.ch * u + n = D.ch * u' + n') : u = u' ∧ n = n' := mr_inj hn hn' h

/-! ## The sizes of the ranges -/

/-- features (λ | h) -/
def S1 : ℕ := D.nH * D.nl
/-- features (λ | k | h), k < lT -/
def S2 : ℕ := D.nH * (D.lT * D.nl)
/-- features (λ | h | n) -/
def S3 : ℕ := D.ch * (D.nH * D.nl)
/-- features (λ | g | n) -/
def S4 : ℕ := D.ch * (D.nG * D.nl)

/-- The number of the feature of a cell that is not a cell of an entry, as the start of the range of
its kind and a mixed-radix number. -/
def phi : Raw → ℕ
  | .c .. => 0
  | .mx k b g _ => fK D k b g
  | .den k b g _ => 4 * S1 D + fK D k b g
  | .ib k b g _ => 8 * S1 D + fI D k b g
  | .qh b g _ n => D.ch * fL D b g + n
  | .qh' b g _ n => S3 D + (D.ch * fL D b g + n)
  | .qry k b g _ n => D.ch * fK D k b g + n
  | .key k lam g _ n => 2 * S3 D + (D.ch * fG D k lam g + n)
  | .val k lam g _ n => 2 * S3 D + 2 * S4 D + (D.ch * fG D k lam g + n)
  | .out k b g _ n => 2 * S3 D + 4 * S4 D + (D.ch * fK D k b g + n)

/-- its position -/
def pos : Raw → ℕ
  | .c .. => 0
  | .mx _ _ _ i => i
  | .den _ _ _ i => i
  | .ib _ _ _ i => i
  | .qh _ _ i _ => i
  | .qh' _ _ i _ => i
  | .qry _ _ _ i _ => i
  | .key _ _ _ j _ => j
  | .val _ _ _ j _ => j
  | .out _ _ _ i _ => i

/-- its matrix -/
def mat : Raw → Mx
  | .c .. => .as
  | .mx .. => .ah
  | .den .. => .ah
  | .ib .. => .ah
  | .qh .. => .ao
  | .qh' .. => .ao
  | _ => .qa

/-- bits of the features in a column -/
def fBits (K : Cols) : Mx → ℕ
  | .ah => K.fh
  | _ => D.ln - 1

/-- the number of features of a matrix -/
def Phi : Mx → ℕ
  | .ah => 8 * S1 D + S2 D
  | .ao => 2 * S3 D
  | .qa => 4 * S3 D + 4 * S4 D
  | _ => 0

def IsC : Raw → Prop
  | .c .. => True
  | _ => False

theorem addr_feat (K : Cols) (c : Raw) (hc : ¬ IsC c) :
    addr D K c = (mat c, featAt D (fBits D K (mat c)) (phi D c) (pos c)) := by
  cases c with
  | c ρ jj b x => exact absurd trivial hc
  | mx k b g i => rfl
  | den k b g i =>
    simp only [addr, mat, fBits, phi, pos, S1, fK]
    congr 2
    ring
  | ib k b g i =>
    simp only [addr, mat, fBits, phi, pos, S1, fI]
    congr 2
    ring
  | qh b g i n =>
    simp only [addr, mat, fBits, phi, pos, fL]
    congr 2
    ring
  | qh' b g i n =>
    simp only [addr, mat, fBits, phi, pos, fL, S3]
    congr 2
    ring
  | qry k b g i n =>
    simp only [addr, mat, fBits, phi, pos, fK]
    congr 2
    ring
  | out k b g i n =>
    simp only [addr, mat, fBits, phi, pos, fK, S3, S4]
    congr 2
    ring
  | key k lam g j n =>
    simp only [addr, mat, fBits, phi, pos, fG, S3]
    congr 2
    ring
  | val k lam g j n =>
    simp only [addr, mat, fBits, phi, pos, fG, S3, S4]
    congr 2
    ring

/-! ## The range of each kind -/

/-- where the range of the kind of a cell starts -/
def lo : Raw → ℕ
  | .den .. => 4 * S1 D
  | .ib .. => 8 * S1 D
  | .qh' .. => S3 D
  | .key .. => 2 * S3 D
  | .val .. => 2 * S3 D + 2 * S4 D
  | .out .. => 2 * S3 D + 4 * S4 D
  | _ => 0

/-- its length -/
def sz : Raw → ℕ
  | .c .. => 1
  | .mx .. => 4 * S1 D
  | .den .. => 4 * S1 D
  | .ib .. => S2 D
  | .qh .. => S3 D
  | .qh' .. => S3 D
  | .qry .. => 2 * S3 D
  | .key .. => 2 * S4 D
  | .val .. => 2 * S4 D
  | .out .. => 2 * S3 D

theorem fK4 {k b g : ℕ} (hk : k < 4) (hb : b < D.nb) (hg : g < D.nG) : fK D k b g < 4 * S1 D := by
  have := fK_lt D hk hb hg
  have e : D.nH * (D.nl * 4) = 4 * S1 D := by unfold S1; ring
  omega

theorem fK2 {k b g n : ℕ} (hk : k < 2) (hb : b < D.nb) (hg : g < D.nG) (hn : n < D.ch) :
    D.ch * fK D k b g + n < 2 * S3 D := by
  have := mr_lt (fK_lt D hk hb hg) hn
  have e : D.ch * (D.nH * (D.nl * 2)) = 2 * S3 D := by unfold S3; ring
  omega

theorem fG2 {k lam g n : ℕ} (hk : k < 2) (hl : lam < D.nl) (hg : g < D.nG) (hn : n < D.ch) :
    D.ch * fG D k lam g + n < 2 * S4 D := by
  have := mr_lt (fG_lt D hk hl hg) hn
  have e : D.ch * (D.nG * (D.nl * 2)) = 2 * S4 D := by unfold S4; ring
  omega

theorem fL1 {b g n : ℕ} (hb : b < D.nb) (hg : g < D.nG) (hn : n < D.ch) :
    D.ch * fL D b g + n < S3 D :=
  mr_lt (fL_lt D hb hg) hn

theorem phi_in (c : Raw) (hv : c.Valid D) : lo D c ≤ phi D c ∧ phi D c < lo D c + sz D c := by
  cases c with
  | c ρ jj b x => exact ⟨le_rfl, by simp [lo, sz, phi]⟩
  | mx k b g i => have := fK4 D hv.1 hv.2.1 hv.2.2.1; simp only [lo, sz, phi]; omega
  | den k b g i => have := fK4 D hv.1 hv.2.1 hv.2.2.1; simp only [lo, sz, phi]; omega
  | ib k b g i => have := fI_lt D hv.1 hv.2.1 hv.2.2.1; simp only [lo, sz, phi, S2]; omega
  | qh b g i n => have := fL1 D hv.1 hv.2.1 hv.2.2.2; simp only [lo, sz, phi]; omega
  | qh' b g i n => have := fL1 D hv.1 hv.2.1 hv.2.2.2; simp only [lo, sz, phi]; omega
  | qry k b g i n => have := fK2 D hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2; simp only [lo, sz, phi]; omega
  | out k b g i n => have := fK2 D hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2; simp only [lo, sz, phi]; omega
  | key k lam g j n => have := fG2 D hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2; simp only [lo, sz, phi]; omega
  | val k lam g j n => have := fG2 D hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2; simp only [lo, sz, phi]; omega

theorem phi_lt (c : Raw) (hv : c.Valid D) (hc : ¬ IsC c) :
    phi D c < Phi D (mat c) ∧ pos c < D.T := by
  have h := (phi_in D c hv).2
  cases c with
  | c ρ jj b x => exact absurd trivial hc
  | mx k b g i => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2⟩
  | den k b g i => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2⟩
  | ib k b g i => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2⟩
  | qh b g i n => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.1⟩
  | qh' b g i n => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.1⟩
  | qry k b g i n => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2.1⟩
  | out k b g i n => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2.1⟩
  | key k lam g j n => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2.1⟩
  | val k lam g j n => simp only [lo, sz, Phi, mat, pos] at h ⊢; exact ⟨by omega, hv.2.2.2.1⟩

/-- the number of the kind of a cell -/
def kind : Raw → ℕ
  | .c .. => 0
  | .mx .. => 1
  | .den .. => 2
  | .ib .. => 3
  | .qh .. => 4
  | .qh' .. => 5
  | .qry .. => 6
  | .key .. => 7
  | .val .. => 8
  | .out .. => 9

/-- For valid cells that are not cells of an entry: in one matrix the ranges of two kinds do not
meet. -/
theorem kind_eq (c c' : Raw) (hv : c.Valid D) (hv' : c'.Valid D) (hc : ¬ IsC c) (hc' : ¬ IsC c')
    (hm : mat c = mat c') (hφ : phi D c = phi D c') : kind c = kind c' := by
  have h1 := phi_in D c hv
  have h2 := phi_in D c' hv'
  rw [hφ] at h1
  cases c <;> cases c' <;>
    first
    | rfl
    | exact absurd trivial hc
    | exact absurd trivial hc'
    | (exfalso; simp [mat] at hm; done)
    | (exfalso; simp only [lo, sz] at h1 h2; omega)

theorem phi_inj (c c' : Raw) (hv : c.Valid D) (hv' : c'.Valid D) (hc : ¬ IsC c) (hc' : ¬ IsC c')
    (hm : mat c = mat c') (hφ : phi D c = phi D c') (hp : pos c = pos c') : c = c' := by
  have hk := kind_eq D c c' hv hv' hc hc' hm hφ
  cases c <;> cases c' <;> first | (exfalso; simp [kind] at hk; done) | skip
  · exact absurd trivial hc
  · obtain ⟨e1, e2, e3⟩ := fK_inj D hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 hφ
    obtain rfl := hp
    rw [e1, e2, e3]
    rfl
  · obtain ⟨e1, e2, e3⟩ := fK_inj D hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 (Nat.add_left_cancel hφ)
    obtain rfl := hp
    rw [e1, e2, e3]
    rfl
  · obtain ⟨e1, e2, e3⟩ :=
      fI_inj D hv.1 hv'.1 hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 (Nat.add_left_cancel hφ)
    obtain rfl := hp
    rw [e1, e2, e3]
    rfl
  · obtain ⟨e0, e4⟩ := ch_inj D hv.2.2.2 hv'.2.2.2 hφ
    obtain ⟨e2, e3⟩ := fL_inj D hv.1 hv'.1 hv.2.1 hv'.2.1 e0
    obtain rfl := hp
    rw [e2, e3, e4]
    rfl
  · obtain ⟨e0, e4⟩ := ch_inj D hv.2.2.2 hv'.2.2.2 (Nat.add_left_cancel hφ)
    obtain ⟨e2, e3⟩ := fL_inj D hv.1 hv'.1 hv.2.1 hv'.2.1 e0
    obtain rfl := hp
    rw [e2, e3, e4]
    rfl
  · obtain ⟨e0, e4⟩ := ch_inj D hv.2.2.2.2 hv'.2.2.2.2 hφ
    obtain ⟨e1, e2, e3⟩ := fK_inj D hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 e0
    obtain rfl := hp
    rw [e1, e2, e3, e4]
    rfl
  · obtain ⟨e0, e4⟩ := ch_inj D hv.2.2.2.2 hv'.2.2.2.2 (Nat.add_left_cancel hφ)
    obtain ⟨e1, e2, e3⟩ := fK_inj D hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 e0
    obtain rfl := hp
    rw [e1, e2, e3, e4]
    rfl
  · obtain ⟨e0, e4⟩ := ch_inj D hv.2.2.2.2 hv'.2.2.2.2 (Nat.add_left_cancel hφ)
    obtain ⟨e1, e2, e3⟩ := fG_inj D hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 e0
    obtain rfl := hp
    rw [e1, e2, e3, e4]
    rfl
  · obtain ⟨e0, e4⟩ := ch_inj D hv.2.2.2.2 hv'.2.2.2.2 (Nat.add_left_cancel hφ)
    obtain ⟨e1, e2, e3⟩ := fG_inj D hv.2.1 hv'.2.1 hv.2.2.1 hv'.2.2.1 e0
    obtain rfl := hp
    rw [e1, e2, e3, e4]
    rfl

/-! ## Every feature is the feature of a cell -/

theorem ch_onto {m x : ℕ} (hx : x < D.ch * m) : ∃ u n, u < m ∧ n < D.ch ∧ D.ch * u + n = x :=
  ⟨x / D.ch, x % D.ch, (mr_dec hx).1, (mr_dec hx).2.1, (mr_dec hx).2.2⟩

theorem phi_onto (μ : Mx) (φ i : ℕ) (hφ : φ < Phi D μ) (hi : i < D.T) :
    ∃ c : Raw, c.Valid D ∧ ¬ IsC c ∧ mat c = μ ∧ phi D c = φ ∧ pos c = i := by
  have e4 : D.nH * (D.nl * 4) = 4 * S1 D := by unfold S1; ring
  have e23 : D.ch * (D.nH * (D.nl * 2)) = 2 * S3 D := by unfold S3; ring
  have e24 : D.ch * (D.nG * (D.nl * 2)) = 2 * S4 D := by unfold S4; ring
  cases μ with
  | as => exact absurd hφ (Nat.not_lt_zero φ)
  | b => exact absurd hφ (Nat.not_lt_zero φ)
  | ah =>
    have hφ' : φ < 8 * S1 D + S2 D := hφ
    by_cases h1 : φ < 4 * S1 D
    · obtain ⟨k, b, g, hk, hb, hg, e⟩ := fK_onto D (m := 4) (x := φ) (by omega)
      exact ⟨.mx k b g i, ⟨hk, hb, hg, hi⟩, fun h => h, rfl, e, rfl⟩
    · by_cases h2 : φ < 8 * S1 D
      · obtain ⟨k, b, g, hk, hb, hg, e⟩ := fK_onto D (m := 4) (x := φ - 4 * S1 D) (by omega)
        exact ⟨.den k b g i, ⟨hk, hb, hg, hi⟩, fun h => h,
          rfl, by show 4 * S1 D + fK D k b g = φ; omega, rfl⟩
      · obtain ⟨k, b, g, hk, hb, hg, e⟩ :=
          fI_onto D (x := φ - 8 * S1 D) (by unfold S2 at hφ'; omega)
        exact ⟨.ib k b g i, ⟨hk, hb, hg, hi⟩, fun h => h,
          rfl, by show 8 * S1 D + fI D k b g = φ; omega, rfl⟩
  | ao =>
    have hφ' : φ < 2 * S3 D := hφ
    by_cases h1 : φ < S3 D
    · obtain ⟨u, n, hu, hn, e⟩ := ch_onto D (m := D.nH * D.nl) (x := φ) h1
      obtain ⟨b, g, hb, hg, e'⟩ := fL_onto D hu
      exact ⟨.qh b g i n, ⟨hb, hg, hi, hn⟩, fun h => h, rfl,
        by show D.ch * fL D b g + n = φ; rw [e', e], rfl⟩
    · obtain ⟨u, n, hu, hn, e⟩ :=
        ch_onto D (m := D.nH * D.nl) (x := φ - S3 D) (by show φ - S3 D < S3 D; omega)
      obtain ⟨b, g, hb, hg, e'⟩ := fL_onto D hu
      exact ⟨.qh' b g i n, ⟨hb, hg, hi, hn⟩, fun h => h, rfl,
        by show S3 D + (D.ch * fL D b g + n) = φ; rw [e', e]; omega, rfl⟩
  | qa =>
    have hφ' : φ < 4 * S3 D + 4 * S4 D := hφ
    by_cases h1 : φ < 2 * S3 D
    · obtain ⟨u, n, hu, hn, e⟩ := ch_onto D (m := D.nH * (D.nl * 2)) (x := φ) (by omega)
      obtain ⟨k, b, g, hk, hb, hg, e'⟩ := fK_onto D hu
      exact ⟨.qry k b g i n, ⟨hk, hb, hg, hi, hn⟩, fun h => h,
        rfl, by show D.ch * fK D k b g + n = φ; rw [e', e], rfl⟩
    · by_cases h2 : φ < 2 * S3 D + 2 * S4 D
      · obtain ⟨u, n, hu, hn, e⟩ :=
          ch_onto D (m := D.nG * (D.nl * 2)) (x := φ - 2 * S3 D) (by omega)
        obtain ⟨k, lam, g, hk, hl, hg, e'⟩ := fG_onto D hu
        exact ⟨.key k lam g i n, ⟨hk, hl, hg, hi, hn⟩, fun h => h, rfl,
          by show 2 * S3 D + (D.ch * fG D k lam g + n) = φ; rw [e', e]; omega, rfl⟩
      · by_cases h3 : φ < 2 * S3 D + 4 * S4 D
        · obtain ⟨u, n, hu, hn, e⟩ :=
            ch_onto D (m := D.nG * (D.nl * 2)) (x := φ - (2 * S3 D + 2 * S4 D)) (by omega)
          obtain ⟨k, lam, g, hk, hl, hg, e'⟩ := fG_onto D hu
          exact ⟨.val k lam g i n, ⟨hk, hl, hg, hi, hn⟩, fun h => h, rfl,
            by show 2 * S3 D + 2 * S4 D + (D.ch * fG D k lam g + n) = φ; rw [e', e]; omega, rfl⟩
        · obtain ⟨u, n, hu, hn, e⟩ :=
            ch_onto D (m := D.nH * (D.nl * 2)) (x := φ - (2 * S3 D + 4 * S4 D)) (by omega)
          obtain ⟨k, b, g, hk, hb, hg, e'⟩ := fK_onto D hu
          exact ⟨.out k b g i n, ⟨hk, hb, hg, hi, hn⟩, fun h => h, rfl,
            by show 2 * S3 D + 4 * S4 D + (D.ch * fK D k b g + n) = φ; rw [e', e]; omega, rfl⟩

/-! ## The matrices of features: rows, columns, whole columns -/

theorem lRow_feat (K : Cols) (μ : Mx) (h : μ = .ah ∨ μ = .ao ∨ μ = .qa) :
    lRow D K μ = fBits D K μ + D.lT := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem nCol_feat (K : Cols) (C : Calls) (μ : Mx) (h : μ = .ah ∨ μ = .ao ∨ μ = .qa) :
    nCol D K C μ = Phi D μ / 2 ^ fBits D K μ := by
  rcases h with rfl | rfl | rfl
  · show (8 * D.nl * D.nH + D.nl * D.lT * D.nH) / 2 ^ K.fh = (8 * S1 D + S2 D) / 2 ^ K.fh
    congr 1
    unfold S1 S2; ring
  · show 2 * D.nl * D.nH * D.ch / 2 ^ (D.ln - 1) = 2 * S3 D / 2 ^ (D.ln - 1)
    congr 1
    unfold S3; ring
  · show (4 * D.nl * D.nH * D.ch + 4 * D.nl * D.nG * D.ch) / 2 ^ (D.ln - 1) =
      (4 * S3 D + 4 * S4 D) / 2 ^ (D.ln - 1)
    congr 1
    unfold S3 S4; ring

theorem dvd_ch : 2 ^ (D.ln - 1) ∣ D.ch := pow_dvd_pow 2 (Nat.sub_le D.ln 1)

theorem dvd_Phi (K : Cols) (hK : D.OK K) (μ : Mx) (h : μ = .ah ∨ μ = .ao ∨ μ = .qa) :
    2 ^ fBits D K μ ∣ Phi D μ := by
  rcases h with rfl | rfl | rfl
  · have e : 8 * D.nl * D.nH + D.nl * D.lT * D.nH = 8 * S1 D + S2 D := by unfold S1 S2; ring
    show 2 ^ K.fh ∣ 8 * S1 D + S2 D
    rw [← e]; exact hK.ah
  · show 2 ^ (D.ln - 1) ∣ 2 * S3 D
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_ch D) _) _
  · show 2 ^ (D.ln - 1) ∣ 4 * S3 D + 4 * S4 D
    exact Nat.dvd_add (Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_ch D) _) _)
      (Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_ch D) _) _)

theorem mat_feat (c : Raw) (hc : ¬ IsC c) : mat c = .ah ∨ mat c = .ao ∨ mat c = .qa := by
  cases c <;> first | exact absurd trivial hc | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

/-! ## The cells of the entries: the matrix as -/

/-- addresses of region M, of region D -/
def SM : ℕ := 2 ^ D.lM * (D.nb * 5)
def SD : ℕ := 2 ^ D.lD * (D.nb * 5)

/-- the address of a cell of an entry -/
def adr : Reg → ℕ → ℕ → ℕ → ℕ
  | .M, jj, b, x => 2 ^ D.lM * (D.nb * jj + b) + x
  | .D, jj, b, x => SM D + (2 ^ D.lD * (D.nb * jj + b) + x)

theorem addr_c (K : Cols) (ρ : Reg) (jj b x : ℕ) :
    addr D K (.c ρ jj b x) = (.as, asAt D K (adr D ρ jj b x)) := by
  cases ρ with
  | M =>
    simp only [addr, adr]
    congr 2
    ring
  | D =>
    simp only [addr, adr, SM]
    congr 2
    ring

theorem asAt_inj (K : Cols) {A A' : ℕ} (h : asAt D K A = asAt D K A') : A = A' := by
  unfold asAt at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  rw [← Nat.div_add_mod A (2 ^ lRow D K .as), ← Nat.div_add_mod A' (2 ^ lRow D K .as), h1, h2]

theorem loc_inj {l jj jj' b b' x x' : ℕ} (hb : b < D.nb) (hb' : b' < D.nb) (hx : x < 2 ^ l)
    (hx' : x' < 2 ^ l) (h : 2 ^ l * (D.nb * jj + b) + x = 2 ^ l * (D.nb * jj' + b') + x') :
    jj = jj' ∧ b = b' ∧ x = x' := by
  obtain ⟨h1, h2⟩ := mr_inj hx hx' h
  obtain ⟨h3, h4⟩ := mr_inj hb hb' h1
  exact ⟨h3, h4, h2⟩

theorem loc_lt {l jj b x : ℕ} (hj : jj < 5) (hb : b < D.nb) (hx : x < 2 ^ l) :
    2 ^ l * (D.nb * jj + b) + x < 2 ^ l * (D.nb * 5) :=
  mr_lt (mr_lt hj hb) hx

theorem loc_onto {l A : ℕ} (h : A < 2 ^ l * (D.nb * 5)) :
    ∃ jj b x, jj < 5 ∧ b < D.nb ∧ x < 2 ^ l ∧ 2 ^ l * (D.nb * jj + b) + x = A := by
  obtain ⟨h1, h2, h3⟩ := mr_dec h
  obtain ⟨h4, h5, h6⟩ := mr_dec h1
  exact ⟨A / 2 ^ l / D.nb, A / 2 ^ l % D.nb, A % 2 ^ l, h4, h5, h2, by rw [h6, h3]⟩

theorem adr_lt {ρ : Reg} {jj b x : ℕ} (hv : (Raw.c ρ jj b x).Valid D) :
    adr D ρ jj b x < SM D + SD D := by
  cases ρ with
  | M => have := loc_lt D hv.1 hv.2.1 hv.2.2; show 2 ^ D.lM * (D.nb * jj + b) + x < SM D + SD D; unfold SM; exact Nat.lt_add_right _ this
  | D => have := loc_lt D hv.1 hv.2.1 hv.2.2; show SM D + (2 ^ D.lD * (D.nb * jj + b) + x) < SM D + SD D; unfold SD; exact Nat.add_lt_add_left this _

theorem adr_inj {ρ ρ' : Reg} {jj jj' b b' x x' : ℕ} (hv : (Raw.c ρ jj b x).Valid D)
    (hv' : (Raw.c ρ' jj' b' x').Valid D) (h : adr D ρ jj b x = adr D ρ' jj' b' x') :
    Raw.c ρ jj b x = Raw.c ρ' jj' b' x' := by
  cases ρ <;> cases ρ'
  · obtain ⟨e1, e2, e3⟩ := loc_inj D hv.2.1 hv'.2.1 hv.2.2 hv'.2.2 h
    rw [e1, e2, e3]
  · exfalso
    have h1 : 2 ^ D.lM * (D.nb * jj + b) + x < SM D := loc_lt D hv.1 hv.2.1 hv.2.2
    have h2 : 2 ^ D.lM * (D.nb * jj + b) + x = SM D + (2 ^ D.lD * (D.nb * jj' + b') + x') := h
    omega
  · exfalso
    have h1 : 2 ^ D.lM * (D.nb * jj' + b') + x' < SM D := loc_lt D hv'.1 hv'.2.1 hv'.2.2
    have h2 : SM D + (2 ^ D.lD * (D.nb * jj + b) + x) = 2 ^ D.lM * (D.nb * jj' + b') + x' := h
    omega
  · obtain ⟨e1, e2, e3⟩ := loc_inj D hv.2.1 hv'.2.1 hv.2.2 hv'.2.2 (Nat.add_left_cancel h)
    rw [e1, e2, e3]

theorem adr_onto {A : ℕ} (h : A < SM D + SD D) :
    ∃ ρ jj b x, (Raw.c ρ jj b x).Valid D ∧ adr D ρ jj b x = A := by
  by_cases h1 : A < SM D
  · obtain ⟨jj, b, x, hj, hb, hx, e⟩ := loc_onto D (l := D.lM) h1
    exact ⟨.M, jj, b, x, ⟨hj, hb, hx⟩, e⟩
  · obtain ⟨jj, b, x, hj, hb, hx, e⟩ :=
      loc_onto D (l := D.lD) (A := A - SM D) (by show A - SM D < SD D; omega)
    exact ⟨.D, jj, b, x, ⟨hj, hb, hx⟩, by show SM D + (2 ^ D.lD * (D.nb * jj + b) + x) = A; omega⟩

theorem nCol_as (K : Cols) (C : Calls) : nCol D K C .as = (SM D + SD D) / 2 ^ lRow D K .as := by
  show (5 * D.nb * 2 ^ D.lM + 5 * D.nb * 2 ^ D.lD) / 2 ^ lRow D K .as = _
  congr 1
  unfold SM SD; ring

theorem dvd_as (K : Cols) : 2 ^ lRow D K .as ∣ SM D + SD D := by
  have h1 : 2 ^ lRow D K .as ∣ 2 ^ D.lM :=
    pow_dvd_pow 2 (by show D.lP + 1 + D.lB + D.lB ≤ D.lM; unfold Dim.lM; omega)
  have h2 : 2 ^ lRow D K .as ∣ 2 ^ D.lD :=
    pow_dvd_pow 2 (by show D.lP + 1 + D.lB + D.lB ≤ D.lD; unfold Dim.lD; omega)
  exact Nat.dvd_add (Dvd.dvd.mul_right h1 _) (Dvd.dvd.mul_right h2 _)

/-! ## The statements -/

theorem addrRange : Spec.addrRange := by
  intro D K C hK c hv
  by_cases hc : IsC c
  · cases c with
    | c ρ jj b x =>
      rw [addr_c]
      have hA := adr_lt D hv
      obtain ⟨q, hq⟩ := dvd_as D K
      refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
      show adr D ρ jj b x / 2 ^ lRow D K .as < nCol D K C .as
      rw [nCol_as, hq, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
      exact Nat.div_lt_of_lt_mul (by rw [← hq]; exact hA)
    | _ => exact absurd hc (fun h => h)
  · rw [addr_feat D K c hc]
    have hm := mat_feat c hc
    obtain ⟨h1, h2⟩ := phi_lt D c hv hc
    have := featAt_range D (dvd_Phi D K hK _ hm) h1 h2
    show _ < 2 ^ lRow D K (mat c) ∧ _ < nCol D K C (mat c)
    rw [lRow_feat D K _ hm, nCol_feat D K C _ hm]
    exact this

theorem mat_ne_as (c : Raw) (hc : ¬ IsC c) : mat c ≠ .as := by
  rcases mat_feat c hc with h | h | h <;> rw [h] <;> decide

theorem addrInj : Spec.addrInj := by
  intro D K _ c c' hv hv' h
  by_cases hc : IsC c <;> by_cases hc' : IsC c'
  · cases c with
    | c ρ jj b x =>
      cases c' with
      | c ρ' jj' b' x' =>
        rw [addr_c, addr_c] at h
        exact adr_inj D hv hv' (asAt_inj D K (Prod.mk.inj h).2)
      | _ => exact absurd hc' (fun h => h)
    | _ => exact absurd hc (fun h => h)
  · cases c with
    | c ρ jj b x =>
      rw [addr_c, addr_feat D K c' hc'] at h
      exact absurd (Prod.mk.inj h).1.symm (mat_ne_as c' hc')
    | _ => exact absurd hc (fun h => h)
  · cases c' with
    | c ρ jj b x =>
      rw [addr_c, addr_feat D K c hc] at h
      exact absurd (Prod.mk.inj h).1 (mat_ne_as c hc)
    | _ => exact absurd hc' (fun h => h)
  · rw [addr_feat D K c hc, addr_feat D K c' hc'] at h
    obtain ⟨hm, hf⟩ := Prod.mk.inj h
    rw [← hm] at hf
    obtain ⟨h1, h2⟩ := featAt_inj D (phi_lt D c hv hc).2 (phi_lt D c' hv' hc').2 hf
    exact phi_inj D c c' hv hv' hc hc' hm h1 h2


theorem addrBFacts : Spec.addrBFacts := by
  intro D K C
  have e14 : 2 ^ lRow D K .b = 16384 := by show 2 ^ 14 = 16384; norm_num
  have eC : nCol D K C .b = 128 * C.NT := rfl
  refine ⟨fun t ht θ hθ π hπ => ?_,
    fun t ht π hπ t' ht' π' hπ' θ θ' h => ?_,
    fun row hrow col hcol => ?_⟩
  · rw [e14, eC]
    unfold addrB
    norm_num at ht ⊢
    constructor <;> omega
  · unfold addrB at h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    norm_num at ht ht' h1 h2
    omega
  · rw [e14] at hrow
    rw [eC] at hcol
    refine ⟨512 * (col % 128) + row / 32, by norm_num; omega, col / 128,
      by omega, row % 32, by omega, ?_⟩
    unfold addrB
    norm_num
    constructor <;> omega

end Inst.Model.AttSeg.AddrFacts
