-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/CastValid.lean: the field relation of a feed-forward segment reads valid cells only,
  if f = 2 fe.

  In Inst/Model/FF/Trace.lean a trace is a function on all names of cells. Every cell that a
  looked-up value (key) of the relation or one of its identities reads has a valid name.
    `key_congr`, `idn_congr` over the integers, for the keys and identities that belong to the
                             relation
    `rfraw_congr`            for `RFraw` (Inst/Model/FF/Cast.lean) over any commutative ring
  The only condition on the sizes is that a layer has twice as many hidden units as an expert
  (`Dim.OK.f`). Small lemmas are in the namespace `Inst.Model.FFSeg.CastValid`.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.
-/
import Inst.Model.FF.NoWrapNorm

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset
open Site (site high)

namespace CastValid

/-! ## The ledger reads 99 bytes -/

section Led
variable {D₁ D₂ : ℕ → ℤ} (e : ∀ n < 99, D₁ n = D₂ n)
include e

omit scl in
theorem b256_eq {a n : ℕ} (h : a + n ≤ 99) : Ledger.b256 D₁ a n = Ledger.b256 D₂ a n :=
  sum_congr rfl fun l hl => by rw [e (a + l) (by have := mem_range.1 hl; omega)]

omit scl in
theorem R_eq : Ledger.R D₁ = Ledger.R D₂ := by
  unfold Ledger.R Ledger.Rlo Ledger.Rhi
  rw [b256_eq e (by norm_num), b256_eq e (by norm_num)]

omit scl in
theorem cs_eq {s : ℕ} (hs : s ≤ 9) : Ledger.cs D₁ s = Ledger.cs D₂ s := by
  unfold Ledger.cs
  split_ifs
  · rfl
  · exact e 9 (by norm_num)
  · rw [b256_eq e (by omega)]

omit scl in
theorem idn_eq (np : NormPar) {Ws Ws' : ℕ → ℤ} (hW : ∀ s, Ws s = Ws' s) {k : ℕ} (hk : k < 17) :
    Ledger.idn np Ws D₁ k = Ledger.idn np Ws' D₂ k := by
  have sa : Ledger.sa D₁ = Ledger.sa D₂ := by
    unfold Ledger.sa
    rw [e 58 (by norm_num), e 59 (by norm_num), e 60 (by norm_num), e 61 (by norm_num)]
  have sb : Ledger.sb D₁ = Ledger.sb D₂ := by
    unfold Ledger.sb
    rw [e 62 (by norm_num), e 63 (by norm_num)]
  have s0 : Ledger.s0 D₁ = Ledger.s0 D₂ := e 59 (by norm_num)
  have sig : Ledger.sig D₁ = Ledger.sig D₂ := by unfold Ledger.sig; rw [sa, sb]
  have kc : Ledger.kc D₁ = Ledger.kc D₂ := by unfold Ledger.kc; rw [e 79 (by norm_num)]
  have Vlo : Ledger.Vlo D₁ = Ledger.Vlo D₂ := b256_eq e (by norm_num)
  have Vhi : Ledger.Vhi D₁ = Ledger.Vhi D₂ := b256_eq e (by norm_num)
  have l1 : Ledger.l1 D₁ = Ledger.l1 D₂ := b256_eq e (by norm_num)
  have h1 : Ledger.h1 D₁ = Ledger.h1 D₂ := b256_eq e (by norm_num)
  have Blo : Ledger.Blo D₁ = Ledger.Blo D₂ := b256_eq e (by norm_num)
  have Bhi : Ledger.Bhi D₁ = Ledger.Bhi D₂ := b256_eq e (by norm_num)
  have Rlo : Ledger.Rlo D₁ = Ledger.Rlo D₂ := b256_eq e (by norm_num)
  have Rhi : Ledger.Rhi D₁ = Ledger.Rhi D₂ := b256_eq e (by norm_num)
  have q1 : Ledger.q1 D₁ = Ledger.q1 D₂ := b256_eq e (by norm_num)
  have rr : Ledger.rr D₁ = Ledger.rr D₂ := b256_eq e (by norm_num)
  have rq : Ledger.rq D₁ = Ledger.rq D₂ := b256_eq e (by norm_num)
  unfold Ledger.idn
  by_cases h9 : k < 9
  · rw [if_pos h9, if_pos h9, hW, cs_eq e (by omega), cs_eq e (by omega), e k (by omega)]
  · rw [if_neg h9, if_neg h9]
    have : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> simp only [sa, sb, s0, sig, kc, Vlo, Vhi, l1, h1, Blo, Bhi, Rlo, Rhi, q1, rr, rq]

end Led

omit scl in
theorem Wsum_eq {d : ℕ} {b b' : ℕ → ℕ → ℤ} (h : ∀ l < 5, ∀ j < d, b l j = b' l j) (s : ℕ) :
    Ledger.Wsum d b s = Ledger.Wsum d b' s :=
  sum_congr rfl fun j hj => sum_congr rfl fun l hl => sum_congr rfl fun l' hl' => by
    rw [h l (mem_range.1 hl) j (mem_range.1 hj), h l' (mem_range.1 hl') j (mem_range.1 hj)]

/-! ## Arrays and functions of the cells -/

omit scl in
theorem half_lt {D : Dim} {l : ℕ} (hl : l < D.nl) (he : isExpL l = true) : l / 2 < D.ne := by
  unfold isExpL at he
  simp only [beq_iff_eq] at he
  unfold Dim.ne
  omega

omit scl in
theorem routed_exp {D : Dim} {l x : ℕ} (hr : routed D l x = true) : isExpL l = true := by
  unfold routed at hr
  simp only [Bool.and_eq_true] at hr
  exact hr.1

section Cells
variable {D : Dim} {t t' : Cell → ℤ} (h : ∀ c : Cell, c.Valid D → t c = t' c)
include h

omit scl in
theorem val_eq (X : Arr) {a j i : ℕ} (ha : a < X.cnt D) (hj : j < X.width D) (hi : i < D.T) :
    val t X a j i = val t' X a j i := by
  unfold val
  congr 1
  exact sum_congr rfl fun k hk => by rw [h ⟨X, k, a, j, i⟩ ⟨mem_range.1 hk, ha, hj, hi⟩]

omit scl in
theorem xS_eq {s j i : ℕ} (hs : s ≤ 2 * D.nl) (hj : j < D.d) (hi : i < D.T) :
    xS D t s j i = xS D t' s j i := by
  obtain ⟨-, -, c3, c4⟩ := stream_cells D hs
  exact val_eq h _ c4 (by rw [c3]; exact hj) hi

omit scl in
theorem bS_eq {s l j i : ℕ} (hs : s ≤ 2 * D.nl) (hl : l < 5) (hj : j < D.d) (hi : i < D.T) :
    bS D t s l j i = bS D t' s l j i := by
  obtain ⟨c1, -, c3, c4⟩ := stream_cells D hs
  exact h _ ⟨by rw [c1]; exact hl, c4, by rw [c3]; exact hj, hi⟩

omit scl in
theorem led_eq {ν i : ℕ} (hν : ν < D.nNu) (hi : i < D.T) : ∀ n < 99, led t ν i n = led t' ν i n :=
  fun _ hn => val_eq h .D hν hn hi

omit scl in
/-- a sum over the channels of an array, with any coefficients -/
theorem dot_eq (X : Arr) {a n i : ℕ} (ha : a < X.cnt D) (hn : n ≤ X.width D)
    (hi : i < D.T) (c : ℕ → ℤ) :
    ∑ j ∈ range n, val t X a j i * c j = ∑ j ∈ range n, val t' X a j i * c j :=
  sum_congr rfl fun j hj => by rw [val_eq h X ha (lt_of_lt_of_le (mem_range.1 hj) hn) hi]

omit scl in
theorem hh_eq {l j i : ℕ} (hl : l < D.nl) (hj : j < D.f) (hi : i < D.T) :
    hh t l j i = hh t' l j i := by
  unfold hh
  rw [val_eq h .sl hl hj hi, val_eq h .up hl hj hi]

omit scl in
theorem mr_eq {l' i : ℕ} (hl : l' < D.ne) (hi : i < D.T) : mr D t l' i = mr D t' l' i :=
  sum_congr rfl fun e he => by
    rw [val_eq h .sel hl (mem_range.1 he) hi, val_eq h .lr hl (mem_range.1 he) hi]

variable (w : ℕ → LW ℤ)

omit scl in
theorem AY_eq {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    AY D t w l x i = AY D t' w l x i := by
  unfold AY Aq Ak
  rw [dot_eq h .a (n := D.d) hl (le_of_eq rfl) hi, dot_eq h .a (n := D.d) hl (le_of_eq rfl) hi]

omit scl in
/-- in a layer with experts: Σ_e sel_e · (a sum over the channels of xr) -/
theorem routed_eq {l i : ℕ} (hl : l < D.nl) (he : isExpL l = true) (hi : i < D.T) (c : ℕ → ℕ → ℤ) :
    ∑ e ∈ range D.nx, val t .sel (l / 2) e i * ∑ j ∈ range D.d, val t .xr (l / 2) j i * c e j =
      ∑ e ∈ range D.nx, val t' .sel (l / 2) e i * ∑ j ∈ range D.d, val t' .xr (l / 2) j i * c e j :=
  sum_congr rfl fun e hE => by
    rw [val_eq h .sel (half_lt hl he) (mem_range.1 hE) hi,
      dot_eq h .xr (n := D.d) (half_lt hl he) (le_of_eq rfl) hi]

omit scl in
theorem Ag_eq {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Ag D t w l x i = Ag D t' w l x i := by
  unfold Ag
  split_ifs with hr
  · exact routed_eq h hl (routed_exp hr) hi _
  · exact dot_eq h .m (n := D.d) hl (le_of_eq rfl) hi _

omit scl in
theorem Au_eq {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Au D t w l x i = Au D t' w l x i := by
  unfold Au
  split_ifs with hr
  · exact routed_eq h hl (routed_exp hr) hi _
  · exact dot_eq h .m (n := D.d) hl (le_of_eq rfl) hi _

omit scl in
theorem Ad_eq (hf : D.f = 2 * D.fe) {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Ad D t w l x i = Ad D t' w l x i := by
  unfold Ad
  split_ifs with he
  · congr 1
    · exact sum_congr rfl fun j hj => by rw [hh_eq h hl (by have := mem_range.1 hj; omega) hi]
    · exact sum_congr rfl fun e hE => by
        rw [val_eq h .sel (half_lt hl he) (mem_range.1 hE) hi]
        congr 1
        exact sum_congr rfl fun j hj => by rw [hh_eq h hl (by have := mem_range.1 hj; omega) hi]
  · exact sum_congr rfl fun j hj => by rw [hh_eq h hl (mem_range.1 hj) hi]

end Cells

end CastValid

open CastValid in
/-- If f = 2 fe, a key of the relation reads valid cells only. -/
theorem key_congr {D : Dim} {t t' : Cell → ℤ} (h : ∀ c : Cell, c.Valid D → t c = t' c)
    (hf : D.f = 2 * D.fe) (tb : Tables) (L0 : ℕ) (w : ℕ → LW ℤ) {s : Fam} {l x i : ℕ}
    (hl : l < D.nl) (hs : present s l = true) (hx : x < len D s) (hi : i < D.T) :
    key D t tb L0 w s l x i = key D t' tb L0 w s l x i := by
  have h2 : 2 * l ≤ 2 * D.nl := by omega
  have h3 : 2 * l + 1 ≤ 2 * D.nl := by omega
  have h4 : 2 * l + 2 ≤ 2 * D.nl := by omega
  cases s
  case G => simp only [key, gw]; rw [Ag_eq h w hl hi, val_eq h .g0 hl hx hi, val_eq h .gh hl hx hi, val_eq h .rg hl hx hi]
  case U => simp only [key]; rw [Au_eq h w hl hi, val_eq h .up hl hx hi, val_eq h .ru hl hx hi]
  case UT => simp only [key]; rw [val_eq h .up hl hx hi]
  case QK => simp only [key, Y']; rw [AY_eq h w hl hi, AY_eq h w hl hi, AY_eq h w hl hi, val_eq h .qkw hl hx hi, val_eq h .rqk hl hx hi]
  case N1 => simp only [key]; rw [xS_eq h h2 hx hi, R_eq (led_eq h (show 2 * l < 2 * D.nl by omega) hi), val_eq h .aw hl hx hi, val_eq h .ra hl hx hi]
  case N2 => simp only [key]; rw [xS_eq h h3 hx hi, R_eq (led_eq h (show 2 * l + 1 < 2 * D.nl by omega) hi), val_eq h .mw hl hx hi, val_eq h .rm hl hx hi]
  case O => simp only [key]; rw [dot_eq h .o (n := D.dq) hl (le_of_eq rfl) hi, xS_eq h h3 hx hi, xS_eq h h2 hx hi, val_eq h .ro hl hx hi]
  case D => simp only [key]; rw [Ad_eq h w hf hl hi, xS_eq h h4 hx hi, xS_eq h h3 hx hi, val_eq h .rd hl hx hi]
  case V => simp only [key, Av]; rw [dot_eq h .a (n := D.d) hl (le_of_eq rfl) hi, val_eq h .vw hl hx hi, val_eq h .rv hl hx hi]
  case LR => simp only [key, lw]; rw [dot_eq h .m (n := D.d) hl (le_of_eq rfl) hi, val_eq h .ly (half_lt hl hs) hx hi, val_eq h .l3 (half_lt hl hs) hx hi, val_eq h .rl (half_lt hl hs) hx hi]
  case XR => simp only [key]; rw [val_eq h .sc (half_lt hl hs) Nat.one_pos hi, val_eq h .m hl hx hi, val_eq h .xr (half_lt hl hs) hx hi]
  case LT => simp only [key]; rw [val_eq h .lr (half_lt hl hs) hx hi]
  case DD =>
    simp only [key]
    rw [mr_eq h (half_lt hl hs) hi, val_eq h .lr (half_lt hl hs) hx hi]
    congr 1
    exact sum_congr rfl fun e he =>
      val_eq h .sel (half_lt hl hs) (mem_range.1 (mem_filter.1 he).1) hi
  case GH => simp only [key]; rw [val_eq h .rg hl hx hi]
  case UH => simp only [key]; rw [val_eq h .ru hl hx hi]
  case OH => simp only [key]; rw [val_eq h .ro hl hx hi]
  case DH => simp only [key]; rw [val_eq h .rd hl hx hi]
  case VH => simp only [key]; rw [val_eq h .rv hl hx hi]
  case LH => simp only [key]; rw [val_eq h .rl (half_lt hl hs) hx hi]
  case QKH => simp only [key]; rw [val_eq h .rqk hl hx hi]
  case N1H => simp only [key]; rw [val_eq h .ra hl hx hi]
  case N2H => simp only [key]; rw [val_eq h .rm hl hx hi]
  case ROW =>
    have hx' : x < 2 * 99 := hx
    simp only [key]
    rw [led_eq h (show 2 * l + x / nLedger < 2 * D.nl by show 2 * l + x / 99 < _; omega) hi
        (x % nLedger) (Nat.mod_lt _ (by decide))]
  case SEL => simp only [key]; rw [val_eq h .sel (half_lt hl hs) hx hi]
  case L3 => simp only [key]; rw [val_eq h .l3 (half_lt hl hs) hx hi]
  case G0 => simp only [key]; rw [val_eq h .g0 hl hx hi]
  case CN1 => simp only [key]; rw [val_eq h .aw hl hx hi, val_eq h .a hl hx hi]
  case CN2 => simp only [key]; rw [val_eq h .mw hl hx hi, val_eq h .m hl hx hi]
  case CQK =>
    have hx' : x < D.dq + D.dkv := hx
    simp only [key]
    rw [val_eq h .qkw hl hx hi]
    split_ifs with hq
    · rw [val_eq h .q hl hq hi]
    · rw [val_eq h .kx hl (show x - D.dq < D.dkv by omega) hi]
  case CV => simp only [key]; rw [val_eq h .vw hl hx hi, val_eq h .v hl hx hi]
  case CLR => simp only [key]; rw [val_eq h .ly (half_lt hl hs) hx hi, val_eq h .lr (half_lt hl hs) hx hi, val_eq h .l3 (half_lt hl hs) hx hi]
  case F =>
    simp only [key]; rw [val_eq h .g0 hl hx hi, val_eq h .gc hl hx hi, val_eq h .sl hl hx hi]
  case MR =>
    simp only [key]; rw [mr_eq h (half_lt hl hs) hi, val_eq h .sc (half_lt hl hs) Nat.one_pos hi]
  case CG => simp only [key]; rw [val_eq h .gh hl hx hi, val_eq h .gc hl hx hi]

open CastValid in
/-- An identity of the relation reads valid cells only. -/
theorem idn_congr {D : Dim} {t t' : Cell → ℤ} (h : ∀ c : Cell, c.Valid D → t c = t' c)
    (first : Bool) (emb : Mat) (tok : ℕ → ℕ) {j : Idn} (hj : j.Valid D first) :
    idnVal D t emb tok j = idnVal D t' emb tok j := by
  cases j with
  | jn k ν i =>
    obtain ⟨hk, hν, hi⟩ := hj
    have hν' : ν ≤ 2 * D.nl := le_of_lt hν
    exact idn_eq (led_eq h hν hi) _ (Wsum_eq fun l hl j hj' => bS_eq h hν' hl hj' hi) hk
  | j10 l' i =>
    obtain ⟨hl, hi⟩ := hj
    show ∑ e ∈ range D.nx, val t .sel l' e i - 1 = ∑ e ∈ range D.nx, val t' .sel l' e i - 1
    congr 1
    exact sum_congr rfl fun e he => val_eq h .sel hl (mem_range.1 he) hi
  | j11 j i =>
    obtain ⟨-, hj', hi⟩ := hj
    show xS D t 0 j i - emb (tok i) j = xS D t' 0 j i - emb (tok i) j
    rw [xS_eq h (Nat.zero_le _) hj' hi]

/-- If f = 2 fe, the relation reads valid cells only: two traces that agree on the valid names are
in the relation together. -/
theorem rfraw_congr {D : Dim} (hf : D.f = 2 * D.fe) {tb : Tables} {L0 : ℕ} {first : Bool} {F : Type}
    [CommRing F] {w : ℕ → LayerW} {emb : Mat} {tok : ℕ → ℕ} {t t' : Cell → ℤ}
    (h : ∀ c : Cell, c.Valid D → t c = t' c) (hR : RFraw D tb L0 first F w emb tok t) :
    RFraw D tb L0 first F w emb tok t' := by
  obtain ⟨h1, h2, h3⟩ := hR
  refine ⟨fun c hc => by rw [← h c hc]; exact h1 c hc, fun q => ?_, fun j hj => ?_⟩
  · have := h2 q
    rw [key_cast] at this ⊢
    rwa [← key_congr h hf tb L0 _ q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2]
  · have := h3 j hj
    rw [idn_cast] at this ⊢
    rwa [← idn_congr h first emb tok hj]

end Inst.Model.FFSeg
