-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysValid.lean: the library's keys read cells with valid names alone, over any
field.

In the library a trace of a feed-forward segment is a function t on all names of cells (Cell in
Inst/Model/FF/Index.lean); a name is valid if its cell number, instance, channel and position lie
within its array (Cell.Valid). This file shows that a key, its three parts, the key vector of a
call and the sums made from them read t at valid names alone: two traces that agree on the valid
names give the same values. The library has this for the keys over the integers (key_congr in
Inst/Model/FF/CastValid.lean); here it is said over a field K, by the same proof, and carried on to
the parts lin, term and mat (Inst/Model/FF/Objects.lean), to keyVec, and to the sums of
Johnson/Road/FormsKeysFree.lean.

What is compared with what. All but the last section: the library with itself, at two traces. The
last section joins this with cells_addr (Johnson/Road/FormsKeysAddr.lean): the library's key vector
on the cells that are read in the entries M of the verifier's matrices by the verifier's rule,
against the library's key vector on the entries of M at the library's own addresses.

Main theorems.
 - key_agree, term_agree, mat_agree, lin_agree: at a layer of the segment where the family is
   present, an entry of the family and a position.
 - keyVec_agree: at an index below 2^(a_c); ext_keyVec_agree: its extension, at every point.
 - LINEP_agree, KEYP_agree, TERMP_agree, ACCP_agree, TSP_agree, KFP_agree.
 - keyVec_addr, ext_keyVec_addr.

The bounds. Beyond them the statements are not claimed: a key at a layer from nl on, at an entry
from the family's length on, or at a position from T on may read names that are not valid, and so
may the key vector at an index from 2^(a_c) on.

The hypotheses, and that they can be met.
 - D.f = 2 D.fe: the routed half of the gated products has the channels fe to 2 fe - 1 of arrays of
   width f. It is the field f of the library's Dim.OK (ref_ok); for sizes that agree with the shape
   of a layout that the verifier returns it is f_two_fe.
 - The two traces agree on the valid names: met by t' := t, and, in the last section, by
   cells_addr.
 - The last section: layout returns; the switches; the two records of sizes (Sized, Sized2);
   profile 4, where the array o is among the cells. Sized and Sized2 are met together by dimA h
   under three equations on the shape (sized_dimA in Johnson/Road/FormsKeysAddr.lean). All of them
   together: by runs alone, see that file.

What is not claimed. Nothing is said of the identities of the ledger, which the library treats
beside the keys. That the entries of M are what a prover has committed to is not looked at. The
program does not import this file.
-/
import Johnson.Road.FormsKeysAddr
import Johnson.Road.FormsKeysFree
import Inst.Model.FF.CastValid
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay Shape layout)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin term mat key_eq keyVec len call present isExpL
  routed famAt famsIn lJ aC val xS led hh mr gw lw AY Aq Ak Av Ag Au Ad Y' nLedger stream_cells)
open Inst.Model.FFSeg.CastValid (half_lt routed_exp)

variable {K : Type} [Field K]

/-! ## The ledger's reciprocal reads bytes below 99 -/

/-- A number of n bytes from byte a on. -/
theorem b256_agree {D₁ D₂ : ℕ → K} (e : ∀ n < 99, D₁ n = D₂ n) {a n : ℕ} (h : a + n ≤ 99) :
    Inst.Model.Ledger.b256 D₁ a n = Inst.Model.Ledger.b256 D₂ a n :=
  sum_congr rfl fun l hl => by rw [e (a + l) (by have := mem_range.1 hl; omega)]

/-- The reciprocal. -/
theorem R_agree {D₁ D₂ : ℕ → K} (e : ∀ n < 99, D₁ n = D₂ n) :
    Inst.Model.Ledger.R D₁ = Inst.Model.Ledger.R D₂ := by
  unfold Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
  rw [b256_agree e (by norm_num), b256_agree e (by norm_num)]

/-! ## Arrays and functions of the cells -/

section Cells

variable {D : Dim} {t t' : Cell → K} (h : ∀ c : Cell, c.Valid D → t c = t' c)

include h

/-- The value of an array at an instance, a channel and a position that it has. -/
theorem val_agree (X : Arr) {a j i : ℕ} (ha : a < X.cnt D) (hj : j < X.width D) (hi : i < D.T) :
    val t X a j i = val t' X a j i := by
  unfold Inst.Model.FFSeg.val
  congr 1
  exact sum_congr rfl fun k hk => by rw [h ⟨X, k, a, j, i⟩ ⟨mem_range.1 hk, ha, hj, hi⟩]

/-- The stream. -/
theorem xS_agree {s j i : ℕ} (hs : s ≤ 2 * D.nl) (hj : j < D.d) (hi : i < D.T) :
    xS D t s j i = xS D t' s j i := by
  obtain ⟨-, -, c3, c4⟩ := stream_cells D hs
  exact val_agree h _ c4 (by rw [c3]; exact hj) hi

/-- The ledger of a norm. -/
theorem led_agree {ν i : ℕ} (hν : ν < D.nNu) (hi : i < D.T) :
    ∀ n < 99, led t ν i n = led t' ν i n :=
  fun _ hn => val_agree h .D hν hn hi

/-- A sum over the channels of an array, with any coefficients. -/
theorem dot_agree (X : Arr) {a n i : ℕ} (ha : a < X.cnt D) (hn : n ≤ X.width D) (hi : i < D.T)
    (c : ℕ → K) :
    ∑ j ∈ range n, val t X a j i * c j = ∑ j ∈ range n, val t' X a j i * c j :=
  sum_congr rfl fun j hj => by rw [val_agree h X ha (lt_of_lt_of_le (mem_range.1 hj) hn) hi]

/-- A gated product. -/
theorem hh_agree {l j i : ℕ} (hl : l < D.nl) (hj : j < D.f) (hi : i < D.T) :
    hh t l j i = hh t' l j i := by
  unfold hh
  rw [val_agree h .sl hl hj hi, val_agree h .up hl hj hi]

/-- The selected logit. -/
theorem mr_agree {l' i : ℕ} (hl : l' < D.ne) (hi : i < D.T) : mr D t l' i = mr D t' l' i :=
  sum_congr rfl fun e he => by
    rw [val_agree h .sel hl (mem_range.1 he) hi, val_agree h .lr hl (mem_range.1 he) hi]

variable (w : ℕ → LW K)

/-- The products with the matrices of queries and keys, at any column. -/
theorem AY_agree {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    AY D t w l x i = AY D t' w l x i := by
  unfold AY Aq Ak
  rw [dot_agree h .a (n := D.d) hl (le_of_eq rfl) hi,
    dot_agree h .a (n := D.d) hl (le_of_eq rfl) hi]

/-- The selector's entries times sums over the channels of xr. -/
theorem routed_agree {l i : ℕ} (hl : l < D.nl) (he : isExpL l = true) (hi : i < D.T)
    (c : ℕ → ℕ → K) :
    ∑ e ∈ range D.nx, val t .sel (l / 2) e i * ∑ j ∈ range D.d, val t .xr (l / 2) j i * c e j =
      ∑ e ∈ range D.nx, val t' .sel (l / 2) e i *
        ∑ j ∈ range D.d, val t' .xr (l / 2) j i * c e j :=
  sum_congr rfl fun e hE => by
    rw [val_agree h .sel (half_lt hl he) (mem_range.1 hE) hi,
      dot_agree h .xr (n := D.d) (half_lt hl he) (le_of_eq rfl) hi]

/-- The gate's product, at any hidden unit. -/
theorem Ag_agree {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Ag D t w l x i = Ag D t' w l x i := by
  unfold Ag
  split_ifs with hr
  · exact routed_agree h hl (routed_exp hr) hi _
  · exact dot_agree h .m (n := D.d) hl (le_of_eq rfl) hi _

/-- The up projection's product. -/
theorem Au_agree {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Au D t w l x i = Au D t' w l x i := by
  unfold Au
  split_ifs with hr
  · exact routed_agree h hl (routed_exp hr) hi _
  · exact dot_agree h .m (n := D.d) hl (le_of_eq rfl) hi _

/-- The routed part of the down product. -/
theorem downR_agree (hf : D.f = 2 * D.fe) {l i : ℕ} (hl : l < D.nl) (he : isExpL l = true)
    (hi : i < D.T) (x : ℕ) :
    ∑ e ∈ range D.nx, val t .sel (l / 2) e i *
        ∑ j ∈ range D.fe, hh t l (D.fe + j) i * (w l).Ed e j x =
      ∑ e ∈ range D.nx, val t' .sel (l / 2) e i *
        ∑ j ∈ range D.fe, hh t' l (D.fe + j) i * (w l).Ed e j x :=
  sum_congr rfl fun e hE => by
    rw [val_agree h .sel (half_lt hl he) (mem_range.1 hE) hi]
    congr 1
    exact sum_congr rfl fun j hj => by
      rw [hh_agree h hl (by have := mem_range.1 hj; omega) hi]

/-- The part of the down product that is not routed, over n hidden units. -/
theorem downS_agree {n : ℕ} (hn : n ≤ D.f) {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    ∑ j ∈ range n, hh t l j i * (w l).Wd j x = ∑ j ∈ range n, hh t' l j i * (w l).Wd j x :=
  sum_congr rfl fun j hj => by
    rw [hh_agree h hl (lt_of_lt_of_le (mem_range.1 hj) hn) hi]

/-- The down product. -/
theorem Ad_agree (hf : D.f = 2 * D.fe) {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) (x : ℕ) :
    Ad D t w l x i = Ad D t' w l x i := by
  unfold Ad
  split_ifs with he
  · rw [downS_agree h w (by omega) hl hi, downR_agree h w hf hl he hi]
  · exact downS_agree h w (Nat.le_refl _) hl hi x

end Cells

/-! ## The keys and their three parts -/

section Keys

variable [scl : Scl] {D : Dim} {t t' : Cell → K} (h : ∀ c : Cell, c.Valid D → t c = t' c)
  (hf : D.f = 2 * D.fe) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) {s : Fam} {l x i : ℕ}
  (hl : l < D.nl) (hs : present s l = true) (hx : x < len D s) (hi : i < D.T)

include h hf hl hs hx hi

/-- A key of a family at a layer where the family is present, at an entry of the family and a
position: it reads cells with valid names alone. The library has this over the integers
(key_congr in Inst/Model/FF/CastValid.lean); the proof is that one. -/
theorem key_agree : key D t tb L0 w s l x i = key D t' tb L0 w s l x i := by
  have h2 : 2 * l ≤ 2 * D.nl := by omega
  have h3 : 2 * l + 1 ≤ 2 * D.nl := by omega
  have h4 : 2 * l + 2 ≤ 2 * D.nl := by omega
  cases s
  case G =>
    simp only [key, gw]
    rw [Ag_agree h w hl hi, val_agree h .g0 hl hx hi, val_agree h .gh hl hx hi,
      val_agree h .rg hl hx hi]
  case U =>
    simp only [key]
    rw [Au_agree h w hl hi, val_agree h .up hl hx hi, val_agree h .ru hl hx hi]
  case UT => simp only [key]; rw [val_agree h .up hl hx hi]
  case QK =>
    simp only [key, Y']
    rw [AY_agree h w hl hi, AY_agree h w hl hi, AY_agree h w hl hi, val_agree h .qkw hl hx hi,
      val_agree h .rqk hl hx hi]
  case N1 =>
    simp only [key]
    rw [xS_agree h h2 hx hi, R_agree (led_agree h (show 2 * l < 2 * D.nl by omega) hi),
      val_agree h .aw hl hx hi, val_agree h .ra hl hx hi]
  case N2 =>
    simp only [key]
    rw [xS_agree h h3 hx hi, R_agree (led_agree h (show 2 * l + 1 < 2 * D.nl by omega) hi),
      val_agree h .mw hl hx hi, val_agree h .rm hl hx hi]
  case O =>
    simp only [key]
    rw [dot_agree h .o (n := D.dq) hl (le_of_eq rfl) hi, xS_agree h h3 hx hi,
      xS_agree h h2 hx hi, val_agree h .ro hl hx hi]
  case D =>
    simp only [key]
    rw [Ad_agree h w hf hl hi, xS_agree h h4 hx hi, xS_agree h h3 hx hi,
      val_agree h .rd hl hx hi]
  case V =>
    simp only [key, Av]
    rw [dot_agree h .a (n := D.d) hl (le_of_eq rfl) hi, val_agree h .vw hl hx hi,
      val_agree h .rv hl hx hi]
  case LR =>
    simp only [key, lw]
    rw [dot_agree h .m (n := D.d) hl (le_of_eq rfl) hi, val_agree h .ly (half_lt hl hs) hx hi,
      val_agree h .l3 (half_lt hl hs) hx hi, val_agree h .rl (half_lt hl hs) hx hi]
  case XR =>
    simp only [key]
    rw [val_agree h .sc (half_lt hl hs) Nat.one_pos hi, val_agree h .m hl hx hi,
      val_agree h .xr (half_lt hl hs) hx hi]
  case LT => simp only [key]; rw [val_agree h .lr (half_lt hl hs) hx hi]
  case DD =>
    simp only [key]
    rw [mr_agree h (half_lt hl hs) hi, val_agree h .lr (half_lt hl hs) hx hi]
    congr 1
    exact sum_congr rfl fun e he =>
      val_agree h .sel (half_lt hl hs) (mem_range.1 (mem_filter.1 he).1) hi
  case GH => simp only [key]; rw [val_agree h .rg hl hx hi]
  case UH => simp only [key]; rw [val_agree h .ru hl hx hi]
  case OH => simp only [key]; rw [val_agree h .ro hl hx hi]
  case DH => simp only [key]; rw [val_agree h .rd hl hx hi]
  case VH => simp only [key]; rw [val_agree h .rv hl hx hi]
  case LH => simp only [key]; rw [val_agree h .rl (half_lt hl hs) hx hi]
  case QKH => simp only [key]; rw [val_agree h .rqk hl hx hi]
  case N1H => simp only [key]; rw [val_agree h .ra hl hx hi]
  case N2H => simp only [key]; rw [val_agree h .rm hl hx hi]
  case ROW =>
    have hx' : x < 2 * 99 := hx
    simp only [key]
    rw [led_agree h (show 2 * l + x / nLedger < 2 * D.nl by show 2 * l + x / 99 < _; omega) hi
        (x % nLedger) (Nat.mod_lt _ (by decide))]
  case SEL => simp only [key]; rw [val_agree h .sel (half_lt hl hs) hx hi]
  case L3 => simp only [key]; rw [val_agree h .l3 (half_lt hl hs) hx hi]
  case G0 => simp only [key]; rw [val_agree h .g0 hl hx hi]
  case CN1 => simp only [key]; rw [val_agree h .aw hl hx hi, val_agree h .a hl hx hi]
  case CN2 => simp only [key]; rw [val_agree h .mw hl hx hi, val_agree h .m hl hx hi]
  case CQK =>
    have hx' : x < D.dq + D.dkv := hx
    simp only [key]
    rw [val_agree h .qkw hl hx hi]
    split_ifs with hq
    · rw [val_agree h .q hl hq hi]
    · rw [val_agree h .kx hl (show x - D.dq < D.dkv by omega) hi]
  case CV => simp only [key]; rw [val_agree h .vw hl hx hi, val_agree h .v hl hx hi]
  case CLR =>
    simp only [key]
    rw [val_agree h .ly (half_lt hl hs) hx hi, val_agree h .lr (half_lt hl hs) hx hi,
      val_agree h .l3 (half_lt hl hs) hx hi]
  case F =>
    simp only [key]
    rw [val_agree h .g0 hl hx hi, val_agree h .gc hl hx hi, val_agree h .sl hl hx hi]
  case MR =>
    simp only [key]
    rw [mr_agree h (half_lt hl hs) hi, val_agree h .sc (half_lt hl hs) Nat.one_pos hi]
  case CG => simp only [key]; rw [val_agree h .gh hl hx hi, val_agree h .gc hl hx hi]

/-- The part of a key that is a sum of products of two values at the position. -/
theorem term_agree : term D t tb L0 w s l x i = term D t' tb L0 w s l x i := by
  have h2 : 2 * l ≤ 2 * D.nl := by omega
  have h3 : 2 * l + 1 ≤ 2 * D.nl := by omega
  cases s
  case N1 =>
    simp only [term]
    rw [xS_agree h h2 hx hi, R_agree (led_agree h (show 2 * l < 2 * D.nl by omega) hi)]
  case N2 =>
    simp only [term]
    rw [xS_agree h h3 hx hi, R_agree (led_agree h (show 2 * l + 1 < 2 * D.nl by omega) hi)]
  case QK =>
    simp only [term, Y']
    rw [AY_agree h w hl hi, AY_agree h w hl hi, AY_agree h w hl hi]
  case XR =>
    simp only [term]
    rw [val_agree h .sc (half_lt hl hs) Nat.one_pos hi, val_agree h .m hl hx hi]
  case DD => simp only [term]; rw [mr_agree h (half_lt hl hs) hi]
  case MR => simp only [term]; rw [mr_agree h (half_lt hl hs) hi]
  case G => simp only [term]; rw [Ag_agree h w hl hi]
  case U => simp only [term]; rw [Au_agree h w hl hi]
  case D =>
    simp only [term]
    split_ifs with he
    · rw [downR_agree h w hf hl he hi]
    · rfl
  all_goals rfl

omit hs hx in
/-- The part of a key that is a matrix product. It reads whole rows of arrays, whatever the
entry. -/
theorem mat_agree : mat D t w s l x i = mat D t' w s l x i := by
  cases s
  case G => simp only [mat]; rw [Ag_agree h w hl hi]
  case U => simp only [mat]; rw [Au_agree h w hl hi]
  case V => simp only [mat, Av]; rw [dot_agree h .a (n := D.d) hl (le_of_eq rfl) hi]
  case O => simp only [mat]; rw [dot_agree h .o (n := D.dq) hl (le_of_eq rfl) hi]
  case LR => simp only [mat]; rw [dot_agree h .m (n := D.d) hl (le_of_eq rfl) hi]
  case D =>
    simp only [mat]
    rw [downS_agree h w (by split_ifs <;> omega) hl hi]
  all_goals rfl

/-- The affine part of a key: what is left of the key. -/
theorem lin_agree : lin D t tb L0 w s l x i = lin D t' tb L0 w s l x i := by
  have e1 := key_eq D t tb L0 w s l x i
  have e2 := key_eq D t' tb L0 w s l x i
  rw [key_agree h hf tb L0 w hl hs hx hi, term_agree h hf tb L0 w hl hs hx hi,
    mat_agree h hf w hl hi] at e1
  linear_combination e2 - e1

end Keys

/-! ## The key vector -/

section Vec

variable [scl : Scl] {D : Dim} {t t' : Cell → K} (h : ∀ c : Cell, c.Valid D → t c = t' c)
  (hf : D.f = 2 * D.fe) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

include h hf

/-- The key vector of a call, at an index below 2^(a_c), reads cells with valid names alone. -/
theorem keyVec_agree (c : Fin 8) {X : ℕ} (hX : X < 2 ^ aC D c) :
    keyVec D t tb L0 w c X = keyVec D t' tb L0 w c X := by
  have hT : 0 < D.T := Nat.two_pow_pos _
  have hi : X % D.T < D.T := Nat.mod_lt _ hT
  have hl : X / D.T / 2 ^ lJ D c < D.nl := by
    have e : 2 ^ aC D c = D.nl * 2 ^ lJ D c * D.T := by
      show 2 ^ (D.lL + lJ D c + D.lT) = 2 ^ D.lL * 2 ^ lJ D c * 2 ^ D.lT
      rw [pow_add, pow_add]
    rw [e] at hX
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hT (Nat.two_pow_pos _))]
    calc X < D.nl * 2 ^ lJ D c * D.T := hX
      _ = D.nl * (D.T * 2 ^ lJ D c) := by ring
  unfold keyVec
  cases hfa : famAt D c (X / D.T % 2 ^ lJ D c) with
  | none => rfl
  | some sx =>
    obtain ⟨s, x⟩ := sx
    obtain ⟨-, hx, -⟩ := (Inst.Model.FFSeg.IndexFacts.famAtPos D c _ s x).mp hfa
    show (if present s (X / D.T / 2 ^ lJ D c) then _ else _) =
      if present s (X / D.T / 2 ^ lJ D c) then _ else _
    split_ifs with hs
    · exact key_agree h hf tb L0 w hl hs hx hi
    · rfl

/-- So does its extension, at every point. -/
theorem ext_keyVec_agree (c : Fin 8) (ζ : ℕ → K) :
    Blocks.ext (aC D c) (keyVec D t tb L0 w c) ζ = Blocks.ext (aC D c) (keyVec D t' tb L0 w c) ζ :=
  Blocks.ext_congr (fun _ hX => keyVec_agree h hf tb L0 w c hX) ζ

end Vec

/-! ## The sums of Johnson/Road/FormsKeysFree.lean -/

section Sums

variable [scl : Scl] {D : Dim} {t t' : Cell → K} (h : ∀ c : Cell, c.Valid D → t c = t' c)
  (hf : D.f = 2 * D.fe) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (ζ : ℕ → K)

include h hf

/-- The affine parts of a family's keys at a layer. -/
theorem LINEP_agree {s : Fam} {l : ℕ} (hl : l < D.nl) (hs : present s l = true) :
    LINEP D t tb L0 w ζ s l = LINEP D t' tb L0 w ζ s l := by
  unfold LINEP
  refine sum_congr rfl fun x hx => ?_
  rw [Blocks.ext_congr (fun i hi => lin_agree h hf tb L0 w hl hs (mem_range.1 hx) hi)]

/-- The whole keys. -/
theorem KEYP_agree {s : Fam} {l : ℕ} (hl : l < D.nl) (hs : present s l = true) :
    KEYP D t tb L0 w ζ s l = KEYP D t' tb L0 w ζ s l := by
  unfold KEYP
  refine sum_congr rfl fun x hx => ?_
  rw [Blocks.ext_congr (fun i hi => key_agree h hf tb L0 w hl hs (mem_range.1 hx) hi)]

/-- The products, at one position. -/
theorem TERMP_agree {s : Fam} {l i : ℕ} (hl : l < D.nl) (hs : present s l = true)
    (hi : i < D.T) : TERMP D t tb L0 w ζ s l i = TERMP D t' tb L0 w ζ s l i := by
  unfold TERMP
  exact sum_congr rfl fun x hx => by rw [term_agree h hf tb L0 w hl hs (mem_range.1 hx) hi]

/-- The matrix products. -/
theorem ACCP_agree (s : Fam) {l : ℕ} (hl : l < D.nl) :
    ACCP D t w ζ s l = ACCP D t' w ζ s l := by
  unfold ACCP
  refine sum_congr rfl fun x _ => ?_
  rw [Blocks.ext_congr (fun i hi => mat_agree h hf w (s := s) (x := x) hl hi)]

/-- What the sumcheck over the positions is to show for a call. -/
theorem TSP_agree (c : Fin 8) : TSP D t tb L0 w c ζ = TSP D t' tb L0 w c ζ := by
  unfold TSP
  refine Blocks.ext_congr (fun i hi => sum_congr rfl fun l hl => ?_) _
  congr 1
  exact congrArg List.sum (List.map_congr_left fun s hs =>
    TERMP_agree h hf tb L0 w ζ (mem_range.1 hl) (List.mem_filter.mp hs).2 hi)

/-- The library's KF of a call, at a free point. -/
theorem KFP_agree (c : Fin 8) : KFP D t tb L0 w c ζ = KFP D t' tb L0 w c ζ := by
  unfold KFP
  rw [TSP_agree h hf tb L0 w ζ c]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  congr 1
  refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
  rw [LINEP_agree h hf tb L0 w ζ (mem_range.1 hl) (List.mem_filter.mp hs).2,
    ACCP_agree h hf w ζ s (mem_range.1 hl)]

end Sums

/-! ## The cells that are read in the verifier's matrices, and the library's addresses -/

section Addr

variable [scl : Scl] {h : Shape} {pc : List (List String)} {y : Lay}
  (hy : layout h pc = .ok y) (S : Switches h) (h4 : h.p4 = true) {D : Dim} (Z : Sized h D)
  (Z2 : Sized2 h D) (M : Mats K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

include hy S h4 Z Z2

omit scl h4 Z2 in
/-- A layer has twice the hidden units of an expert, in the library's sizes too. -/
theorem f_two_fe : D.f = 2 * D.fe := by
  have A := admitted_of_layout hy S.p3
  show D.P.f = 2 * D.P.fe
  rw [Z.f, Z.fe, ← A.shape]
  exact A.laid.ffe

/-- The library's key vector on the cells that are read in the entries M of the verifier's matrices
by the verifier's rule is the key vector on the entries of M at the library's own addresses. At
profile 4, where the array o is among the cells. -/
theorem keyVec_addr (c : Fin 8) {X : ℕ} (hX : X < 2 ^ aC D c) :
    keyVec D (cellsOf D (cellsAt y M)) tb L0 w c X =
      keyVec D (fun q => atAddr y D M (Inst.Model.FFSeg.addr D q)) tb L0 w c X :=
  keyVec_agree (fun q hv => cells_addr_of_layout hy S Z Z2 M q hv fun _ => h4)
    (f_two_fe hy S Z) tb L0 w c hX

/-- The same for its extension, at every point. -/
theorem ext_keyVec_addr (c : Fin 8) (ζ : ℕ → K) :
    Blocks.ext (aC D c) (keyVec D (cellsOf D (cellsAt y M)) tb L0 w c) ζ =
      Blocks.ext (aC D c)
        (keyVec D (fun q => atAddr y D M (Inst.Model.FFSeg.addr D q)) tb L0 w c) ζ :=
  Blocks.ext_congr (fun _ hX => keyVec_addr hy S h4 Z Z2 M tb L0 w c hX) ζ

end Addr

#print axioms key_agree
#print axioms term_agree
#print axioms mat_agree
#print axioms lin_agree
#print axioms keyVec_agree
#print axioms KFP_agree
#print axioms keyVec_addr
#print axioms ext_keyVec_addr

end OnBytes.Road
