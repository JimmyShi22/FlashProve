-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/HonestKeys.lean: the honest trace (`hon`, Inst/Model/FF/Trace.lean) of a
  feed-forward segment, part 2: under `Par` and `Runs`, every looked-up value (key) of the relation
  (`KeyName`) is an entry of its table, over the integers, and the identities hold.

    Part 1  `Par`: the conditions on the sizes, the first layer L0, the shifts and the two
            normalisations' numbers; the range conditions of the integer program
            (Inst/Model/Program.lean)
    Part 2  the arrays of the router in a layer with experts
    Part 3  the 34 families (`key_hon`)
    Part 4  the identities (`idn_hon`)

  The identities (`Idn`, `idnVal`, Inst/Model/FF/Trace.lean): (J1) to (J9), those of the ledger of a
  normalisation; (J10), the router's selection bits add up to 1; (J11), in the first segment the
  stream at the index 0 is the embedding of the prompt, which `idn_hon` assumes of x. The sizes D
  are not fixed: `key_hon` and `idn_hon` hold for all sizes and shifts that meet `Par`, and for
  every run of the segment's steps (`Runs`, Inst/Model/FF/Trace.lean). `Par` allows all shifts of
  the matrix products up to 24 (QK: 32): for the honest trace no lower limit is needed.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: G, U, UT, ..: the families of keys (`Fam`); `present s l`: the family is present in
  layer ℓ (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table functions that the program
  reads; `w l`: a `LayerW`: the weight matrices of one layer; `rhu a k`: ⌊(a + 2^(k−1)) / 2^k⌋,
  k ≥ 1 (Inst/Model/Program.lean); `x`, `o`: ℕ → ℕ → `Vec`: in `hv`: x s is state s of the stream in
  the segment, o ℓ the output of attention in layer ℓ; WR: `fun l => LW.ofInt ℤ (w l)`: integer
  weights, mapped into ℤ; `npOf D ν`: the parameters of the norm instance ν = 2ℓ + n; `led t ν i`:
  the bytes of the ledger of the norm instance ν at position i, as values; `Runs ..`: the steps of
  the segment lead from state to state of the stream, and none of their range conditions fails, with
  the bounds of its fields `o`, `wr` (Inst/Model/FF/Trace.lean); `cellW n a l`: cell l of the value
  a in an array of n cells (the widened cell rule) (Inst/Model/Widened.lean); `site`, `high` (for
  every shift: `ssite`, `shigh`): the low and the high key of a rounding; `hd A k`: ⌊rem(A, k) /
  2^16⌋, the high digit (Inst/Model/Common/Site.lean); `R8`, `R16`: the tables ι, for ι < 2^8, and
  ι, for ι < 2^16 (Inst/Model/Tables.lean); `InLutZ L key`: the key is an entry of the table
  (Inst/Model/Common/TableKeys.lean).
-/
import Inst.Model.FF.HonestBase
import Inst.Model.Common.Unit
import Inst.Model.Common.TableKeys

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg.Hon

variable [scl : Scl]

open Finset
open Inst.Model.TableKeys (InLutZ inLutZ_r8 inLutZ_r16 fc_hon)
open Inst.Model.Site (site high ssite shigh hd site_hon high_hon ssite_hon shigh_hon)

/-! ## Part 1. Sizes, shifts, range conditions -/

/-- The conditions on the sizes and the shifts: L0 is even (`even`: `isExpL_iff`,
Inst/Model/FF/HonestBase.lean, asks it); there is at least one expert (`nx`); D.T ≤ D.P.T (`T`); f =
2 fe (`f`: a layer with experts has as many hidden units as a dense one); d ≤ 2^16 (`d`:
`Ledger.HonHyp`, Inst/Model/Common/LedgerHonest.lean, asks it); in every layer, each of the ten
shifts of a layer (`Params`, Inst/Model/Program.lean) is at most the `top` of its high key in `key`
(Inst/Model/FF/Trace.lean): 32 for kq, kk (queries and keys), 24 for the others (kv: VH; ko: OH; kd:
DH; kr: LH; kg, kg': GH; ku, ku': UH), and both normalisations meet `NormPar.OK` (`n1`, `n2`). -/
structure Par (D : Dim) (L0 : ℕ) : Prop where
  even : L0 % 2 = 0
  nx : 0 < D.nx
  T : D.T ≤ D.P.T
  f : D.f = 2 * D.fe
  d : D.d ≤ 2 ^ 16
  kq : ∀ l, (D.Pl l).kq ≤ 32
  kk : ∀ l, (D.Pl l).kk ≤ 32
  kv : ∀ l, (D.Pl l).kv ≤ 24
  ko : ∀ l, (D.Pl l).ko ≤ 24
  kd : ∀ l, (D.Pl l).kd ≤ 24
  kr : ∀ l, (D.Pl l).kr ≤ 24
  kg : ∀ l, (D.Pl l).kg ≤ 24
  ku : ∀ l, (D.Pl l).ku ≤ 24
  kg' : ∀ l, (D.Pl l).kg' ≤ 24
  ku' : ∀ l, (D.Pl l).ku' ≤ 24
  n1 : ∀ l, (D.Pl l).n1.OK
  n2 : ∀ l, (D.Pl l).n2.OK

variable {D : Dim} {tb : Tables} {w : ℕ → LayerW} {L0 : ℕ} {x o : ℕ → ℕ → Vec}

local notation "H" => hon D tb w L0 x o
local notation "HV" => hv D tb w L0 x o
local notation "WR" => fun l => LW.ofInt ℤ (w l)

theorem Par.kG (hp : Par D L0) (l L y : ℕ) : FF.kG (D.Pl l) L y ≤ 24 := by
  unfold FF.kG
  split_ifs
  · exact (hp.kg' _)
  · exact (hp.kg _)

theorem Par.kU (hp : Par D L0) (l L y : ℕ) : FF.kU (D.Pl l) L y ≤ 24 := by
  unfold FF.kU
  split_ifs
  · exact (hp.ku' _)
  · exact (hp.ku _)

theorem Par.kQK (hp : Par D L0) (l c : ℕ) : kQK D l c ≤ 32 := by
  unfold FFSeg.kQK
  split_ifs
  · exact (hp.kq _)
  · exact (hp.kk _)

theorem Par.np (hp : Par D L0) (ν : ℕ) : (npOf D ν).OK := by
  unfold npOf
  split_ifs
  · exact (hp.n1 _)
  · exact (hp.n2 _)

section Run

variable (hp : Par D L0) (R : Runs D tb w L0 x o)
include hp R

/-- Under `Par`, `Runs`: no range condition of a hidden unit of the segment (`hl`, `hy`), at a
position i < T, fails. -/
theorem unit_ok {l y i : ℕ} (hl : l < D.nl) (hy : y < D.f) (hi : i < D.T) :
    UNIT.OK D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (x (2 * l + 1)) i y)
      (FF.wg (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i y)
      (FF.wu (D.Pl l) (w l) (L0 + l) (x (2 * l + 1)) i y)
      (FF.kG (D.Pl l) (L0 + l) y) (FF.kU (D.Pl l) (L0 + l) y) := by
  refine (R.ff l hl i (lt_of_lt_of_le hi hp.T)).2.2 y ?_
  unfold FF.units
  have h1 := hp.f
  have e1 : D.f = (D.Pl l).f := rfl
  have e2 : D.fe = (D.Pl l).fe := rfl
  split_ifs <;> omega

/-- Under `Par`, `Runs`, for ν < 2 nl and i < T: the normalisation at the index ν of the stream does
not halt. -/
theorem norm_ok {ν i : ℕ} (hν : ν < 2 * D.nl) (hi : i < D.T) : NORM.OK (npOf D ν) D.d (x ν i) := by
  have hi' := lt_of_lt_of_le hi hp.T
  unfold npOf
  split_ifs with h
  · have e : 2 * (ν / 2) = ν := by omega
    have := (R.att (ν / 2) (by omega) i hi').1
    rwa [e] at this
  · have e : 2 * (ν / 2) + 1 = ν := by omega
    have := (R.ff (ν / 2) (by omega) i hi').1
    rwa [e] at this

/-- Under `Par`, `Runs`, for ν < 2 nl and i < T: the conditions of the honest ledger
(`Ledger.HonHyp`) hold. -/
theorem honHyp {ν i : ℕ} (hν : ν < 2 * D.nl) (hi : i < D.T) :
    Ledger.HonHyp (npOf D ν) D.d fun l j => cellW 5 (x ν i j) l where
  eps_pos := (hp.np ν).1
  eps_lt := (hp.np ν).2.1
  M_le := (hp.np ν).2.2.2.1
  d_le := hp.d
  cell := fun l hl j hj => R.wr ν (by omega) i hi j hj l hl
  fits := by
    rw [xOf_cells]
    exact (norm_ok hp R hν hi).1

theorem R_hon {ν i : ℕ} (hν : ν < 2 * D.nl) (hi : i < D.T) :
    Ledger.R (led H ν i) = NORM.R (npOf D ν) D.d (x ν i) := by
  rw [led_hon, Ledger.hon_R (honHyp hp R hν hi), xOf_cells]

end Run

/-! ## Part 2. The arrays of the router -/

section RouterArrays

variable (D tb w L0 x o)
variable {l : ℕ} (he : isExpL l = true)
include he

theorem ly_hon (e i : ℕ) : val H .ly (l / 2) e i = FF.ly (D.Pl l) (w l) (x (2 * l + 1)) i e := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show FF.ly (D.Pl (2 * (l / 2) + 1)) (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i e = _
  rw [e1, e2]
theorem l3_hon (e i : ℕ) : val H .l3 (l / 2) e i = FF.l3 (D.Pl l) (w l) (x (2 * l + 1)) i e := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show FF.l3 (D.Pl (2 * (l / 2) + 1)) (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i e = _
  rw [e1, e2]
theorem lr_hon (e i : ℕ) : val H .lr (l / 2) e i = FF.lr (D.Pl l) (w l) (x (2 * l + 1)) i e := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show FF.lr (D.Pl (2 * (l / 2) + 1)) (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i e = _
  rw [e1, e2]
theorem rl_hon (e i : ℕ) :
    val H .rl (l / 2) e i =
      hd (dot D.d (FF.m (D.Pl l) (x (2 * l + 1)) i) fun j => (w l).Wr j e) (D.Pl l).kr := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show hd (dot D.d (FF.m (D.Pl (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i) fun j =>
        (w (2 * (l / 2) + 1)).Wr j e)
      (D.Pl (2 * (l / 2) + 1)).kr = _
  rw [e1, e2]
theorem sel_hon (e i : ℕ) :
    val H .sel (l / 2) e i = if e = FF.es (D.Pl l) (w l) (x (2 * l + 1)) i then 1 else 0 := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show (if e = FF.es (D.Pl (2 * (l / 2) + 1)) (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i then
        (1 : ℤ)
      else 0) = _
  rw [e1, e2]
theorem sc_hon (n i : ℕ) : val H .sc (l / 2) n i = FF.sc (D.Pl l) tb (w l) (x (2 * l + 1)) i := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show FF.sc (D.Pl (2 * (l / 2) + 1)) tb (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i = _
  rw [e1, e2]
theorem xr_hon (j i : ℕ) : val H .xr (l / 2) j i = FF.xr (D.Pl l) tb (w l) (x (2 * l + 1)) i j := by
  obtain ⟨e1, e2⟩ := odd_layer he
  rw [val_hon]
  show FF.xr (D.Pl (2 * (l / 2) + 1)) tb (w (2 * (l / 2) + 1)) (x (4 * (l / 2) + 3)) i j = _
  rw [e1, e2]

end RouterArrays

/-- the honest values of the router of layer ℓ at position i, as a record of
Inst/Model/Common/Router.lean -/
def rv (D : Dim) (tb : Tables) (w : ℕ → LayerW) (x : ℕ → ℕ → Vec) (l i : ℕ) : Router.RouterV :=
  Router.hon tb (D.Pl l).kr D.nx (FF.m (D.Pl l) (x (2 * l + 1)) i) fun e =>
    dot D.d (FF.m (D.Pl l) (x (2 * l + 1)) i) fun j => (w l).Wr j e

/-! ## Part 3. The 34 families -/

omit scl in
theorem site_in (A : ℤ) (k : ℕ) : InLutZ R16 (site A (rhu A k) (hd A k) k) :=
  inLutZ_r16 (site_hon A k).2.1 (site_hon A k).2.2

omit scl in
theorem high_in16 (A : ℤ) {k : ℕ} (hk : 16 ≤ k ∧ k ≤ 32) : InLutZ R16 (high (hd A k) k 32) := by
  have h := high_hon A (w := 16) rfl hk.1 hk.2
  exact inLutZ_r16 h.1 h.2

omit scl in
theorem ssite_in (A : ℤ) (k : ℕ) : InLutZ R16 (ssite A (rhu A k) (hd A k) k) :=
  inLutZ_r16 (ssite_hon A k).2.1 (ssite_hon A k).2.2

omit scl in
theorem shigh_in8 (A : ℤ) {k : ℕ} (hk : k ≤ 24) : InLutZ R8 (shigh (hd A k) k 24) := by
  have h := shigh_hon A (w := 8) rfl hk
  exact inLutZ_r8 h.1 h.2

omit scl in
theorem shigh_in16 (A : ℤ) {k : ℕ} (hk : k ≤ 32) : InLutZ R16 (shigh (hd A k) k 32) := by
  have h := shigh_hon A (w := 16) rfl hk
  exact inLutZ_r16 h.1 h.2

theorem npOf_even (D : Dim) (l : ℕ) : npOf D (2 * l) = (D.Pl l).n1 := by
  unfold npOf
  rw [if_pos (by omega), show 2 * l / 2 = l by omega]

theorem npOf_odd (D : Dim) (l : ℕ) : npOf D (2 * l + 1) = (D.Pl l).n2 := by
  unfold npOf
  rw [if_neg (by omega), show (2 * l + 1) / 2 = l by omega]

section Sums

variable (D tb w L0 x o)

theorem Ar_hon (l e i : ℕ) :
    ∑ j ∈ range D.d, val H .m l j i * (WR l).Wr j e =
      dot D.d (FF.m (D.Pl l) (x (2 * l + 1)) i) fun j => (w l).Wr j e := by
  unfold dot
  exact sum_congr rfl fun j _ => by rw [val_hon]; simp only [LW.ofInt, Int.cast_id]; rfl

theorem Ao_hon (l c i : ℕ) :
    ∑ j ∈ range D.dq, val H .o l j i * (WR l).Wo j c = dot D.dq (o l i) fun j => (w l).Wo j c := by
  unfold dot
  exact sum_congr rfl fun j _ => by rw [val_hon]; simp only [LW.ofInt, Int.cast_id]; rfl

theorem mr_hon' {l : ℕ} (he : isExpL l = true) (i : ℕ) :
    mr D H (l / 2) i = (rv D tb w x l i).mr D.nx := by
  unfold mr Router.RouterV.mr
  exact sum_congr rfl fun e _ => by rw [sel_hon D tb w L0 x o he, lr_hon D tb w L0 x o he]; rfl

end Sums

section Families

variable (hp : Par D L0) (R : Runs D tb w L0 x o)
include hp R

/-- Under `Par`, `Runs`: every key of the relation (`KeyName`), on the honest trace, is an entry of
its table, over the integers. -/
theorem key_hon (s : Fam) {l y i : ℕ} (hl : l < D.nl) (hpr : present s l = true)
    (hy : y < len D s) (hi : i < D.T) :
    InLutZ (lut tb (call s)) (key D H tb L0 WR s l y i) := by
  have hi' : i < D.P.T := lt_of_lt_of_le hi hp.T
  have UK := fun hy' : y < D.f =>
    Unit.hon_keys (tb := tb) (unit_ok hp R hl hy' hi) (hp.kG _ (L0 + l) y) (hp.kU _ (L0 + l) y)
  have RK := fun he : isExpL l = true =>
    Router.hon_keys (tb := tb) (m := FF.m (D.Pl l) (x (2 * l + 1)) i)
      (Ar := fun e => dot D.d (FF.m (D.Pl l) (x (2 * l + 1)) i) fun j => (w l).Wr j e) hp.nx
      (hp.kr _) ((R.ff l hl i hi').2.1 ((isExpL_iff hp.even l).1 he))
  cases s with
  | G =>
    simp only [key, Ag_hon D tb w x o hp.even hp.nx, kG_eq D hp.even, gw, val_hon]
    exact (UK hy).2.2.2.2.1
  | U =>
    simp only [key, Au_hon D tb w x o hp.even hp.nx, kU_eq D hp.even, val_hon]
    exact (UK hy).2.2.2.2.2.2.1
  | UT =>
    simp only [key, val_hon]
    exact (UK hy).2.2.2.1
  | GH =>
    simp only [key, kG_eq D hp.even, val_hon]
    exact (UK hy).2.2.2.2.2.1
  | UH =>
    simp only [key, kU_eq D hp.even, val_hon]
    exact (UK hy).2.2.2.2.2.2.2
  | G0 =>
    simp only [key, val_hon]
    exact (UK hy).1
  | F =>
    simp only [key, val_hon]
    exact (UK hy).2.1
  | CG =>
    simp only [key, val_hon]
    exact (UK hy).2.2.1
  | QK =>
    simp only [key, Y'_hon, val_hon]
    exact ssite_in _ _
  | QKH =>
    simp only [key, val_hon]
    exact shigh_in16 _ (hp.kQK _ y)
  | N1 =>
    simp only [key, xS_hon, R_hon hp R (show 2 * l < 2 * D.nl by omega) hi, npOf_even, val_hon]
    exact site_in _ _
  | N1H =>
    simp only [key, val_hon]
    exact high_in16 _ ⟨by have := (hp.n1 l).2.2.2.2.1; omega, (hp.n1 l).2.2.2.2.2.1⟩
  | N2 =>
    simp only [key, xS_hon, R_hon hp R (show 2 * l + 1 < 2 * D.nl by omega) hi, npOf_odd, val_hon]
    exact site_in _ _
  | N2H =>
    simp only [key, val_hon]
    exact high_in16 _ ⟨by have := (hp.n2 l).2.2.2.2.1; omega, (hp.n2 l).2.2.2.2.2.1⟩
  | O =>
    simp only [key]
    rw [Ao_hon]
    simp only [xS_hon, val_hon]
    rw [R.pl7 l hl i hi y hy, add_sub_cancel_left]
    exact ssite_in _ _
  | OH =>
    simp only [key, val_hon]
    exact shigh_in8 _ (hp.ko _)
  | D =>
    simp only [key, Ad_hon D tb w x o hp.even hp.nx, xS_hon, val_hon]
    rw [R.pl13 l hl i hi y hy, FF.x'', add_sub_cancel_left]
    exact ssite_in _ _
  | DH =>
    simp only [key, val_hon]
    exact shigh_in8 _ (hp.kd _)
  | V =>
    simp only [key, Av_hon, val_hon]
    exact ssite_in _ _
  | VH =>
    simp only [key, val_hon]
    exact shigh_in8 _ (hp.kv _)
  | LR =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, Ar_hon, lw, ly_hon D tb w L0 x o he,
      l3_hon D tb w L0 x o he, rl_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).1
  | LH =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, rl_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).2.1
  | L3 =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, l3_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).2.2.1
  | CLR =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, ly_hon D tb w L0 x o he, lr_hon D tb w L0 x o he, l3_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).2.2.2.1
  | LT =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, lr_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).2.2.2.2.1
  | SEL =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, sel_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).2.2.2.2.2.1
  | DD =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, mr_hon' D tb w L0 x o he, lr_hon D tb w L0 x o he, sel_hon D tb w L0 x o he]
    exact ((RK he).1 y hy).2.2.2.2.2.2
  | MR =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, mr_hon' D tb w L0 x o he, sc_hon D tb w L0 x o he]
    exact (RK he).2.1
  | XR =>
    have he : isExpL l = true := by simpa [present, isExp] using hpr
    simp only [key, sc_hon D tb w L0 x o he, xr_hon D tb w L0 x o he, val_hon]
    exact (RK he).2.2.1 y
  | ROW =>
    have hy' : y < 2 * nLedger := hy
    have hν : 2 * l + y / nLedger < 2 * D.nl := by
      have : y / nLedger < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hy')
      omega
    have hn : y % nLedger < 99 := Nat.mod_lt _ (by decide)
    simp only [key, Int.cast_id, led_hon]
    have h := Ledger.hon_typed (honHyp hp R hν hi) (y % nLedger) hn
    exact inLutZ_r8 h.1 (by linarith [h.2])
  | CN1 =>
    simp only [key, val_hon]
    exact fc_hon ((R.att l hl i hi').1.2 y hy)
  | CN2 =>
    simp only [key, val_hon]
    exact fc_hon ((R.ff l hl i hi').1.2 y hy)
  | CQK =>
    have hf := (R.att l hl i hi').2.1 y hy
    simp only [key, val_hon]
    by_cases hq : y < D.dq
    · rw [if_pos hq]
      exact fc_hon hf
    · rw [if_neg hq]
      have e : HV .kx l (y - D.dq) i =
          clamp 2047 (Att.qkw (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i y) := by
        show clamp 2047
            (Att.qkw (D.Pl l) tb (w l) (L0 + l) (x (2 * l)) i (Att.dq (D.Pl l) + (y - D.dq))) = _
        have e2 : Att.dq (D.Pl l) + (y - D.dq) = y := by
          have : Att.dq (D.Pl l) = D.dq := rfl
          omega
        rw [e2]
      rw [e]
      exact fc_hon hf
  | CV =>
    simp only [key, val_hon]
    exact fc_hon ((R.att l hl i hi').2.2 y hy)

end Families

/-! ## Part 4. The identities -/

section Identities

variable (hp : Par D L0) (R : Runs D tb w L0 x o)
include hp R

/-- Under `Par`, `Runs`: (J1) to (J10) hold over the integers, and (J11) in the first segment, if
the stream at the index 0 is the embedding of the prompt. -/
theorem idn_hon (emb : ℕ → ℕ → ℤ) (tok : ℕ → ℕ) (first : Bool)
    (hf : first = true → ∀ i < D.T, ∀ j < D.d, x 0 i j = emb (tok i) j) :
    ∀ j : Idn, j.Valid D first → idnVal D H emb tok j = 0
  | .jn k ν i, hv => by
      have hν : ν < 2 * D.nl := hv.2.1
      have e : (fun l j => bS D H ν l j i) = fun l j => cellW 5 (x ν i j) l := by
        funext l j
        exact bS_hon D tb w L0 x o ν l j i
      simp only [idnVal, e, led_hon]
      exact Ledger.hon_idn (honHyp hp R hν hv.2.2) k hv.1
  | .j10 l' i, _ => by
      have he : isExpL (2 * l' + 1) = true := by
        unfold isExpL
        rw [beq_iff_eq]
        omega
      have h := sum_sel D tb w L0 x o hp.nx he i fun _ => 1
      have e : (2 * l' + 1) / 2 = l' := by omega
      rw [e] at h
      simp only [mul_one] at h
      simp only [idnVal, h, sub_self]
  | .j11 j i, hv => by
      simp only [idnVal, xS_hon]
      rw [hf hv.1 i hv.2.2 j hv.2.1, sub_self]

end Identities

end Inst.Model.FFSeg.Hon
