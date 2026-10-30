-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Sanity.lean: sanity lemmas on some definitions of Inst/Model/Program.lean.
To audit the relation `RinfPP` (Inst/Model/Scales.lean), nothing of this file need be read.
    Part 1  `rhu`, `isqrt`, `lowByte`, `maxTo`, `argTo` meet their descriptions
    Part 2  the order of the steps (which layer and which block makes X_{λ+1} from X_λ); Model_i is
            a partial function; the literals read back from `ppref`; no division by 0 at ς and den,
            if 1 ≤ ϵ, `tb.OK P` and 0 < `P.expRows` (`sig_pos`, `den_pos`); a matrix in a box is
            determined by its entries inside (`Box.ext`)
    Part 3  an index whose layers are all zero: if each of the ten shifts of a layer is at least 1
            (`Shifts1`), the stream never changes, and the program runs if the three normalisations
            do
    Part 4  a toy configuration on which the program runs and evaluates, and two indices that differ
            on an instance
Labels such as (N2): the head of Inst/Model/Program.lean.
Notation (Inst/Model/Program.lean): `rhu a k : ℤ`: `(a + 2 ^ (k - 1)) / 2 ^ k`, "the quotient by 2^k
rounded to the nearest integer, halves up" (k ≥ 1); `lowByte a : ℤ`: `(a + 128) % 256 - 128`, "the
balanced low byte of a"; ς: an integer, `NORM.sig`: (N2) ς = isqrt(V + ϵ); den: an integer,
`Att.den`: (PA5) den_i = Σ_{j ≤ i} wt_ij; the ten shifts of a layer: the fields kq to ku' of
`Params`; `sh`: a natural number, a field of `Params`: the shift applied to mx − sc before the
look-up in Exp, step (PA3); Model_i(prompt) = y: `ModelIs`.
-/
import Inst.Model.Program
import Inst.Model.Tables
import Mathlib.Tactic

set_option autoImplicit false

namespace Inst.Model

/-! ## Part 1 -/

theorem rhu_spec (a : ℤ) (k : ℕ) :
    2 ^ k * rhu a k ≤ a + 2 ^ (k - 1) ∧ a + 2 ^ (k - 1) < 2 ^ k * (rhu a k + 1) := by
  have hp : (0 : ℤ) < 2 ^ k := by positivity
  unfold rhu
  constructor
  · exact Int.mul_ediv_self_le hp.ne'
  · exact Int.lt_mul_ediv_self_add hp |>.trans_eq (by ring)

theorem rhu_zero {k : ℕ} (hk : 1 ≤ k) : rhu 0 k = 0 := by
  unfold rhu
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  apply Int.ediv_eq_zero_of_lt (by positivity)
  simp only [zero_add, Nat.add_sub_cancel, pow_succ]
  have : (0 : ℤ) < 2 ^ n := by positivity
  linarith

theorem isqrt_spec {v : ℤ} (hv : 0 ≤ v) :
    0 ≤ isqrt v ∧ isqrt v ^ 2 ≤ v ∧ v < (isqrt v + 1) ^ 2 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hv
  simp only [isqrt, Int.toNat_natCast]
  refine ⟨by positivity, ?_, ?_⟩
  · exact_mod_cast Nat.sqrt_le' n
  · exact_mod_cast Nat.lt_succ_sqrt' n

theorem lowByte_spec (a : ℤ) : -128 ≤ lowByte a ∧ lowByte a ≤ 127 ∧ (a - lowByte a) % 256 = 0 := by
  unfold lowByte
  omega

theorem maxTo_spec (f : Vec) (n : ℕ) : (∀ j ≤ n, f j ≤ maxTo f n) ∧ ∃ j ≤ n, f j = maxTo f n := by
  induction n with
  | zero => exact ⟨fun j hj => by rw [Nat.le_zero.1 hj]; exact le_rfl, 0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨h1, j0, hj0, h2⟩ := ih
    constructor
    · intro j hj
      rcases Nat.lt_or_ge j (n + 1) with h | h
      · exact (h1 j (by omega)).trans (le_max_left _ _)
      · rw [show j = n + 1 by omega]; exact le_max_right _ _
    · simp only [maxTo]
      rcases le_total (maxTo f n) (f (n + 1)) with h | h
      · exact ⟨n + 1, le_rfl, (max_eq_right h).symm⟩
      · exact ⟨j0, by omega, h2.trans (max_eq_left h).symm⟩

/-- argTo f n is the least index of a greatest value among f 0, ..., f n. -/
theorem argTo_spec (f : Vec) (n : ℕ) :
    argTo f n ≤ n ∧ (∀ j ≤ n, f j ≤ f (argTo f n)) ∧ ∀ j < argTo f n, f j < f (argTo f n) := by
  induction n with
  | zero =>
    exact ⟨le_rfl,
      fun j hj => by rw [Nat.le_zero.1 hj]; exact le_rfl,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [argTo]
    split_ifs with h
    · refine ⟨le_rfl, fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_ge j (n + 1) with h' | h'
        · exact ((h1 j (by omega)).trans_lt h).le
        · rw [show j = n + 1 by omega]
      · exact (h1 j (by omega)).trans_lt h
    · refine ⟨by omega, fun j hj => ?_, h2⟩
      rcases Nat.lt_or_ge j (n + 1) with h' | h'
      · exact h1 j (by omega)
      · rw [show j = n + 1 by omega]; exact not_lt.1 h

/-! ## Part 2 -/

section Order
variable (P : Params) (tb : Tables) (i : Weights) (prompt : Fin P.T → Fin P.V)

theorem X_succ (l : ℕ) : X P tb i prompt (l + 1) =
    if l % 2 = 0 then Att.x' P tb (i.layer (l / 2)) (l / 2) (X P tb i prompt l)
    else FF.x'' P tb (i.layer (l / 2)) (l / 2) (X P tb i prompt l) := rfl

/-- X_{2L+1} follows the attention block of layer L. -/
theorem X_att (L : ℕ) :
    X P tb i prompt (2 * L + 1) = Att.x' P tb (i.layer L) L (X P tb i prompt (2 * L)) := by
  have h1 : 2 * L % 2 = 0 := by omega
  have h2 : 2 * L / 2 = L := by omega
  simp only [X, h1, h2, if_true]

/-- X_{2L+2} follows the feed-forward block of layer L. -/
theorem X_ff (L : ℕ) :
    X P tb i prompt (2 * L + 2) = FF.x'' P tb (i.layer L) L (X P tb i prompt (2 * L + 1)) := by
  have h1 : (2 * L + 1) % 2 ≠ 0 := by omega
  have h2 : (2 * L + 1) / 2 = L := by omega
  simp only [X, h1, h2, if_false]

/-- Model_i is a partial function. -/
theorem modelIs_unique {y y' : ℕ} (h : ModelIs P tb i prompt y) (h' : ModelIs P tb i prompt y') :
    y = y' := by
  obtain ⟨-, hy, hmax, hleast⟩ := h
  obtain ⟨-, hy', hmax', hleast'⟩ := h'
  rcases Nat.lt_trichotomy y y' with hlt | heq | hgt
  · exact absurd (hmax y' hy') (not_le.2 (hleast' y hlt))
  · exact heq
  · exact absurd (hmax' y hy) (not_le.2 (hleast y' hgt))

/-- Under `hV` it is defined wherever no range condition fails. -/
theorem modelIs_of_runs (hV : 1 ≤ P.V) (h : Runs P tb i prompt) :
    ModelIs P tb i prompt (argTo (lg P tb i prompt (P.T - 1)) (P.V - 1)) := by
  obtain ⟨h0, h1, h2⟩ := argTo_spec (lg P tb i prompt (P.T - 1)) (P.V - 1)
  exact ⟨h, by omega, fun ι hι => h1 ι (by omega), h2⟩

end Order

/-- literals read back from `ppref` -/
theorem ppref_readback :
    Att.dq ppref = 5120 ∧
    Att.dq ppref + ppref.nkv * ppref.ch = 6144 ∧
    (∀ h, Att.kvOf ppref h = h / 5) ∧
    (∀ L, FF.units ppref L = 16384) ∧
    ppref.T - 1 = 1023 ∧
    2 * ppref.layers = 96 := by
  refine ⟨rfl, rfl, fun _ => rfl, fun L => ?_, rfl, rfl⟩
  unfold FF.units
  split_ifs <;> rfl

/-! Under the hypotheses below, no division by 0 is reached at ς and den. -/

/-- (N2) "So 1 ≤ ς": from ϵ ≥ 1. -/
theorem sig_pos (np : NormPar) (h : 1 ≤ np.eps) (d : ℕ) (x : Vec) : 1 ≤ NORM.sig np d x := by
  have hV : 0 ≤ NORM.V d x := Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨h0, -, h2⟩ := isqrt_spec (v := NORM.V d x + np.eps) (by linarith)
  unfold NORM.sig
  by_contra hc
  have h3 : isqrt (NORM.V d x + np.eps) = 0 := by omega
  rw [h3] at h2
  norm_num at h2
  linarith

/-- Under `hT`, `hE`: 2^12 ≤ den_i, from (Tab8). So the division in (PA7) is defined. -/
theorem den_pos (P : Params) (tb : Tables) (hT : tb.OK P) (hE : 0 < P.expRows) (w : LayerW) (L : ℕ)
    (x : ℕ → Vec) (h i : ℕ) :
    2 ^ 12 ≤ Att.den P tb w L x h i := by
  obtain ⟨-, -, -, hExp, hExp0⟩ := hT
  obtain ⟨hmax, j0, hj0, hj0e⟩ := maxTo_spec (Att.sc P tb w L x h i) i
  have hu : ∀ j ≤ i, 0 ≤ Att.u P tb w L x h i j := fun j hj =>
    Int.ediv_nonneg (by have := hmax j hj; unfold Att.mx; linarith) (by norm_num)
  have hw : ∀ j ∈ Finset.range (i + 1), 0 ≤ Att.wt P tb w L x h i j := by
    intro j hj
    have hj' : j ≤ i := by have := Finset.mem_range.1 hj; omega
    unfold Att.wt
    split_ifs with hlt
    · have h1 := hExp (Att.u P tb w L x h i j).toNat (by have := hu j hj'; omega)
      rw [Int.toNat_of_nonneg (hu j hj')] at h1
      linarith [h1.1]
    · exact le_rfl
  have hw0 : Att.wt P tb w L x h i j0 = 2 ^ 12 := by
    have hu0 : Att.u P tb w L x h i j0 = 0 := by simp [Att.u, Att.mx, hj0e]
    simp [Att.wt, hu0, hE, hExp0]
  unfold Att.den
  rw [← hw0]
  exact Finset.single_le_sum hw (Finset.mem_range.2 (by omega))

/-- A matrix in a box is determined by its entries inside. -/
theorem Box.ext {r c : ℕ} {lo hi : ℤ} {W W' : Mat} (h : Box r c lo hi W) (h' : Box r c lo hi W')
    (e : ∀ j < r, ∀ x < c, W j x = W' j x) : W = W' := by
  funext j x
  have a := h j x
  have b := h' j x
  by_cases hin : j < r ∧ x < c
  · exact e j hin.1 x hin.2
  · rw [if_neg hin] at a b
    rw [a, b]

/-! ## Part 3.  All layers zero -/

/-- the layer whose matrices are all zero -/
def zeroLayer : LayerW :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

theorem dot_zero (n : ℕ) (a : Vec) : dot n a (fun _ => 0) = 0 := by simp [dot]

theorem fits16_zero : Fits16 0 := by unfold Fits16; norm_num

section Zero
variable (P : Params) (tb : Tables) (L : ℕ) (x : ℕ → Vec)

theorem att_zero (hko : 1 ≤ P.ko) : Att.x' P tb zeroLayer L x = x := by
  funext i c
  simp [Att.x', zeroLayer, dot_zero, rhu_zero hko]

theorem att_ok_zero (hq : 1 ≤ P.kq) (hk : 1 ≤ P.kk) (hv : 1 ≤ P.kv) :
    Att.OK P tb zeroLayer L x ↔ ∀ i < P.T, NORM.OK P.n1 P.d (x i) := by
  have h1 : ∀ i c, Att.qkw P tb zeroLayer L x i c = 0 := by
    intro i c
    have hA : ∀ c', Att.AY P zeroLayer x i c' = 0 := by
      intro c'
      simp [Att.AY, Att.Aq, Att.Ak, zeroLayer, dot_zero]
    simp only [Att.qkw, Att.Y', hA, mul_zero, sub_zero, add_zero, ite_self]
    split_ifs
    · exact rhu_zero hq
    · exact rhu_zero hk
  have h2 : ∀ i c, Att.vw P zeroLayer x i c = 0 := by
    intro i c
    simp [Att.vw, Att.Av, zeroLayer, dot_zero, rhu_zero hv]
  simp only [Att.OK, h1, h2]
  exact ⟨fun h i hi => (h i hi).1,
    fun h i hi => ⟨h i hi, fun _ _ => fits16_zero, fun _ _ => fits16_zero⟩⟩

theorem ff_zero (hkd : 1 ≤ P.kd) : FF.x'' P tb zeroLayer L x = x := by
  funext i c
  simp [FF.x'', FF.Ad, zeroLayer, rhu_zero hkd]

theorem ff_ok_zero (hr : 1 ≤ P.kr) (hg : 1 ≤ P.kg) (hu : 1 ≤ P.ku)
    (hg' : 1 ≤ P.kg') (hu' : 1 ≤ P.ku') :
    FF.OK P tb zeroLayer L x ↔ ∀ i < P.T, NORM.OK P.n2 P.d (x i) := by
  have h1 : ∀ i e, FF.ly P zeroLayer x i e = 0 := by
    intro i e
    simp [FF.ly, FF.l3, FF.lw, zeroLayer, dot_zero, rhu_zero hr]
  have hkG : ∀ j, 1 ≤ FF.kG P L j := by intro j; unfold FF.kG; split_ifs <;> assumption
  have hkU : ∀ j, 1 ≤ FF.kU P L j := by intro j; unfold FF.kU; split_ifs <;> assumption
  have hwg : ∀ i j, FF.wg P zeroLayer L x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wg, zeroLayer]
  have hwu : ∀ i j, FF.wu P zeroLayer L x i j = fun _ => 0 := by
    intro i j; funext t; simp [FF.wu, zeroLayer]
  have h2 : ∀ i j,
      UNIT.OK P.d (FF.z P tb zeroLayer L x i j) (FF.wg P zeroLayer L x i j)
        (FF.wu P zeroLayer L x i j) (FF.kG P L j) (FF.kU P L j) := by
    intro i j
    simp only [UNIT.OK, UNIT.gh, UNIT.g0, UNIT.gw, UNIT.up, hwg, hwu, dot_zero, rhu_zero (hkG j),
      rhu_zero (hkU j), lowByte]
    refine ⟨by norm_num, fits16_zero⟩
  simp only [FF.OK, h1]
  exact ⟨fun h i hi => (h i hi).1,
    fun h i hi => ⟨h i hi, fun _ _ _ => fits16_zero, fun j _ => h2 i j⟩⟩

end Zero

/-- each of the ten shifts of a layer (kq .. ku') is at least 1 -/
def Params.Shifts1 (P : Params) : Prop :=
  1 ≤ P.kq ∧ 1 ≤ P.kk ∧ 1 ≤ P.kv ∧ 1 ≤ P.ko ∧ 1 ≤ P.kg ∧ 1 ≤ P.ku ∧ 1 ≤ P.kd ∧
  1 ≤ P.kr ∧ 1 ≤ P.kg' ∧ 1 ≤ P.ku'

section ZeroIndex
variable (P : Params) (tb : Tables) (Emb H : Mat) (prompt : Fin P.T → Fin P.V)

/-- With all layers zero, under `hs`, the stream never changes. -/
theorem X_zero (hs : P.Shifts1) (l : ℕ) :
    X P tb ⟨fun _ => zeroLayer, Emb, H⟩ prompt l =
      X P tb ⟨fun _ => zeroLayer, Emb, H⟩ prompt 0 := by
  obtain ⟨-, -, -, hko, -, -, hkd, -, -, -⟩ := hs
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [X_succ]
    split_ifs
    · rw [att_zero P tb _ _ hko, ih]
    · rw [ff_zero P tb _ _ hkd, ih]

/-- With all layers zero, under `hs`, the program runs if the three normalisations accept the
embedding rows of the prompt. -/
theorem runs_zero (hs : P.Shifts1)
    (hn : ∀ pos < P.T,
      NORM.OK P.n1 P.d (X P tb ⟨fun _ => zeroLayer, Emb, H⟩ prompt 0 pos) ∧
      NORM.OK P.n2 P.d (X P tb ⟨fun _ => zeroLayer, Emb, H⟩ prompt 0 pos) ∧
      NORM.OK P.nf P.d (X P tb ⟨fun _ => zeroLayer, Emb, H⟩ prompt 0 pos)) :
    Runs P tb ⟨fun _ => zeroLayer, Emb, H⟩ prompt := by
  obtain ⟨hq, hk, hv, -, hg, hu, -, hr, hg', hu'⟩ := id hs
  refine ⟨fun L _ => ⟨?_, ?_⟩, fun pos hpos => ?_⟩
  · rw [att_ok_zero P tb L _ hq hk hv, X_zero P tb Emb H prompt hs]
    exact fun pos hpos => (hn pos hpos).1
  · rw [ff_ok_zero P tb L _ hr hg hu hg' hu', X_zero P tb Emb H prompt hs]
    exact fun pos hpos => (hn pos hpos).2.1
  · rw [X_zero P tb Emb H prompt hs]
    exact (hn pos hpos).2.2

end ZeroIndex

/-! ## Part 4.  A toy configuration -/

/-- 2 positions, 2 tokens, 2 layers (one dense, one with one expert), width 1; the ten shifts of a
layer all 1; sh = 8; NORM with M = 4, K = 1, ϵ = 7 -/
def toyP : Params where
  T := 2
  V := 2
  layers := 2
  d := 1
  nq := 1
  nkv := 1
  ch := 2
  f := 2
  fe := 1
  nexp := 1
  kq := 1
  kk := 1
  kv := 1
  ko := 1
  kg := 1
  ku := 1
  kd := 1
  kr := 1
  kg' := 1
  ku' := 1
  n1 := ⟨4, 1, 7⟩
  n2 := ⟨4, 1, 7⟩
  nf := ⟨4, 1, 7⟩
  expRows := 1
  sh := 8

def toyTb : Tables := ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- every token is embedded as the number 3 -/
def toyEmb : Mat := fun t j => if t < 2 ∧ j < 1 then 3 else 0
/-- the output matrix that favours the token v -/
def toyH (v : ℕ) : Mat := fun j ι => if j < 1 ∧ ι < 2 then (if ι = v then 1 else 0) else 0
/-- for v = 0, 1: two indices, which differ in the output matrix only -/
def toyI (v : ℕ) : Weights := ⟨fun _ => zeroLayer, toyEmb, toyH v⟩
def toyPrompt : Fin toyP.T → Fin toyP.V := fun _ => ⟨0, by show 0 < 2; norm_num⟩

theorem toy_X0 (v pos : ℕ) (h : pos < 2) :
    X toyP toyTb (toyI v) toyPrompt 0 pos = fun j => if j < 1 then 3 else 0 := by
  funext j
  have hT : pos < toyP.T := h
  simp [X, hT, toyI, toyEmb, toyPrompt]

theorem sqrt16 : Nat.sqrt 16 = 4 := Nat.sqrt_eq' 4

/-- NORM on the vector (3): V = 9, ς = isqrt 16 = 4, R = ⌊(16 + 2)/4⌋ = 4, yw = rhu(12, 1) = 6,
out = 6. -/
theorem toy_norm_yw : NORM.yw ⟨4, 1, 7⟩ 1 (fun j => if j < 1 then 3 else 0) 0 = 6 := by
  simp [NORM.yw, NORM.R, NORM.sig, NORM.V, isqrt, rhu, sqrt16]

theorem toy_norm_ok : NORM.OK ⟨4, 1, 7⟩ 1 (fun j => if j < 1 then 3 else 0) := by
  refine ⟨by simp [NORM.V], fun j hj => ?_⟩
  rw [show j = 0 by omega, toy_norm_yw]
  unfold Fits16
  norm_num

theorem toy_runs (v : ℕ) : Runs toyP toyTb (toyI v) toyPrompt := by
  refine runs_zero toyP toyTb toyEmb (toyH v) toyPrompt
    (by simp [Params.Shifts1, toyP]) fun pos hpos => ?_
  have e := toy_X0 v pos hpos
  simp only [toyI] at e
  rw [e]
  exact ⟨toy_norm_ok, toy_norm_ok, toy_norm_ok⟩

/-- the logits at the last position: 6 for the favoured token, 0 for the other -/
theorem toy_lg (v ι : ℕ) (hι : ι < 2) :
    lg toyP toyTb (toyI v) toyPrompt 1 ι = if ι = v then 6 else 0 := by
  have hX : X toyP toyTb (toyI v) toyPrompt (2 * toyP.layers) 1 =
      fun j => if j < 1 then 3 else 0 := by
    have :=
      X_zero toyP toyTb toyEmb (toyH v) toyPrompt (by simp [Params.Shifts1, toyP]) (2 * toyP.layers)
    simp only [toyI] at *
    rw [this]
    exact toy_X0 v 1 (by norm_num)
  have hn : nrm toyP toyTb (toyI v) toyPrompt 1 0 = 6 := by
    simp only [nrm, hX, NORM.out]
    show clamp 2047 (NORM.yw ⟨4, 1, 7⟩ 1 (fun j => if j < 1 then 3 else 0) 0) = 6
    rw [toy_norm_yw]
    simp [clamp]
  have hd : toyP.d = 1 := rfl
  simp only [lg, dot, hd, Finset.sum_range_one, hn]
  simp [toyI, toyH, hι]

/-- The program runs and evaluates: for v < 2, the index that favours v outputs v. -/
theorem toy_model (v : ℕ) (hv : v < 2) : ModelIs toyP toyTb (toyI v) toyPrompt v := by
  have hT : toyP.T - 1 = 1 := rfl
  refine ⟨toy_runs v, hv, fun ι hι => ?_, fun ι hι => ?_⟩
  · rw [hT, toy_lg v ι hι, toy_lg v v hv, if_pos rfl]
    split_ifs <;> norm_num
  · rw [hT, toy_lg v ι (by omega), toy_lg v v hv, if_neg (by omega), if_pos rfl]
    norm_num

theorem two_zero : Two 0 0 (fun _ _ => 0) := by intro j x; simp

theorem toy_wf (v : ℕ) : (toyI v).WF toyP := by
  have hz : ∀ r c, Two r c (fun _ _ => 0) := by
    intro r c j x
    split_ifs <;> norm_num
  refine ⟨fun L => ?_, ?_, ?_⟩
  · split_ifs with hL
    · refine ⟨hz _ _, hz _ _, hz _ _, hz _ _, ?_⟩
      split_ifs
      · exact ⟨hz _ _, hz _ _, hz _ _, hz _ _,
          fun e => by split_ifs <;> exact ⟨hz _ _, hz _ _, hz _ _⟩⟩
      · exact ⟨hz _ _, hz _ _, hz _ _, hz _ _, fun e => ⟨hz _ _, hz _ _, hz _ _⟩⟩
    · exact ⟨hz _ _, hz _ _, hz _ _, hz _ _, hz _ _, hz _ _, hz _ _,
        hz _ _, fun e => ⟨hz _ _, hz _ _, hz _ _⟩⟩
  · intro j x
    show if j < 2 ∧ x < 1 then _ ≤ toyEmb j x ∧ toyEmb j x ≤ _ else toyEmb j x = 0
    unfold toyEmb
    split_ifs <;> norm_num
  · intro j x
    show if j < 1 ∧ x < 2 then _ ≤ toyH v j x ∧ toyH v j x ≤ _ else toyH v j x = 0
    unfold toyH
    split_ifs <;> norm_num

/-- Two indices that differ on an instance: (prompt, 1) is in L(i) for the index that favours 1 and
not for the one that favours 0. -/
theorem toy_differ :
    Rinf toyP toyTb ⟨toyI 1, toy_wf 1⟩ (Instance.nextOf toyPrompt ⟨1, by show 1 < 2; norm_num⟩) ∧
    ¬ Rinf toyP toyTb ⟨toyI 0, toy_wf 0⟩
      (Instance.nextOf toyPrompt ⟨1, by show 1 < 2; norm_num⟩) := by
  refine ⟨toy_model 1 (by norm_num), fun h => ?_⟩
  have : (1 : ℕ) = 0 := modelIs_unique toyP toyTb (toyI 0) toyPrompt h (toy_model 0 (by norm_num))
  exact absurd this (by norm_num)

/-- A configuration on which the program halts on every prompt (the theorem below: at `toyPrompt`,
for every `toyI v`): with ϵ = 2^78 in the final normalisation the test of (N1) fails, and no y is
the output.
(Halting by each of the six kinds of range condition, on non-zero weights, is covered by evaluation
only, and that evaluation is not part of this library; but for (PL5): `halts_haltW`,
Inst/Model/SanityRef.lean; `halts_pB`, Inst/Model/SanityPart.lean.) -/
theorem halts_example (v y : ℕ) :
    ¬ ModelIs { toyP with nf := ⟨4, 1, 2 ^ 78⟩ } toyTb (toyI v) toyPrompt y := by
  rintro ⟨⟨-, h⟩, -⟩
  have h0 := (h 0 (by show 0 < 2; norm_num)).1
  have hV : 0 ≤
      NORM.V 1 (X { toyP with nf := ⟨4, 1, 2 ^ 78⟩ } toyTb (toyI v) toyPrompt (2 * 2) 0) :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have : NORM.V 1 (X { toyP with nf := ⟨4, 1, 2 ^ 78⟩ } toyTb (toyI v) toyPrompt (2 * 2) 0) +
        2 ^ 78 < 2 ^ 78 := h0
  linarith

end Inst.Model
