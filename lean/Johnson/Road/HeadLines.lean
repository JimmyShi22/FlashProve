-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLines.lean: what the forms of the output head's lookup keys are worth on cells: the
tools, and two families.

Two texts describe the keys that the output head's sub-proof looks up. The verifier in OnBytes/
builds, for each segment of a lookup call, an affine form in entries of the reads (LINE in
OnBytes/Model/HeadForms.lean). The library defines, for each family, the key at one entry and one
position as a polynomial in the cells (Inst/Model/Head/Trace.lean; Cm/TargetPHead.lean;
Policy/Rel/LedgerHead.lean). This file states in what sense the first is the second.

The sense. An entry of the reads stands for a sum of cells under the equality weights of a point. In
a world where every entry that a form names holds that sum (LongAt, ShortAt), the value of the form
of a segment is the sum, over the segment's entries x, of the weight of x times the multilinear
extension, over the positions, of the keys at x.

The statements are written with the sizes as letters (Johnson/Road/HeadSizes.lean). Each has a
corollary at the library's sizes, in the library's own names.

Main definitions: LongAt, ShortAt (a table of the reads is true of cells); SegFit, SegHas, PosFit
(what is asked of a segment's columns and of its call's point); Laid (what is asked of the layout's
numbers); ReqFits (the request as the library's record); npOf.
Main theorems: Sl_cells; SegFit.blocked, SegHas.size, PosFit.zt; wsum_pos, onSum_value, wxOf_value;
line_NFH, line_HD1.

What is not claimed. Nothing is said about when a world is true, about the weights' origin, or about
what a verifier's acceptance shows. Every theorem on a form begins "if the routine succeeds": none
says that it does. That the records Laid, SegFit, SegHas, PosFit and ReqFits hold of what the
verifier's functions return is not shown here (Johnson/Road/HeadLaid.lean has the part on the
layout and the request; Johnson/Road/HeadPoint.lean has the part on the key points, for a run on a
view, under hypotheses that it names). The program does not import this file.
-/
import Johnson.Road.HeadKit
import Johnson.Road.HeadSizes
import Johnson.Road.FormsKeysEq

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

section Tools

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-! ## True tables -/

/-- The long table with the name nm is true of the cells c at the point (low | u): every entry that
a form can name holds the cells of its block of 2^ls features, summed under the equality weights of
low over the features of the block and of u over the 2^lt positions. K3: the number of columns of
the array that stores the reads. -/
def LongAt (R : Model.Head.Run) (K3 : ℕ) (nm : String) (ls lt : ℕ) (low u : ℕ → K)
    (c : ℕ → ℕ → K) : Prop :=
  ∀ tb, Starts R nm tb → ∀ b, Valid R tb b →
    rdW W R.iU3 K3 (tb + b) = ∑ r ∈ range (2 ^ ls),
      Blocks.eqN ls 0 low r * Blocks.ext lt (fun i => c (b * 2 ^ ls + r) i) u

/-- The short table with the name nm is true of the cells c at the point u: every entry that a form
can name holds its feature's cells, summed over the 2^lt positions under the equality weights of
u. -/
def ShortAt (R : Model.Head.Run) (K3 : ℕ) (nm : String) (lt : ℕ) (u : ℕ → K)
    (c : ℕ → ℕ → K) : Prop :=
  ∀ tb, Starts R nm tb → ∀ φ, Valid R tb φ →
    rdW W R.iU3 K3 (tb + φ) = Blocks.ext lt (fun i => c φ i) u

variable {ρ W}

/-- A table has one first entry. -/
theorem Starts.unique {R : Model.Head.Run} {nm : String} {a b : ℕ} (h1 : Starts R nm a)
    (h2 : Starts R nm b) : a = b := by
  unfold Starts at h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- A tensor of the matrix hf under a segment's weights, on cells: the weighted sum, over the
segment's entries, of the extension of the value that the nl limbs spell. -/
theorem Sl_cells (hρ : Numerals ρ) {R : Model.Head.Run} {sn : String} {OFF nl J lt : ℕ}
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {c : ℕ → ℕ → K}
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls lt low u c)
    (hdiv : ∀ l, l < nl → 2 ^ R.h.ls ∣ OFF + l * J)
    (h : Ok (Model.Head.Sl R sn OFF nl J) F C a G D) :
    G = F ∧ D = C ∧ ∃ wh, Ok (Model.Head.ewh R sn) F C wh F C ∧
      ∀ ew : Array E, Blocked ρ ew wh R.h.ls low →
        a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) lt u (wh.size * 2 ^ R.h.ls)
          (fun x i => ∑ l ∈ range nl, (256 : K) ^ l * c (OFF + l * J + x) i) := by
  obtain ⟨e1, e2, wh, tb, hwh, hst, hval, hv⟩ := Sl_value ρ W hρ h
  refine ⟨e1, e2, wh, hwh, fun ew hB => ?_⟩
  rw [hv]
  unfold wsum
  rw [sum_blocks]
  refine sum_congr rfl fun xh hxh => ?_
  have hS : R.h.S2 = 2 ^ R.h.ls := rfl
  have step : ∀ l, l < nl →
      rdW W R.iU3 (colsOf F R.iU3) (tb + ((OFF + l * J) / R.h.S2 + xh)) =
        ∑ r ∈ range (2 ^ R.h.ls), Blocks.eqN R.h.ls 0 low r *
          Blocks.ext lt (fun i => c (OFF + l * J + (xh * 2 ^ R.h.ls + r)) i) u := by
    intro l hl
    rw [hL tb hst _ (hval xh (mem_range.mp hxh) l hl)]
    refine sum_congr rfl fun r _ => ?_
    obtain ⟨q, hq⟩ := hdiv l hl
    have hpos : 0 < 2 ^ R.h.ls := by positivity
    have e : ((OFF + l * J) / R.h.S2 + xh) * 2 ^ R.h.ls + r =
        OFF + l * J + (xh * 2 ^ R.h.ls + r) := by
      rw [hS, hq, Nat.mul_div_cancel_left q hpos]
      ring
    rw [e]
  have s1 : ∑ l ∈ range nl, ((256 : K) ^ l * ρ.val (wh.getD xh zeroE)) *
        rdW W R.iU3 (colsOf F R.iU3) (tb + ((OFF + l * J) / R.h.S2 + xh)) =
      ∑ l ∈ range nl, ((256 : K) ^ l * ρ.val (wh.getD xh zeroE)) *
        ∑ r ∈ range (2 ^ R.h.ls), Blocks.eqN R.h.ls 0 low r *
          Blocks.ext lt (fun i => c (OFF + l * J + (xh * 2 ^ R.h.ls + r)) i) u :=
    sum_congr rfl fun l hl => by rw [step l (mem_range.mp hl)]
  rw [s1]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r hr => ?_
  rw [hB xh r (mem_range.mp hr), ← ext_limbs, mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-! ## A segment's columns and its call's point -/

variable (ρ) in
/-- What is asked of a segment that is read by blocks: it has n entries, its columns are aligned on
blocks of 2^ls entries, its call's point has one coordinate for each bit of a column, and the last
ls of these are the coordinates low. -/
def SegFit (R : Model.Head.Run) (sn : String) (n : ℕ) (low : ℕ → K) : Prop :=
  ∃ q g, Model.Head.callNo R.L sn = some q ∧ (R.L.calls.getD q default).seg? sn = some g ∧
    g.n = n ∧ Aligned g R.h.ls (R.L.calls.getD q default).lJ ∧
    (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ ∧
    R.h.ls ≤ (R.L.calls.getD q default).lJ ∧
    ∀ j, j < R.h.ls →
      pt ρ (Model.Head.zjOf R.L R.x.g1 q) ((R.L.calls.getD q default).lJ - R.h.ls + j) = low j

/-- What is asked of a segment whose entries are read one by one: it has n entries, each with a
column. -/
def SegHas (R : Model.Head.Run) (sn : String) (n : ℕ) : Prop :=
  ∃ q g, Model.Head.callNo R.L sn = some q ∧ (R.L.calls.getD q default).seg? sn = some g ∧
    g.n = n ∧ g.pos.size = n

variable (ρ) in
/-- The position coordinates of the key point of the call with the segment sn are the point u. -/
def PosFit (R : Model.Head.Run) (sn : String) (u : ℕ → K) : Prop :=
  ∃ q, Model.Head.callNo R.L sn = some q ∧ (Model.Head.ztOf R.h R.L R.x.g1 q).size = R.h.lt ∧
    ∀ j, j < R.h.lt → pt ρ (Model.Head.ztOf R.h R.L R.x.g1 q) j = u j

/-- What cutting off the last k coordinates returns. -/
theorem cutLast_ok {z : Array E} {k : ℕ} {r : Array E × Array E}
    (h : Model.cutLast z k = .ok r) : k ≤ z.size ∧ r.1 = z.extract 0 (z.size - k) := by
  unfold Model.cutLast at h
  split at h
  · cases h
  · rename_i hk
    cases h
    exact ⟨Nat.le_of_not_lt hk, rfl⟩

/-- For a segment that fits, the weights of the entries and the weights of the blocks are one set of
weights, there are n of the first, and the blocks make up the n entries. -/
theorem SegFit.blocked {R : Model.Head.Run} {sn : String} {n : ℕ} {low : ℕ → K}
    (S : SegFit ρ R sn n low) {F G F' G' : Fork} {C D C' D' : Ctx} {ew wh : Array E}
    (h1 : Ok (Model.Head.ewOf R sn) F C ew G D) (h2 : Ok (Model.Head.ewh R sn) F' C' wh G' D') :
    ew.size = n ∧ wh.size * 2 ^ R.h.ls = n ∧ Blocked ρ ew wh R.h.ls low := by
  obtain ⟨q, g, hq, hg, hn, A, hz, hls, hlow⟩ := S
  obtain ⟨_, _, q1, g1, hq1, hg1, rfl⟩ := ok_ewOf h1
  obtain ⟨_, _, q2, g2, k, hq2, hg2, hk, rfl⟩ := ok_ewh h2
  rw [hq] at hq1 hq2
  obtain rfl := Option.some.inj hq1
  obtain rfl := Option.some.inj hq2
  rw [hg] at hg1 hg2
  obtain rfl := Option.some.inj hg1
  obtain rfl := Option.some.inj hg2
  obtain ⟨hk1, hk2⟩ := cutLast_ok hk
  obtain ⟨Q, hQ⟩ := A.whole
  have hpos : 0 < 2 ^ R.h.ls := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold Model.Layer.Env.ewFrom
    rw [Array.size_map, A.size, hn]
  · unfold Model.Layer.Env.ewhFrom
    rw [Array.size_map, Array.size_range, ← hn, hQ]
    show Q * 2 ^ R.h.ls / 2 ^ R.h.ls * 2 ^ R.h.ls = Q * 2 ^ R.h.ls
    rw [Nat.mul_div_cancel _ hpos]
  · have hzh : k.1.size = (R.L.calls.getD q default).lJ - R.h.ls := by
      rw [hk2, Array.size_extract, hz]
      omega
    have B := blocked_of_aligned ρ (Model.Head.zjOf R.L R.x.g1 q) k.1 hz hls hzh
      (fun j hj => by
        have a1 : j < (Model.Head.zjOf R.L R.x.g1 q).size := by rw [hz]; omega
        have a2 : j < (Model.Head.zjOf R.L R.x.g1 q).size - R.h.ls := by rw [hz]; exact hj
        rw [hk2]
        simp [Array.getD, Array.size_extract, a1, a2])
      g A
    intro xh r hr
    rw [B xh r hr]
    congr 1
    refine eqN_congr' _ _ (fun j hj => ?_) r
    rw [Nat.zero_add]
    exact hlow j hj

/-- A segment that fits has its entries. -/
theorem SegFit.has {R : Model.Head.Run} {sn : String} {n : ℕ} {low : ℕ → K}
    (S : SegFit ρ R sn n low) : SegHas R sn n := by
  obtain ⟨q, g, hq, hg, hn, A, _⟩ := S
  exact ⟨q, g, hq, hg, hn, by rw [A.size, hn]⟩

/-- A segment has as many weights as entries. -/
theorem SegHas.size {R : Model.Head.Run} {sn : String} {n : ℕ} (S : SegHas R sn n)
    {F G : Fork} {C D : Ctx} {ew : Array E} (h1 : Ok (Model.Head.ewOf R sn) F C ew G D) :
    ew.size = n := by
  obtain ⟨q, g, hq, hg, _, hp⟩ := S
  obtain ⟨_, _, q1, g1, hq1, hg1, rfl⟩ := ok_ewOf h1
  rw [hq] at hq1
  obtain rfl := Option.some.inj hq1
  rw [hg] at hg1
  obtain rfl := Option.some.inj hg1
  unfold Model.Layer.Env.ewFrom
  rw [Array.size_map, hp]

/-- The position coordinates of a segment's call, as the routine returns them. -/
theorem PosFit.zt {R : Model.Head.Run} {sn : String} {u : ℕ → K} (S : PosFit ρ R sn u)
    {F G : Fork} {C D : Ctx} {zt : Array E} (h : Ok (Model.Head.ztSeg R sn) F C zt G D) :
    G = F ∧ D = C ∧ zt.size = R.h.lt ∧ ∀ j, j < R.h.lt → pt ρ zt j = u j := by
  obtain ⟨q, hq, hs, hu⟩ := S
  unfold Model.Head.ztSeg at h
  rw [ok_bind] at h
  obtain ⟨q1, F1, C1, h1, h2⟩ := h
  rw [ok_lift, getAs_ok] at h1
  obtain ⟨⟨hq1, e1⟩, e2⟩ := h1
  rw [hq] at hq1
  obtain rfl := Option.some.inj hq1
  rw [ok_pure] at h2
  obtain ⟨rfl, e3, e4⟩ := h2
  exact ⟨e3.trans e2, e4.trans e1, hs, hu⟩

/-! ## Sums over the positions -/

/-- A weighted sum of a function of the position alone. -/
theorem wsum_pos (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) (f : ℕ → K) :
    wsum g lt u n (fun _ i => f i) = (∑ x ∈ range n, g x) * Blocks.ext lt f u := by
  unfold wsum
  rw [sum_mul]

/-- A fold that adds the members of an array at the numbers that a test picks. -/
theorem foldl_on (ρ : Reading K) (on : ℕ → Bool) (e : Array E) : ∀ n : ℕ,
    ρ.val ((List.range n).foldl
      (fun s t => if on t then addE s (e.getD t zeroE) else s) zeroE) =
      ∑ t ∈ range n, if on t then ρ.val (e.getD t zeroE) else 0
  | 0 => by simp [ρ.zero]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← foldl_on ρ on e n]
    split
    · rw [ρ.add]
    · rw [add_zero]

/-- The extension reads its point at the coordinates below g alone. -/
theorem ext_point {g : ℕ} (v : ℕ → K) {p p' : ℕ → K} (h : ∀ j, j < g → p j = p' j) :
    Blocks.ext g v p = Blocks.ext g v p' := by
  unfold Blocks.ext
  refine sum_congr rfl fun X _ => ?_
  have e : Blocks.eqN g 0 p X = Blocks.eqN g 0 p' X :=
    eqN_congr' g 0 (fun j hj => by rw [Nat.zero_add]; exact h j hj) X
  rw [e]

/-- The sum of the equality weights of the point P over the covered positions is the extension, at
P, of the indicator of the covered positions. -/
theorem onSum_value (ρ : Reading K) (R : Model.Head.Run) (P : Array E) (f : ℕ → K)
    (hP : P.size = R.h.lt)
    (hf : ∀ i, i < 2 ^ R.h.lt → f i = if R.cov.hOn.getD i false then 1 else 0) :
    ρ.val (Model.Head.onSum R P) = Blocks.ext R.h.lt f (pt ρ P) := by
  have e : Model.Head.onSum R P = (List.range (2 ^ R.h.lt)).foldl
      (fun s t => if R.cov.hOn.getD t false then addE s ((Model.eqTab P).getD t zeroE) else s)
      zeroE := rfl
  rw [e, foldl_on ρ (fun t => R.cov.hOn.getD t false)]
  unfold Blocks.ext
  refine sum_congr rfl fun X hX => ?_
  have hX' : X < 2 ^ P.size := by rw [hP]; exact mem_range.mp hX
  rw [hf X (mem_range.mp hX), eqTab_value ρ P X hX', hP]
  split
  · rw [mul_one]
  · rw [mul_zero]

/-- The sum of a segment's weights over the entries of the vocabulary. -/
theorem wxOf_value (ρ : Reading K) (R : Model.Head.Run) (ew : Array E) (h : R.h.V ≤ ew.size) :
    ρ.val (Model.Head.wxOf R ew) = ∑ x ∈ range R.h.V, ρ.val (ew.getD x zeroE) := by
  have e : Model.Head.wxOf R ew = Model.Layer.sumR ew 0 R.h.V := rfl
  rw [e, sumR_value ρ ew 0 R.h.V h, Nat.sub_zero]
  exact sum_congr rfl fun y _ => by rw [Nat.zero_add]

end Tools

/-! ## The layout's numbers -/

/-- What is asked of the public numbers of a run of the head's check, for the sizes z: the numbers
of positions, channels and vocabulary entries are z's, no column stands behind the vocabulary, and
the tensors of the matrix hf begin at the features of Johnson/Road/HeadSizes.lean, which at the
library's sizes are the library's. -/
structure Laid (R : Model.Head.Run) (z : Sizes) : Prop where
  T : z.T = 2 ^ R.h.lt
  d : R.h.d = z.d
  V : R.h.V = z.V
  JV : R.L.JV = z.V
  JVa : R.L.JVa = z.Va
  oAw : R.L.oAw = 0
  oRa : R.L.oRa = 2 * z.d
  oD1 : R.L.oD1 = 4 * z.d
  oD2 : R.L.oD2 = 4 * z.d + 2 * z.V
  oE : R.L.oE = 4 * z.d + 3 * z.V
  /-- a block's features divide the width and the vocabulary -/
  Sd : 2 ^ R.h.ls ∣ z.d
  SV : 2 ^ R.h.ls ∣ z.V

/-- The final normalisation's three numbers, as the library's record. -/
def npOf (h : Model.Head.Shape) : NormPar := ⟨h.MF, h.KF, (h.epsF : ℤ)⟩

/-- The request y, as the library's record, is the request of the run: the covered and the counted
positions are the run's, and at a covered position the checked token is the run's. -/
structure ReqFits (R : Model.Head.Run) (z : Sizes) (y : Inst.Model.Head.Req) : Prop where
  rho : ∀ i, i < z.T → y.rho i = if R.cov.hOn.getD i false then 1 else 0
  rhoC : ∀ i, i < z.T → HeadSizes.rhoC z y i = if R.cov.hOnC.getD i false then 1 else 0
  win : ∀ i, i < z.T → R.cov.hOn.getD i false = true → y.win i = R.x.win.getD i 0

section Families

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- The sum of an array's members reads as the sum of their readings. -/
theorem sumE_value' (ρ : Reading K) (v : Array E) :
    ρ.val (Model.sumE v) = ∑ x ∈ range v.size, ρ.val (v.getD x zeroE) :=
  sumE_value ρ v

/-- The program's 2^k reads as 2^k. -/
theorem pw_value (hρ : Numerals ρ) (k : ℕ) : ρ.val (Model.Head.pw k) = (2 : K) ^ k := by
  unfold Model.Head.pw
  rw [hρ.ofNat, Nat.cast_pow, Nat.cast_ofNat]

/-- The family NFH, the high key of the final normalisation's rounding. If the routine that builds
the segment's form succeeds, it leaves state and context, and in a world where the long table on hf
is true of the cells t at the point (low | u) the form is worth the sum, over the segment's entries
x, of the weight of x times the extension over the positions, at u, of the keys at x. -/
theorem line_NFH (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "NFH" z.d low) (h : Ok (Model.Head.LINE R "NFH") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "NFH") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.d
        (fun x i => HeadSizes.key z (npOf R.h) t H y .NFH x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.Sl R "NFH" R.L.oRa 2 R.h.d >>= fun s =>
      pure ((Aff.ofConst (mulE Model.Head.o2 (Model.sumE ew)) + s).scale
        (Model.Head.pw (32 - R.h.KF)))) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨s, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, wh, hwh, hs⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oRa, Z.d]
      exact Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 2) (Dvd.dvd.mul_left Z.Sd l)) h3
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  rw [Aff.value_scale, Aff.value_add, Aff.value_ofConst, hs ew b3, b2, ρ.mul, sumE_value', b1,
    pw_value hρ]
  have e : (fun x i => HeadSizes.key z (npOf R.h) t H y .NFH x i) = fun x i =>
      (2 : K) ^ (32 - R.h.KF) * ((32896 : K) +
        ∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oRa + l * R.h.d + x) i) := by
    funext x i
    show ((2 ^ (32 - R.h.KF) : ℕ) : K) * ((32896 : K) +
      ∑ l ∈ range 2, (256 : K) ^ l * t.hf (2 * z.d + z.d * l + x) i) = _
    rw [Z.oRa, Z.d, Nat.cast_pow, Nat.cast_ofNat]
    simp only [Nat.mul_comm]
  rw [e, wsum_smul, wsum_add, wsum_const]
  have o : ρ.val Model.Head.o2 = (32896 : K) := by
    unfold Model.Head.o2
    rw [hρ.ofNat, Nat.cast_ofNat]
  rw [o]
  ring

/-- The offset of two cells reads as 32,896; that of one cell as 128. -/
theorem o2_value (hρ : Numerals ρ) : ρ.val Model.Head.o2 = (32896 : K) := by
  unfold Model.Head.o2
  rw [hρ.ofNat, Nat.cast_ofNat]
theorem o1_value (hρ : Numerals ρ) : ρ.val Model.Head.o1 = (128 : K) := by
  unfold Model.Head.o1
  rw [hρ.ofNat, Nat.cast_ofNat]

/-- The indicator of the covered positions, read in K. -/
theorem ReqFits.rhoK {R : Model.Head.Run} {z : Sizes} {y : Inst.Model.Head.Req}
    (Y : ReqFits R z y) (Z : Laid R z) (i : ℕ) (hi : i < 2 ^ R.h.lt) :
    ((y.rho i : ℤ) : K) = if R.cov.hOn.getD i false then 1 else 0 := by
  rw [Y.rho i (by rw [Z.T]; exact hi)]
  split <;> simp

/-- The family HD1, the middle digit of a margin. If the routine that builds the segment's form
succeeds, it leaves state and context, and in a world where the long table on hf is true of the
cells t at the point (low | u), u being the position coordinates of the call's key point, the form
is worth the sum, over the segment's entries x, of the weight of x times the extension over the
positions, at u, of the keys at x. -/
theorem line_HD1 (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} (Z : Laid R z)
    {F G : Fork} {C D : Ctx} {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req} (Y : ReqFits R z y)
    (hL : LongAt W R (colsOf F R.iU3) "hf@Z" R.h.ls R.h.lt low u t.hf)
    (S : SegFit ρ R "HD1" z.V low) (U : PosFit ρ R "HD1" u)
    (h : Ok (Model.Head.LINE R "HD1") F C a G D) :
    G = F ∧ D = C ∧ ∃ ew, Ok (Model.Head.ewOf R "HD1") F C ew F C ∧
      a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u z.V
        (fun x i => HeadSizes.key z (npOf R.h) t H y .HD1 x i) := by
  unfold Model.Head.LINE at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨ew, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewOf h1
  replace h2 : Ok (Model.Head.ztSeg R "HD1" >>= fun zt =>
      Model.Head.middleDigit R "HD1"
        (mulE (Model.Head.wxOf R ew) (Model.Head.onSum R zt))) F1 C1 a G D := h2
  rw [ok_bind] at h2
  obtain ⟨zt, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, hzs, hzu⟩ := U.zt h3
  unfold Model.Head.middleDigit at h4
  rw [ok_bind] at h4
  obtain ⟨s, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, wh, hwh, hs⟩ := Sl_cells hρ hL
    (fun l _ => by
      rw [Z.oD1, Z.JV]
      exact Nat.dvd_add (Dvd.dvd.mul_left Z.Sd 4) (Dvd.dvd.mul_left Z.SV l)) h5
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  obtain ⟨b1, b2, b3⟩ := S.blocked h1 hwh
  refine ⟨rfl, rfl, ew, h1, ?_⟩
  rw [Aff.value_add, Aff.value_ofConst, hs ew b3, b2, ρ.mul, ρ.mul, o2_value hρ,
    wxOf_value ρ R ew (by rw [b1, Z.V]), Z.V,
    onSum_value ρ R zt (fun i => ((y.rho i : ℤ) : K)) hzs (Y.rhoK Z), ext_point _ hzu]
  have e : (fun x i => HeadSizes.key z (npOf R.h) t H y .HD1 x i) = fun x i =>
      (∑ l ∈ range 2, (256 : K) ^ l * t.hf (R.L.oD1 + l * R.L.JV + x) i) +
        (32896 : K) * ((y.rho i : ℤ) : K) := by
    funext x i
    show (∑ l ∈ range 2, (256 : K) ^ l * t.hf (4 * z.d + z.V * l + x) i) +
      (32896 : K) * ((y.rho i : ℤ) : K) = _
    rw [Z.oD1, Z.JV]
    simp only [Nat.mul_comm]
  rw [e, wsum_add, wsum_pos, Blocks.ext_smul]
  ring

end Families

#print axioms Sl_cells
#print axioms SegFit.blocked
#print axioms line_NFH
#print axioms line_HD1
#print axioms onSum_value

end OnBytes.Road.Hd
