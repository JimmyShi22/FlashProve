-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrapRef.lean: the normalisations, the projections and the first residual addition
  in the form of `Part1` and `Part2` (Inst/Model/FF/Trace.lean), and the size conditions at the
  reference parameters.

    `p1_aw` .. `p1_bound`
                         one theorem for each of the fields aw, a, qkw, q, kx, vw, v, att, n2, mw,
                         m, led, bound of `Part1`, under `IntRel` and `AdmN`, and for qkw, q, kx,
                         vw, v, att also `AdmP`, for a layer l < D.nl
    `part2_of`           `Part2`, under `IntRel`, `AdmN`, `AdmS`, (FA12), for a layer l < D.nl
    `wf_layer_ref`, `admP_ref`, `admS_ref`
                         from `Spec.Setting`: the weights that the layout reads for a layer L <
                         `ppref.layers` are well formed (from the field `wf`), and the size
                         conditions hold at p = 2^61 − 1, at the reference sizes, for valid scales
  `IntRel`: Inst/Model/FF/NoWrap0.lean; `AdmN`: Inst/Model/FF/NoWrapNorm.lean; `AdmP`:
  Inst/Model/FF/NoWrapProj.lean; `AdmS`: Inst/Model/FF/NoWrapStream.lean; (FA12): `OBound`,
  Inst/Model/FF/Trace.lean.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). "the
  reference parameters": the sizes `Dim.ref`, with any scales (valid ones under `[Lawful]`,
  Inst/Model/FF/Lawful.lean). A theorem marked "omit scl in" reads no scale.

  Notation: `D`: a `Dim`: the sizes of a feed-forward segment; aw, a, mw, m, qkw, ..: arrays (`Arr`)
  (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table functions that the program reads;
  `w l`: a `LayerW`: the weight matrices of one layer; `Att.aw`, `Att.a`, .., `FF.mw`, `FF.m`,
  `NORM.V`, `sig`, `R`: the integer program's values of these names (Inst/Model/Program.lean); `L0`:
  a natural number: the first layer of the segment; `t`: a map `Cell` → ℤ: a trace, a function on
  the names of cells; `val t X inst j i`: the read-out formula, at an array, an instance, a channel
  j and a position i; `stream D t s`, `xS D t s j i`: state s of the stream, x_s[j] at position i;
  `npOf D ν`: the parameters of the norm instance ν = 2ℓ + n; `led t ν i`: the bytes of the ledger
  of the norm instance ν at position i, as values; `Part1 .. l`: a `Prop`: what the relation gives
  without a fact from another segment, for layer ℓ; its field `led`: the intermediate values of both
  normalisations; `Part2 .. l`: a `Prop`: (PL7): x_(2ℓ+1) is the value that the output projection
  computes from x_(2ℓ) and o (Inst/Model/FF/Trace.lean); `IntRel ..`: a `Prop`: the field relation
  over `ZMod p`, restated over the integers (Inst/Model/FF/NoWrap0.lean); `Ledger.Vlo`, `Vhi`: bytes
  0..5; 6..9: V = Vlo + 2^48 Vhi (Inst/Model/Common/Ledger.lean).
-/
import Inst.Model.FF.NoWrapStream

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset

section Fields
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {p : ℤ} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ} (h : IntRel D tb L0 first p w emb tok t) (admN : AdmN p D)
include h admN

theorem p1_aw {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ j < D.d, val t .aw l j i = Att.aw (D.Pl l) (stream D t (2 * l)) i j :=
  fun _ hi j hj => (norm1_at h admN hl hi).2.1 j hj

theorem p1_a {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ j < D.d, val t .a l j i = Att.a (D.Pl l) (stream D t (2 * l)) i j :=
  fun _ hi j hj => (norm1_at h admN hl hi).2.2.1 j hj

theorem p1_n2 {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, NORM.OK (D.Pl l).n2 D.d (stream D t (2 * l + 1) i) :=
  fun _ hi => (norm2_at h admN hl hi).1

theorem p1_mw {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ j < D.d, val t .mw l j i = FF.mw (D.Pl l) (stream D t (2 * l + 1)) i j :=
  fun _ hi j hj => (norm2_at h admN hl hi).2.1 j hj

theorem p1_m {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ j < D.d, val t .m l j i = FF.m (D.Pl l) (stream D t (2 * l + 1)) i j :=
  fun _ hi j hj => (norm2_at h admN hl hi).2.2.1 j hj

theorem p1_led {l : ℕ} (hl : l < D.nl) :
    ∀ n < 2, ∀ i < D.T,
      Ledger.Vlo (led t (2 * l + n) i) + 2 ^ 48 * Ledger.Vhi (led t (2 * l + n) i) =
        NORM.V D.d (stream D t (2 * l + n) i) ∧
      Ledger.sig (led t (2 * l + n) i) =
        NORM.sig (npOf D (2 * l + n)) D.d (stream D t (2 * l + n) i) ∧
      Ledger.R (led t (2 * l + n) i) =
        NORM.R (npOf D (2 * l + n)) D.d (stream D t (2 * l + n) i) := fun n hn _ hi => by
  obtain ⟨a1, a2, a3, -⟩ :=
    ledger_at h admN (ν := 2 * l + n) (show 2 * l + n < 2 * D.nl by omega) hi
  exact ⟨a1, a2, a3⟩

theorem p1_bound {l : ℕ} (hl : l < D.nl) :
    ∀ n < 2, ∀ i < D.T, ∀ j < D.d, |xS D t (2 * l + n) j i| < 2 ^ 39 := fun n hn _ hi j hj =>
  (ledger_at h admN (ν := 2 * l + n) (show 2 * l + n < 2 * D.nl by omega) hi).2.2.2.2.1 j hj

variable (admP : AdmP p D tb L0 w)
include admP

theorem p1_qkw {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T,
      ∀ c < D.dqk, val t .qkw l c i = Att.qkw (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c :=
  fun i hi _ hc => (qk_at h admP hl hi (p1_a h admN hl i hi) hc).1

theorem p1_q {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ c < D.dq, val t .q l c i =
      Att.q (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c := fun i hi c hc => by
  obtain ⟨r1, -, r3, -⟩ :=
    qk_at h admP hl hi (p1_a h admN hl i hi) (c := c) (by unfold Dim.dqk; omega)
  rw [if_pos hc, r1] at r3
  exact r3

theorem p1_kx {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ c < D.dkv, val t .kx l c i =
      Att.kx (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) i c := fun i hi c hc => by
  obtain ⟨r1, -, r3, -⟩ :=
    qk_at h admP hl hi (p1_a h admN hl i hi) (c := D.dq + c) (by unfold Dim.dqk; omega)
  rw [if_neg (by omega), r1, Nat.add_sub_cancel_left] at r3
  exact r3

theorem p1_vw {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ c < D.dkv, val t .vw l c i = Att.vw (D.Pl l) (w l) (stream D t (2 * l)) i c :=
  fun i hi _ hc => (v_at h admP hl hi (p1_a h admN hl i hi) hc).1

theorem p1_v {l : ℕ} (hl : l < D.nl) :
    ∀ i < D.T, ∀ c < D.dkv,
      val t .v l c i = Att.v (D.Pl l) (w l) (stream D t (2 * l)) i c := fun i hi c hc => by
  obtain ⟨r1, -, r3, -⟩ := v_at h admP hl hi (p1_a h admN hl i hi) hc
  rw [r1] at r3
  exact r3

/-- (PL2), (PL5): under `IntRel`, `AdmN`, `AdmP`, `hl`, no range condition fails. -/
theorem p1_att {l : ℕ} (hl : l < D.nl) :
    Att.OK (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l)) := fun i hi' => by
  have hi : i < D.T := by rw [admP.T]; exact hi'
  refine ⟨(norm1_at h admN hl hi).1, fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨r1, r2, -⟩ := qk_at h admP hl hi (p1_a h admN hl i hi) (c := c) hc
    rw [← r1]
    exact r2
  · obtain ⟨r1, r2, -⟩ := v_at h admP hl hi (p1_a h admN hl i hi) (c := c) hc
    rw [← r1]
    exact r2

end Fields

/-- `Part2`, under `IntRel`, `AdmN`, `AdmS` and (FA12) (`OBound`). (not all hypotheses are named
here: see the statement below) -/
theorem part2_of {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {p : ℤ} {w : ℕ → LayerW}
    {emb : Mat} {tok : ℕ → ℕ} {t : Cell → ℤ} (h : IntRel D tb L0 first p w emb tok t)
    (admN : AdmN p D) (admS : AdmS p D L0 w) (ho : OBound D t) {l : ℕ} (hl : l < D.nl) :
    Part2 D w t l :=
  fun i hi _ hc => (pl7_at h admN admS hl hi (fun j hj => ho l hl i hi j hj) hc).1

/-! ## The reference parameters -/

omit scl in
theorem wf_layer_ref {W : Mat} (hW : Layout.WFW ppref Layout.kRef W Layout.hRef)
    {L : ℕ} (hL : L < ppref.layers) :
    (Layout.layerOf ppref Layout.kRef W L).WF ppref L := by
  have h := (Layout.Bridge.indexOf W hW).2.1 L
  rw [if_pos hL] at h
  have eL : (Layout.weightsOf ppref Layout.kRef W).layer L = Layout.layerOf ppref Layout.kRef W L :=
    if_pos hL
  rw [← eL]
  exact h

theorem admP_ref [Lawful] {tb : Tables} {W : Mat} {L0 : ℕ}
    {tok : ℕ → ℕ} (S : Spec.Setting tb W L0 tok) :
    AdmP (2 ^ 61 - 1) Dim.ref tb L0 fun l => Layout.layerOf ppref Layout.kRef W (L0 + l) where
  big := by norm_num
  kq := fun l => (Lawful.all l).rq.2
  kk := fun l => (Lawful.all l).rk.2
  kv := fun l => (Lawful.all l).rv.2
  wq := fun l => Scales.wq_int (Lawful.all l).ranges.kq.1 (Lawful.all l).ranges.kq.2
  wk := fun l => Scales.wq_int (Lawful.all l).ranges.kk.1 (Lawful.all l).ranges.kk.2
  wv := fun l => Scales.wv_int (Lawful.all l).rv.2
  even := by decide
  T := by decide
  layers := S.layers
  tab := S.tab
  wf := fun l hl => wf_layer_ref S.wf (by have := S.layers; omega)

theorem admS_ref [Lawful] {tb : Tables} {W : Mat} {L0 : ℕ}
    {tok : ℕ → ℕ} (S : Spec.Setting tb W L0 tok) :
    AdmS (2 ^ 61 - 1) Dim.ref L0 fun l => Layout.layerOf ppref Layout.kRef W (L0 + l) where
  ko := fun l => (Lawful.all l).ro.2
  kd := fun l => (Lawful.all l).rd.2
  hi := by norm_num
  o := fun l => Scales.wo_int (Lawful.all l).ranges.ko.2
  d := fun l => Scales.wd_int (Lawful.all l).ranges.kd.1 (Lawful.all l).ranges.kd.2
  even := S.even
  f := by decide
  nexp := by decide
  wf := fun l hl => wf_layer_ref S.wf (by have := S.layers; omega)

end Inst.Model.FFSeg
