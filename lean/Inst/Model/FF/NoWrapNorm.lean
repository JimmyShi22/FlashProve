-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrapNorm.lean: the two normalisations of a layer: from the field relation to the
  steps (N1) to (N5) of the integer program (Inst/Model/Program.lean).

  The file treats the families of looked-up values (keys in Lean names) ROW, N1H, N2H and CN1, CN2,
  the ledger (the bytes of a normalisation's intermediate values), and the rounding sites N1, N2;
  facts (FL1), (FL7) to (FL9), (FL13) to (FL18). `Part1` (Inst/Model/FF/Trace.lean) takes its fields
  on the two normalisations from them. `ledger_at`, `norm1_at`, `norm2_at` are under `IntRel`
  (Inst/Model/FF/NoWrap0.lean: the field relation over `ZMod p`, restated over the integers) and
  `AdmN`.
    `AdmN p D`           the size conditions
    `stream_cells`, `xS_eq_xOf`
                         the stream at an index has five cells for each value and no offset
    `ledger_at`          the ledger of the norm instance ν at position i holds V, ς, R of the
                         program on the stream at the index ν; V + ϵ < 2^78; |x[j]| < 2^39; |x[j] R|
                         < 2^M + 2^38
    `norm1_at`, `norm2_at`
                         the arrays aw, a, ra and mw, m, rm hold `NORM.yw`, `NORM.out` and the high
                         digit, and `NORM.OK` holds
  The arithmetic of the ledger is that of Inst/Model/Common/LedgerSound.lean, that of a rounding
  that of Inst/Model/Common/Site.lean. The sizes D are not fixed: except for `admN_ref`, the
  statements hold for all sizes that meet their hypotheses, among them `AdmN`. Labels such as (FL7)
  and "Step L1" link one docstring to another; (FL18) and "Step L6" occur in no other file of Inst/.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: `D`: a `Dim`: the sizes of a feed-forward segment; the stream: the array xs holds it at
  the indices 1, .., 2 nl − 1; x0 and x8 hold it at the first and the last index (`Arr`); `D.nNu`:
  norm instances ν = 2ℓ + n; `nLedger` (99): the number of bytes of the ledger of a norm instance at
  a position (Inst/Model/FF/Index.lean); `X.off` (Inst/Model/FF/Index.lean): the offset in the
  formula of `val`; ℓ: the number of a layer in the segment (`l` in `norm1_at`, `norm2_at`); `t`: a
  map `Cell` → ℤ: a trace, a function on the names of cells; `stream D t s`, `xS D t s j i`: state s
  of the stream, x_s[j] at position i; `npOf D ν`: the parameters of the norm instance ν = 2ℓ + n:
  the first normalisation of a layer for n = 0, the second for n = 1; `led t ν i`: the bytes of the
  ledger of the norm instance ν at position i, as values; `val t X inst j i`: the read-out formula,
  at an array, an instance, a channel j and a position i (Inst/Model/FF/Trace.lean); `Ledger.Vlo`,
  `Vhi`: "bytes 0..5; 6..9: V = Vlo + 2^48 Vhi" (their doc comment); `Ledger.mu n`: the multiplier
  µ_n of byte n in the keys of the family ROW; `Ledger.idn`: the 17 identities
  (Inst/Model/Common/Ledger.lean).
-/
import Inst.Model.FF.NoWrap0

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset
open Inst.Model.TableKeys (InLut)

/-- The size conditions for the normalisations of a segment. -/
structure AdmN (p : ℤ) (D : Dim) : Prop where
  big : 2 ^ 60 ≤ p
  led1 : ∀ l, Ledger.Adm p (D.Pl l).n1 D.d (2 ^ 18)
  led2 : ∀ l, Ledger.Adm p (D.Pl l).n2 D.d (2 ^ 18)
  ok1 : ∀ l, (D.Pl l).n1.OK
  ok2 : ∀ l, (D.Pl l).n2.OK

theorem AdmN.led {p : ℤ} {D : Dim} (a : AdmN p D) (ν : ℕ) :
    Ledger.Adm p (npOf D ν) D.d (2 ^ 18) := by
  unfold npOf
  split_ifs
  · exact (a.led1 _)
  · exact (a.led2 _)

/-! ## The stream -/

omit scl in
/-- the stream at an index s ≤ 2 nl: five cells, no offset, width d, and its instance exists -/
theorem stream_cells (D : Dim) {s : ℕ} (hs : s ≤ 2 * D.nl) :
    (streamAt D s).1.nCell = 5 ∧
    (streamAt D s).1.off = 0 ∧
    (streamAt D s).1.width D = D.d ∧
    (streamAt D s).2 < (streamAt D s).1.cnt D := by
  unfold streamAt
  split_ifs with h0 h8
  · exact ⟨rfl, rfl, rfl, Nat.one_pos⟩
  · exact ⟨rfl, rfl, rfl, Nat.one_pos⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    show s - 1 < 2 * D.nl - 1
    omega

omit scl in
theorem xS_eq_xOf (D : Dim) (t : Cell → ℤ) {s : ℕ} (hs : s ≤ 2 * D.nl) (j i : ℕ) :
    xS D t s j i = Ledger.xOf (fun l j => bS D t s l j i) j := by
  obtain ⟨h1, h2, -, -⟩ := stream_cells D hs
  unfold xS val Ledger.xOf bS
  rw [h1, h2]
  simp

omit scl in
theorem stream_eq_xOf (D : Dim) (t : Cell → ℤ) {s : ℕ} (hs : s ≤ 2 * D.nl) (i : ℕ) :
    stream D t s i = Ledger.xOf fun l j => bS D t s l j i :=
  funext fun j => xS_eq_xOf D t hs j i

section Rel
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {p : ℤ} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}

/-- The ledger of a norm instance ν < 2 nl at a position i < T (Steps L1, L4, L5): (FL13) to (FL17),
except 1 ≤ ς < 2^39, under `IntRel` and `AdmN`. -/
theorem ledger_at (h : IntRel D tb L0 first p w emb tok t) (adm : AdmN p D) {ν i : ℕ}
    (hν : ν < D.nNu) (hi : i < D.T) :
    Ledger.Vlo (led t ν i) + 2 ^ 48 * Ledger.Vhi (led t ν i) = NORM.V D.d (stream D t ν i) ∧
    Ledger.sig (led t ν i) = NORM.sig (npOf D ν) D.d (stream D t ν i) ∧
    Ledger.R (led t ν i) = NORM.R (npOf D ν) D.d (stream D t ν i) ∧
    NORM.V D.d (stream D t ν i) + (npOf D ν).eps < 2 ^ 78 ∧
    (∀ j < D.d, |xS D t ν j i| < 2 ^ 39) ∧
    ∀ j < D.d, |xS D t ν j i * Ledger.R (led t ν i)| < 2 ^ (npOf D ν).M + 2 ^ 38 := by
  have hν' : ν < 2 * D.nl := hν
  have hs : ν ≤ 2 * D.nl := hν'.le
  obtain ⟨c1, -, c3, c4⟩ := stream_cells D hs
  have hb : ∀ l < 5, ∀ j < D.d, |bS D t ν l j i| ≤ 2 ^ 18 := fun l hl j hj =>
    (h.small ⟨(streamAt D ν).1, l, (streamAt D ν).2, j, i⟩
      ⟨by rw [c1]; exact hl, c4, by rw [c3]; exact hj, hi⟩).le
  have hD : ∀ n < 99, |led t ν i n - 128| ≤ 2 ^ 18 := fun n hn =>
    val1 h.small .D rfl (a := ν) (j := n) hν hn hi
  have hk : ∀ n < 99,
      ∃ u : ℤ, 0 ≤ u ∧ u < 256 ∧ Ledger.mu n * led t ν i n ≡ u [ZMOD p] := fun n hn => by
    have hkey := h.key .ROW (ν / 2) (ν % 2 * 99 + n) i (by omega) rfl (by show _ < 2 * 99; omega) hi
    have e1 : (ν % 2 * 99 + n) % nLedger = n := by show _ % 99 = n; omega
    have e2 : 2 * (ν / 2) + (ν % 2 * 99 + n) / nLedger = ν := by show _ + _ / 99 = ν; omega
    have e : key D t tb L0 (fun l => LW.ofInt ℤ (w l)) .ROW (ν / 2) (ν % 2 * 99 + n) i =
        Ledger.mu n * led t ν i n := by
      show ((Ledger.mu ((ν % 2 * 99 + n) % nLedger) : ℤ) : ℤ) *
          led t (2 * (ν / 2) + (ν % 2 * 99 + n) / nLedger) i ((ν % 2 * 99 + n) % nLedger) = _
      rw [e1, e2]
    rw [e] at hkey
    exact TableKeys.InLut.r8 hkey
  have hi17 : ∀ k < 17,
      Ledger.idn (npOf D ν) (Ledger.Wsum D.d fun l j => bS D t ν l j i) (led t ν i) k ≡
        0 [ZMOD p] := fun k hk' =>
    h.idn (.jn k ν i) ⟨hk', hν, hi⟩
  obtain ⟨-, a1, a2, a3, a4, -, -, a7, a8⟩ := Ledger.ledger_sound (adm.led ν) hb hD hk hi17
  rw [← stream_eq_xOf D t hs i] at a1 a2 a3 a4
  refine ⟨a1, a2, a3, a4, fun j hj => ?_, fun j hj => ?_⟩
  · rw [xS_eq_xOf D t hs]
    exact a7 j hj
  · rw [xS_eq_xOf D t hs]
    exact a8 j hj

end Rel

/-! ## A lemma on numbers: (N4), (N5) -/

omit scl in
/-- Step L6 with the Steps L1 and L2 for its digit and its clamp: the low key, the high key (a digit
of two cells with the offset 32,896) and the key of the clamp. -/
theorem norm_site {p : ℤ} {np : NormPar} (ok : np.OK) (big : 2 ^ 60 ≤ p) {A yw y rh : ℤ}
    (hA : |A| < 2 ^ np.M + 2 ^ 38) (hyw : |yw| ≤ 257 * 2 ^ 18) (hy : |y| ≤ 257 * 2 ^ 18)
    (hR : |rh - 32896| ≤ 257 * 2 ^ 18) (kL : InLut p R16 (Site.site A yw rh np.K))
    (kH : InLut p R16 (Site.high rh np.K 32))
    (kC : InLut p FC ((yw + 2 ^ 15) + 2 ^ 28 * (y + 2 ^ 11))) :
    yw = rhu A np.K ∧ Fits16 yw ∧ y = clamp 2047 yw ∧ rh = Site.hd A np.K := by
  obtain ⟨-, -, -, hM, hK17, hK32, -⟩ := ok
  have m1 : (2 : ℤ) ^ np.M ≤ 2 ^ 47 := pow_le_pow_right₀ (by norm_num) hM
  have k1 : (2 : ℤ) ^ (np.K - 1) ≤ 2 ^ 31 := pow_le_pow_right₀ (by norm_num) (by omega)
  have k2 : (2 : ℤ) ^ np.K ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) hK32
  have k3 : (2 : ℤ) ^ (32 - np.K) ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hR' : |rh| ≤ 257 * 2 ^ 18 + 32896 := by
    have := abs_le.mp hR
    rw [abs_le]
    constructor <;> linarith
  refine clamp_site (top := 32) (w := 16) (Ab := 2 ^ 47 + 2 ^ 38) (B2 := 257 * 2 ^ 18)
    (Rb := 257 * 2 ^ 18 + 32896) rfl (by omega) hK32 (by linarith) hyw hy hR' (by linarith)
    (by norm_num) ?_ ?_ kL kH.r16 kC
  · nlinarith
  · nlinarith

section Rel2
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {p : ℤ} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}

theorem npOf_even (D : Dim) (l : ℕ) : npOf D (2 * l) = (D.Pl l).n1 := by
  unfold npOf
  rw [if_pos (by omega), show 2 * l / 2 = l by omega]

theorem npOf_odd (D : Dim) (l : ℕ) : npOf D (2 * l + 1) = (D.Pl l).n2 := by
  unfold npOf
  rw [if_neg (by omega), show (2 * l + 1) / 2 = l by omega]

/-- The first normalisation of layer ℓ < nl at position i < T: (PL2), under `IntRel` and `AdmN`. -/
theorem norm1_at (h : IntRel D tb L0 first p w emb tok t) (adm : AdmN p D) {l i : ℕ}
    (hl : l < D.nl) (hi : i < D.T) :
    NORM.OK (D.Pl l).n1 D.d (stream D t (2 * l) i) ∧
    (∀ j < D.d, val t .aw l j i = NORM.yw (D.Pl l).n1 D.d (stream D t (2 * l) i) j) ∧
    (∀ j < D.d, val t .a l j i = NORM.out (D.Pl l).n1 D.d (stream D t (2 * l) i) j) ∧
    ∀ j < D.d, val t .ra l j i =
      Site.hd (stream D t (2 * l) i j * NORM.R (D.Pl l).n1 D.d (stream D t (2 * l) i))
        (D.Pl l).n1.K := by
  obtain ⟨-, -, a3, a4, -, a6⟩ := ledger_at h adm (ν := 2 * l) (show 2 * l < 2 * D.nl by omega) hi
  rw [npOf_even] at a3 a4 a6
  have key : ∀ j < D.d,
      val t .aw l j i = rhu (xS D t (2 * l) j i * Ledger.R (led t (2 * l) i)) (D.Pl l).n1.K ∧
      Fits16 (val t .aw l j i) ∧
      val t .a l j i = clamp 2047 (val t .aw l j i) ∧
      val t .ra l j i =
        Site.hd (xS D t (2 * l) j i * Ledger.R (led t (2 * l) i)) (D.Pl l).n1.K := fun j hj =>
    norm_site (adm.ok1 _) adm.big (a6 j hj) (val2z h.small .aw rfl rfl (a := l) (j := j) hl hj hi)
      (val2z h.small .a rfl rfl (a := l) (j := j) hl hj hi)
      (val2 h.small .ra rfl (a := l) (j := j) hl hj hi) (h.key .N1 l j i hl rfl hj hi)
      (h.key .N1H l j i hl rfl hj hi) (h.key .CN1 l j i hl rfl hj hi)
  have eyw : ∀ j < D.d,
      val t .aw l j i = NORM.yw (D.Pl l).n1 D.d (stream D t (2 * l) i) j := fun j hj => by
    rw [(key j hj).1, a3]
    rfl
  refine ⟨⟨a4, fun j hj => ?_⟩, eyw, fun j hj => ?_, fun j hj => ?_⟩
  · rw [← eyw j hj]
    exact (key j hj).2.1
  · rw [(key j hj).2.2.1, eyw j hj]
    rfl
  · rw [(key j hj).2.2.2, a3]
    rfl

/-- The second normalisation of layer ℓ < nl at position i < T: (PL8), under `IntRel` and `AdmN`. -/
theorem norm2_at (h : IntRel D tb L0 first p w emb tok t) (adm : AdmN p D) {l i : ℕ}
    (hl : l < D.nl) (hi : i < D.T) :
    NORM.OK (D.Pl l).n2 D.d (stream D t (2 * l + 1) i) ∧
    (∀ j < D.d, val t .mw l j i = NORM.yw (D.Pl l).n2 D.d (stream D t (2 * l + 1) i) j) ∧
    (∀ j < D.d, val t .m l j i = NORM.out (D.Pl l).n2 D.d (stream D t (2 * l + 1) i) j) ∧
    ∀ j < D.d, val t .rm l j i =
      Site.hd (stream D t (2 * l + 1) i j * NORM.R (D.Pl l).n2 D.d (stream D t (2 * l + 1) i))
        (D.Pl l).n2.K := by
  obtain ⟨-, -, a3, a4, -, a6⟩ :=
    ledger_at h adm (ν := 2 * l + 1) (show 2 * l + 1 < 2 * D.nl by omega) hi
  rw [npOf_odd] at a3 a4 a6
  have key : ∀ j < D.d,
      val t .mw l j i =
        rhu (xS D t (2 * l + 1) j i * Ledger.R (led t (2 * l + 1) i)) (D.Pl l).n2.K ∧
      Fits16 (val t .mw l j i) ∧
      val t .m l j i = clamp 2047 (val t .mw l j i) ∧
      val t .rm l j i =
        Site.hd (xS D t (2 * l + 1) j i * Ledger.R (led t (2 * l + 1) i))
          (D.Pl l).n2.K := fun j hj =>
    norm_site (adm.ok2 _) adm.big (a6 j hj) (val2z h.small .mw rfl rfl (a := l) (j := j) hl hj hi)
      (val2z h.small .m rfl rfl (a := l) (j := j) hl hj hi)
      (val2 h.small .rm rfl (a := l) (j := j) hl hj hi) (h.key .N2 l j i hl rfl hj hi)
      (h.key .N2H l j i hl rfl hj hi) (h.key .CN2 l j i hl rfl hj hi)
  have eyw : ∀ j < D.d,
      val t .mw l j i = NORM.yw (D.Pl l).n2 D.d (stream D t (2 * l + 1) i) j := fun j hj => by
    rw [(key j hj).1, a3]
    rfl
  refine ⟨⟨a4, fun j hj => ?_⟩, eyw, fun j hj => ?_, fun j hj => ?_⟩
  · rw [← eyw j hj]
    exact (key j hj).2.1
  · rw [(key j hj).2.2.1, eyw j hj]
    rfl
  · rw [(key j hj).2.2.2, a3]
    rfl

end Rel2

/-- At the reference sizes (`Dim.ref`), for valid scales and p = 2^61 − 1, the size conditions
hold. -/
theorem admN_ref [Lawful] : AdmN (2 ^ 61 - 1) Dim.ref :=
  ⟨by norm_num,
    fun l => Scales.led_K (Lawful.all l).n1,
    fun l => Scales.led_K (Lawful.all l).n2,
    fun l => (Lawful.all l).n1,
    fun l => (Lawful.all l).n2⟩

end Inst.Model.FFSeg
