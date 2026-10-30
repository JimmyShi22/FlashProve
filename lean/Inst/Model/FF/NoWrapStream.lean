-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrapStream.lean: the two residual additions of a layer: from the field relation to
  the steps (PL7), (PL12) and (PL13) of the integer program (Inst/Model/Program.lean).

  The file treats the families of looked-up values (keys in Lean names) OH, DH and the rounding
  sites O and D, and bounds the accumulators. The quotient of such a rounding has no cells: it is
  the difference of the stream at two indices, and its bound comes from the bounds |x| < 2^39 on the
  stream there. At an index that a normalisation of the segment reads, the stream has this bound
  from the ledger (FL14). At the last index it has it from the next segment (FL19), which is a
  hypothesis here. |o| ≤ 2,047 is a fact of the attention segment (FA12), also a hypothesis here.
    `AdmS p D L0 w`      the size conditions and the ranges of the weights
    `resid_site`         a lemma on numbers, for one residual addition
    `pl7_at`             (PL7)
    `Ad_eq`, `abs_Ad_le` (PL12): the accumulator of the trace is the program's, once sl, up and sel
                         hold the program's values; its bound
    `pl13_at`            (PL13)
  The sizes D are not fixed: the statements hold for all sizes that meet `AdmN` and `AdmS`, and for
  every shift up to 24 that meets the no-overflow conditions `o` and `d` of `AdmS` (the keys are
  those of Inst/Model/Common/Site.lean, Sections 5 to 8). Labels such as (PL7) link one docstring to
  another.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: `D`: a `Dim`: the sizes of a feed-forward segment; the ledger holds the intermediate
  values of a normalisation (`nLedger`) (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table
  functions that the program reads; `w l`: a `LayerW`: the weight matrices of one layer; `rhu a k`:
  ⌊(a + 2^(k−1)) / 2^k⌋, k ≥ 1 (Inst/Model/Program.lean); `L0`: a natural number: the first layer of
  the segment; `t`: a map `Cell` → ℤ: a trace, a function on the names of cells; `stream D t s`,
  `xS D t s j i`: state s of the stream, x_s[j] at position i (Inst/Model/FF/Trace.lean); `site`,
  `high` (for every shift: `ssite`, `shigh`): the low and the high key of a rounding; `hd A k`:
  ⌊rem(A, k) / 2^16⌋, the high digit; `up k`: max(k, 16); `dn k`: max(0, 16 − k)
  (Inst/Model/Common/Site.lean); `R8`, `R16`: the tables ι, for ι < 2^8, and ι, for ι < 2^16
  (Inst/Model/Tables.lean); `InLut p L key`: the key is congruent modulo p to an entry of the table
  (Inst/Model/Common/TableKeys.lean); in `resid_site`: `A`, `x`, `x'`, `rh`, `Ab`: integers: the
  accumulator, the two states of the stream, the high digit, the bound on |A|; `k`: the shift.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.FF.NoWrapProj
import Inst.Model.Sanity

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset
open Inst.Model.TableKeys (InLut)

/-- The size conditions for the residual additions, and the ranges of the weights. -/
structure AdmS (p : ℤ) (D : Dim) (L0 : ℕ) (w : ℕ → LayerW) : Prop where
  ko : ∀ l, (D.Pl l).ko ≤ 24
  kd : ∀ l, (D.Pl l).kd ≤ 24
  hi : 2 ^ 8 * (2 ^ 18 + 128) + 2 ^ 8 ≤ p
  /-- The no-overflow condition of a rounding site, in the form of the implementation's
  (`Scales.SiteW`, Inst/Model/FF/ScalesDef.lean) with ≤ p − 2^16 where that has < 2^60: the sites O
  and D. The accumulator's bound is multiplied by the weight 2^dn(k), dn(k) = max(0, 16 − k) -/
  o : ∀ l, 2 ^ Site.dn (D.Pl l).ko *
        ((D.dq : ℤ) * (2047 * 2 ^ 12) + 2 ^ ((D.Pl l).ko - 1) + 2 ^ (D.Pl l).ko * 2 ^ 40) +
      2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ p
  d : ∀ l, 2 ^ Site.dn (D.Pl l).kd *
        ((D.f : ℤ) * (4095 * 2 ^ 15 * 2 ^ 12) + 2 ^ ((D.Pl l).kd - 1) + 2 ^ (D.Pl l).kd * 2 ^ 40) +
      2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤ p
  even : L0 % 2 = 0
  f : D.P.f = 2 * D.P.fe
  nexp : 1 ≤ D.P.nexp
  wf : ∀ l < D.nl, (w l).WF D.P (L0 + l)

omit scl in
/-- A residual addition: under the bounds below, the two keys force x' = x + rhu(A, k) and the high
digit, which has one cell and the offset 128. -/
theorem resid_site {p : ℤ} {k : ℕ} (hk : k ≤ 24) {A x x' rh Ab : ℤ} (hA : |A| ≤ Ab)
    (hx : |x| < 2 ^ 39) (hx' : |x'| < 2 ^ 39) (hR : |rh - 128| ≤ 2 ^ 18)
    (hpH : 2 ^ 8 * (2 ^ 18 + 128) + 2 ^ 8 ≤ p)
    (hpL : 2 ^ Site.dn k * (Ab + 2 ^ (k - 1) + 2 ^ k * 2 ^ 40) + 2 ^ 16 * (2 ^ 18 + 128) + 2 ^ 16 ≤
      p)
    (kL : InLut p R16 (Site.ssite A (x' - x) rh k)) (kH : InLut p R8 (Site.shigh rh k 24)) :
    x' = x + rhu A k ∧ rh = Site.hd A k := by
  have hR' : |rh| ≤ 2 ^ 18 + 128 := by
    have := abs_le.mp hR
    rw [abs_le]
    constructor <;> linarith
  have hq : |x' - x| ≤ 2 ^ 40 := by
    have h1 := abs_lt.mp hx
    have h2 := abs_lt.mp hx'
    rw [abs_le]
    constructor <;> linarith
  have k3 : (2 : ℤ) ^ (24 - Site.up k) ≤ 2 ^ 8 := Site.two_pow_top_sub_le k rfl
  obtain ⟨r0, r1⟩ := Site.shigh_sound (w := 8) rfl hk hR' (by nlinarith) kH.r8
  obtain ⟨s1, s2, s3⟩ := Site.ssite_sound hA hq hR' r0 r1 hpL kL.r16
  refine ⟨by linarith, ?_⟩
  rw [s1] at s2 s3
  exact Site.hd_unique_s s2 s3

section Rel
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {p : ℤ} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}

/-- (PL7), under `IntRel`, `AdmN`, `AdmS` and (FA12). (not all hypotheses are named here: see the
statement below) -/
theorem pl7_at (h : IntRel D tb L0 first p w emb tok t) (admN : AdmN p D)
    (adm : AdmS p D L0 w) {l i : ℕ} (hl : l < D.nl) (hi : i < D.T)
    (ho : ∀ j < D.dq, |val t .o l j i| ≤ 2047) {c : ℕ} (hc : c < D.d) :
    xS D t (2 * l + 1) c i =
      xS D t (2 * l) c i +
        rhu (dot D.dq (fun j => val t .o l j i) fun j => (w l).Wo j c) (D.Pl l).ko ∧
    val t .ro l c i =
      Site.hd (dot D.dq (fun j => val t .o l j i) fun j => (w l).Wo j c) (D.Pl l).ko := by
  obtain ⟨-, -, -, -, b0, -⟩ := ledger_at h admN (ν := 2 * l) (show 2 * l < 2 * D.nl by omega) hi
  obtain ⟨-, -, -, -, b1, -⟩ :=
    ledger_at h admN (ν := 2 * l + 1) (show 2 * l + 1 < 2 * D.nl by omega) hi
  obtain ⟨-, -, -, hWo, -⟩ := adm.wf l hl
  exact resid_site (adm.ko _) (abs_dot_le ho fun j _ => abs_two_le hWo j c) (b0 c hc) (b1 c hc)
    (val1 h.small .ro rfl (a := l) (j := c) hl hc hi) adm.hi (adm.o _)
    (h.key .O l c i hl rfl hc hi) (h.key .OH l c i hl rfl hc hi)

/-! ## (PL12) -/

omit scl in
theorem hasExperts_iff (he : L0 % 2 = 0) (l : ℕ) : hasExperts (L0 + l) ↔ isExpL l = true := by
  unfold hasExperts isExpL
  simp only [beq_iff_eq]
  omega

section Ad
variable {l i : ℕ}
  (hsl : ∀ x < D.f, val t .sl l x i =
    UNIT.sl tb D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x) (FF.kG (D.Pl l) (L0 + l) x))
  (hup : ∀ x < D.f, val t .up l x i =
    UNIT.up D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x) (FF.kU (D.Pl l) (L0 + l) x))
include hsl hup

theorem hh_eq {x : ℕ} (hx : x < D.f) :
    hh t l x i = FF.hh (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x := by
  unfold hh
  rw [hsl x hx, hup x hx]
  rfl

/-- (PL12): under `AdmS`, the accumulator of the trace is the program's, once sl, up and sel hold
the program's values. -/
theorem Ad_eq (adm : AdmS p D L0 w)
    (hsel : isExpL l = true →
      ∀ e < D.nx, val t .sel (l / 2) e i =
        if e = FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i then 1 else 0) (c : ℕ) :
    Ad D t (fun l => LW.ofInt ℤ (w l)) l c i =
      FF.Ad (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i c := by
  have hf : D.f = 2 * D.fe := adm.f
  unfold Ad FF.Ad FF.units
  by_cases hE : isExpL l = true
  · have hE' : hasExperts (L0 + l) := (hasExperts_iff adm.even l).2 hE
    rw [if_pos hE, if_pos hE', two_mul, sum_range_add]
    have hes : FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i < D.nx := by
      have h1 :=
        (argTo_spec (FF.lr (D.Pl l) (w l) (stream D t (2 * l + 1)) i) ((D.Pl l).nexp - 1)).1
      have h2 : 1 ≤ (D.Pl l).nexp := adm.nexp
      show argTo _ _ < (D.Pl l).nexp
      omega
    congr 1
    · refine sum_congr rfl fun j hj => ?_
      have hj' : j < D.fe := mem_range.1 hj
      rw [hh_eq hsl hup (by omega),
        if_neg (fun hr : FF.routed (D.Pl l) (L0 + l) j => by have : D.fe ≤ j := hr.2; omega)]
      rfl
    · rw [sum_eq_single_of_mem (FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i) (mem_range.2 hes) fun e he hne => by
        rw [hsel hE e (mem_range.1 he), if_neg hne, zero_mul]]
      rw [hsel hE _ hes, if_pos rfl, one_mul]
      refine sum_congr rfl fun j hj => ?_
      have hj' : j < D.fe := mem_range.1 hj
      have hr : FF.routed (D.Pl l) (L0 + l) ((D.Pl l).fe + j) := ⟨hE', Nat.le_add_right _ _⟩
      rw [hh_eq hsl hup (by omega), if_pos hr, Nat.add_sub_cancel_left]
      rfl
  · have hE' : ¬ hasExperts (L0 + l) := fun h' => hE ((hasExperts_iff adm.even l).1 h')
    rw [if_neg hE, if_neg hE']
    refine sum_congr rfl fun j hj => ?_
    rw [hh_eq hsl hup (mem_range.1 hj), if_neg (fun hr : FF.routed (D.Pl l) (L0 + l) j => hE' hr.1)]
    rfl

end Ad

/-- The bound on the accumulator of D, on the program's values, under `AdmS` (two-byte weights, f =
2 fe), `hl` and `hhh` (|hh| ≤ 4,095 · 2^15, from |sl| ≤ 4,095 and "up fits 16 bits": `NWR.hh_abs`,
Cm/TargetInstFFRouter.lean). -/
theorem abs_Ad_le (adm : AdmS p D L0 w) {l : ℕ} (hl : l < D.nl) (x : ℕ → Vec) (i c : ℕ)
    (hhh : ∀ j < D.f, |FF.hh (D.Pl l) tb (w l) (L0 + l) x i j| ≤ 4095 * 2 ^ 15) :
    |FF.Ad (D.Pl l) tb (w l) (L0 + l) x i c| ≤ (D.f : ℤ) * (4095 * 2 ^ 15 * 2 ^ 12) := by
  have hu : FF.units (D.Pl l) (L0 + l) = D.f := by
    unfold FF.units
    split_ifs
    · exact adm.f.symm
    · rfl
  have hW : ∀ j, |if FF.routed (D.Pl l) (L0 + l) j then
        (w l).Ed (FF.es (D.Pl l) (w l) x i) (j - D.P.fe) c
      else (w l).Wd j c| ≤ 2 ^ 12 := fun j => by
    have hwf := (adm.wf l hl).2.2.2.2
    split_ifs with hr
    · rw [if_pos hr.1] at hwf
      have h5 := hwf.2.2.2.2 (FF.es (D.Pl l) (w l) x i)
      split_ifs at h5
      · exact abs_two_le h5.2.2 _ _
      · exact abs_two_le h5.2.2 _ _
    · split_ifs at hwf
      · exact abs_two_le hwf.2.2.1 _ _
      · exact abs_two_le hwf.2.2.1 _ _
  unfold FF.Ad
  rw [hu]
  exact abs_dot_le (a := fun j => FF.hh (D.Pl l) tb (w l) (L0 + l) x i j) hhh fun j _ => hW j

/-- (PL13), under `IntRel`, `AdmN`, `AdmS` and the hypotheses `hx2`, `hAd`, `hhh`, `hl`, `hi`, `hc`.
`hx2` is the bound on the stream at the index 2ℓ + 2, which is (FL14) for an index that a
normalisation of the segment reads and (FL19) for the last index. -/
theorem pl13_at (h : IntRel D tb L0 first p w emb tok t) (admN : AdmN p D) (adm : AdmS p D L0 w)
    {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) {c : ℕ} (hc : c < D.d)
    (hx2 : |xS D t (2 * l + 2) c i| < 2 ^ 39)
    (hAd : Ad D t (fun l => LW.ofInt ℤ (w l)) l c i =
      FF.Ad (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i c)
    (hhh : ∀ j < D.f,
      |FF.hh (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i j| ≤ 4095 * 2 ^ 15) :
    xS D t (2 * l + 2) c i = FF.x'' (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i c ∧
    val t .rd l c i =
      Site.hd (FF.Ad (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i c) (D.Pl l).kd := by
  obtain ⟨-, -, -, -, b1, -⟩ :=
    ledger_at h admN (ν := 2 * l + 1) (show 2 * l + 1 < 2 * D.nl by omega) hi
  have kL := h.key .D l c i hl rfl hc hi
  have eL : key D t tb L0 (fun l => LW.ofInt ℤ (w l)) .D l c i =
      Site.ssite (FF.Ad (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i c)
        (xS D t (2 * l + 2) c i - xS D t (2 * l + 1) c i) (val t .rd l c i) (D.Pl l).kd := by
    simp only [key]
    rw [hAd]
  rw [eL] at kL
  exact resid_site (adm.kd _) (abs_Ad_le adm hl _ i c hhh) (b1 c hc) hx2
    (val1 h.small .rd rfl (a := l) (j := c) hl hc hi) adm.hi (adm.d _)
    kL (h.key .DH l c i hl rfl hc hi)

/-- the bound on the stream at an index that a normalisation of the segment reads, or at the last
index from (FL19) -/
theorem stream_bound (h : IntRel D tb L0 first p w emb tok t) (admN : AdmN p D)
    (hlast : LastBound D t) {s i j : ℕ} (hs : s ≤ 2 * D.nl) (hi : i < D.T) (hj : j < D.d) :
    |xS D t s j i| < 2 ^ 39 := by
  rcases Nat.lt_or_ge s (2 * D.nl) with h1 | h1
  · exact (ledger_at h admN (ν := s) h1 hi).2.2.2.2.1 j hj
  · obtain rfl : s = 2 * D.nl := by omega
    exact hlast i hi j hj

end Rel

end Inst.Model.FFSeg
