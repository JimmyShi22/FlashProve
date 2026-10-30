-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/NoWrapRouter.lean: no wrap-around (the term: the head of Inst/Model/FF/NoWrap.lean)
  in a feed-forward segment: the router, the routed expert, the feed-forward block's hidden layer.

  This file and Cm/TargetInstFFRouter.lean treat the router and the routed expert ((FL40): only the
  chosen expert contributes). The work for a single position is done in
  Inst/Model/Common/Router.lean (`router_sound`) and Inst/Model/Common/Unit.lean. In
  Cm/TargetInstFFRouter.lean the looked-up values (keys) of the router of a layer with experts at a
  position are taken from the field relation, and the results are stated with the functions of
  Inst/Model/Program.lean.
    `WFabs`               what is used of `LayerW.WF`: every weight that the feed-forward block
                          reads is at most 2^12 in absolute value
    `rv`, `small`, `keys` the values of the router; condition (1) (every valid cell is below 2^18
                          in absolute value) for these values; its keys and (J10)
    `router_facts`        `Part3.ly`, `l3`, `lr`, `sel`, `sc`, `xr`, the range condition of (R2),
                          and |xr| ≤ 2,047
    `hidden_facts`        `Part3.slP`, `upP`, hh, and the range conditions of UNIT
    `ok_facts`            `Part3.ok`
    `emb_facts`           (PL1), in the first segment (its hypotheses: see its docstring)
  Here: `WFabs`, `SzR`, `rv` and the lemmas beneath. The others: Cm/TargetInstFFRouter.lean.
  `router_facts`, `hidden_facts`, `ok_facts` are under `RFraw` over `ZMod p` (`Big p`), the ranges
  of the tables (`tb.OK`), `SzR` (128 experts; f = 2 fe; the router's shift from 8 to 24; `Sz`) and
  `WFabs`, at a layer l < D.nl and a position i < D.T (`hidden_facts`: at a hidden unit x < D.f);
  the first is for a layer with experts, the other two assume that the segment starts at an even
  layer. Two facts of the first half of the proof (`norm2_at`, Inst/Model/FF/NoWrapNorm.lean) are
  hypotheses of these theorems: m is the program's second normalisation, and its range conditions
  are met. Labels such as (FL40) and "Step L9" link one docstring to another.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). A
  theorem marked "omit scl in" reads no scale.

  Notation: no wrap-around (the file's name): see the head of Inst/Model/FF/NoWrap.lean; `D`: a
  `Dim`: the sizes of a feed-forward segment; ly, l3, lr, sel, ..: arrays (`Arr`)
  (Inst/Model/FF/Index.lean); `tb`: `Tables`: the five table functions that the program reads;
  `w l`: a `LayerW`: the weight matrices of one layer; `FF.ly`, `l3`, `lr`, `es`, `sc`, `xr`, `hh`:
  the integer program's values of the steps (R2) to (R6), (PL9), (PL11); `FF.z`, `wg`, `wu`, `kG`,
  `kU`: the input, the two columns and the two shifts of the hidden unit j
  (Inst/Model/Program.lean); `P'`: a `Params`; `tb.OK P'`: the bounds (Tab3), (Tab4), (Tab5), (Tab8)
  on the tables (Inst/Model/Tables.lean); `L0`: a natural number: the first layer of the segment;
  `t`: a map `Cell` → ℤ: a trace, a function on the names of cells; `val t X inst j i`: the read-out
  formula, at an array, an instance, a channel j and a position i; the arrays of the router have the
  instance ℓ′, which is layer 2ℓ′ + 1 (so l / 2) (`hv`); `hh t l j i`: sl_j up_j
  (Inst/Model/FF/Trace.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.FF.NoWrapUnit
import Inst.Model.Common.Router
import Inst.Model.All.Congr

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg

variable [scl : Scl]

open Finset

namespace NWR
open NWU (abs_dot_le Sz)

/-! ## The weights -/

omit scl in
theorem two_abs {r c : ℕ} {W : Mat} (h : Two r c W) (j x : ℕ) : |W j x| ≤ 2 ^ 12 := by
  have := h j x
  rw [abs_le]
  split_ifs at this
  · constructor <;> omega
  · rw [this]
    norm_num

/-- every weight that the feed-forward block reads is at most 2^12 in absolute value -/
structure WFabs (w : LayerW) : Prop where
  Wg : ∀ j x, |w.Wg j x| ≤ 2 ^ 12
  Wu : ∀ j x, |w.Wu j x| ≤ 2 ^ 12
  Wd : ∀ j x, |w.Wd j x| ≤ 2 ^ 12
  Wr : ∀ j x, |w.Wr j x| ≤ 2 ^ 12
  Eg : ∀ e j x, |w.Eg e j x| ≤ 2 ^ 12
  Eu : ∀ e j x, |w.Eu e j x| ≤ 2 ^ 12
  Ed : ∀ e j x, |w.Ed e j x| ≤ 2 ^ 12

omit scl in
theorem WFabs.of_wf {P : Params} {L : ℕ} {w : LayerW} (h : w.WF P L) : WFabs w := by
  obtain ⟨-, -, -, -, h5⟩ := h
  split_ifs at h5
  · obtain ⟨a, b, c, d, e⟩ := h5
    refine ⟨two_abs a, two_abs b, two_abs c, two_abs d, fun k => ?_, fun k => ?_, fun k => ?_⟩ <;>
    · have := e k
      split_ifs at this
      · first | exact two_abs this.1 | exact two_abs this.2.1 | exact two_abs this.2.2
      · first | exact two_abs this.1 | exact two_abs this.2.1 | exact two_abs this.2.2
  · obtain ⟨a, b, c, d, e⟩ := h5
    exact ⟨two_abs a, two_abs b, two_abs c, two_abs d, fun k => two_abs (e k).1,
      fun k => two_abs (e k).2.1, fun k => two_abs (e k).2.2⟩

/-! ## The router -/

/-- what is used of the sizes, besides `Sz` -/
structure SzR (D : Dim) : Prop extends Sz D where
  /-- below 8 a quotient may exceed the radix of the key CLR (the implementation's condition
  guard-radix-clamp) -/
  kr : ∀ l, 8 ≤ (D.Pl l).kr ∧ (D.Pl l).kr ≤ 24
  nx : D.nx = 128
  f2 : D.f = 2 * D.fe

/-- The values of the router of the layer with experts number ℓ′ at position i. -/
def rv (t : Cell → ℤ) (l' i : ℕ) : Router.RouterV :=
  ⟨fun e => val t .ly l' e i, fun e => val t .l3 l' e i,
    fun e => val t .lr l' e i, fun e => val t .sel l' e i,
    fun e => val t .rl l' e i, val t .sc l' 0 i, fun j => val t .xr l' j i⟩

omit scl in
theorem abs_clamp (a : ℤ) : |clamp 2047 a| ≤ 2047 := by
  unfold clamp
  rw [abs_le]
  constructor <;> omega

section
variable {D : Dim} {l : ℕ} (hl : l < D.nl) (he : isExpL l = true)

omit scl in
include hl he in
theorem half_lt : l / 2 < D.ne := by
  have h1 : l % 2 = 1 := by simpa [isExpL] using he
  unfold Dim.ne
  omega

end

/-! ## The second normalisation is at most 2,047 in absolute value -/

section
variable {D : Dim} {t : Cell → ℤ} {l i : ℕ}
  (hmP : ∀ j < D.d, val t .m l j i = FF.m (D.Pl l) (stream D t (2 * l + 1)) i j)

include hmP in
theorem m_abs : ∀ j < D.d, |val t .m l j i| ≤ 2047 := fun j hj => by
  rw [hmP j hj]
  exact abs_clamp _

end

/-! ## The flags of a layer with experts; a sum against an indicator -/

/-- the flag `routed` of the trace is that of the program, in a segment that starts at an even layer
-/
theorem routed_iff {D : Dim} {L0 : ℕ} (hL0 : L0 % 2 = 0) (l x : ℕ) :
    routed D l x = true ↔ FF.routed (D.Pl l) (L0 + l) x := by
  unfold routed FF.routed hasExperts isExpL Dim.fe
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by omega, b⟩

omit scl in
theorem exp_iff {L0 : ℕ} (hL0 : L0 % 2 = 0) (l : ℕ) : isExpL l = true ↔ hasExperts (L0 + l) := by
  unfold hasExperts isExpL
  simp only [beq_iff_eq]
  omega

omit scl in
/-- a sum against the indicator of one index -/
theorem sum_ind {n es : ℕ} (hes : es < n) {sel : ℕ → ℤ}
    (hsel : ∀ e < n, sel e = if e = es then 1 else 0) (G : ℕ → ℤ) :
    ∑ e ∈ range n, sel e * G e = G es := by
  rw [Finset.sum_eq_single es]
  · rw [hsel es hes, if_pos rfl, one_mul]
  · intro e he hne
    rw [hsel e (mem_range.mp he), if_neg hne, zero_mul]
  · intro hn
    exact absurd (mem_range.mpr hes) hn

end NWR

end Inst.Model.FFSeg
