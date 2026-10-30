-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/NoWrap2.lean: from the field relation of an attention segment to the program,
  second half: what does not read the modulus. What reads it is in Inst/Model/Bound/Att2.lean, in
  parts of the same numbers, for a number p with `Big p`. This head tells the parts of both files.

  * Part 1: `tau2_row`, `maxTo_eq`. In Inst/Model/Bound/Att2.lean: the three steps on bare integers:
    a looked-up value of call 2; (At3) (`Idn.at3`, Inst/Model/Att/Trace.lean); the pieces (3W, b).
  * Part 2: Step A5 at the entries of the two regions: (FA7), (FA8), (FA9); the weight at the entry
    of a pair of positions. Here: the positions of an entry (`posM`, `posD`) and `gp_bounds`.
  * Part 3: Step A6: (PA2), (FA10), (FA11). Here: the weight on integers (`wtP`, `wtP_bounds`).
  * Part 4: Step A7: (FA12): all of it in Inst/Model/Bound/Att2.lean.
  * Part 5: the program: under `InputsAre` and `Fit`, for the pairs b of the layer, with the same
    Exp in both tables, the functions of the cells scV and outV are sc and o of
    Inst/Model/Program.lean (`sc_link` here; `out_link` in Inst/Model/Bound/Att2.lean; mx, wt, den,
    ac: steps inside the proof of `out_link`).
  * Part 6: the reference parameters (`exp_facts`, `fit_ref`, `exp_ref`). The two statements at any
    valid shift are `outBoundK`, `noWrapK` (Inst/Model/Bound/AttK.lean).
  Parts 1 to 5 are for every valid input shift sh of the exponential and every valid number u0 of
  its live rows (sh is read from the scales, u0 is a field of D; `ExpOK` in Inst/Model/Tables.lean;
  8 and 2,307 at the reference parameters). Parts 2 to 5 are for sizes D with at most 1,024
  positions (Parts 2 to 4: any such D; Part 5: under `Fit`), for one pair b, from `IntRel`
  (Inst/Model/Att/NoWrap0.lean) and what Steps A1 to A4 give for b (`Half1`; `half1` in
  Inst/Model/Bound/Att1.lean gives it from `IntRel` under D.ch ≤ 128, D.lT ≤ 10 and `InB`), with the
  ranges (Tab8) of Exp and, for (FA11), (FA12), `InB`. (PL5), (PA1) to (PA7):
  Inst/Model/Program.lean. Labels such as (PA2) and (FA7) link the docstrings of both files.
  Text in double quotes: see the head of Inst/Model/Program.lean.
-/
import Inst.Model.Att.NoWrap1
import Inst.Model.TablesExp
import Inst.Model.Sanity

set_option autoImplicit false

namespace Inst.Model.AttSeg

open Finset

namespace NW2
open NW (eq_of_dvd)

/-! ## Part 1. The rows of τ2, and the maximum (the three steps: Inst/Model/Bound/Att2.lean) -/

/-- The rows of τ2 (`tau2`, Inst/Model/Tables.lean; (Tab8)): e1 + 2^32 f + 2^33 v, live (f = 0, e1 =
2^sh ι, v = Exp[ι]) or dead (f = 1, v = 0, C − 2^sh ≤ e1 ≤ C + 4 S_max + 2^15). -/
theorem tau2_row {sh u0 : ℕ} (hO : ExpOK sh u0) {tb : Tables}
    (hE : ∀ u : ℕ, u < u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) {ι : ℕ} (hι : ι < 2 ^ 16) :
    ∃ e1 f v : ℤ,
      (tau2 sh u0 tb).row ι = e1 + 2 ^ 32 * f + 2 ^ 33 * v ∧
      ((ι < u0 ∧ e1 = 2 ^ sh * ι ∧ f = 0 ∧ v = tb.Exp ι ∧ 1 ≤ v ∧ v ≤ 2 ^ 12) ∨
        (f = 1 ∧ v = 0 ∧ cutC sh u0 - 2 ^ sh ≤ e1 ∧ e1 ≤ cutC sh u0 + 4 * Smax + 2 ^ 15)) := by
  obtain ⟨s0, s1⟩ := un_bounds hO
  obtain ⟨st0, st1⟩ := stp_bounds hO
  obtain ⟨n0, -⟩ := nd_spec hO
  have hfill := hO.fill
  have small : ∀ {x : ℤ},
      0 ≤ x → x < nd sh → 0 ≤ stp sh * x ∧ stp sh * x ≤ 4 * Smax := fun {x} hx0 hx1 =>
    ⟨mul_nonneg (by omega) hx0,
      le_trans (mul_le_mul_of_nonneg_left (by omega : x ≤ (nd sh : ℤ) - 1) (by omega)) n0⟩
  simp only [tau2]
  by_cases h1 : ι < u0
  · rw [if_pos h1]
    exact ⟨2 ^ sh * ι, 0, tb.Exp ι, by ring, Or.inl ⟨h1, rfl, rfl, rfl, (hE ι h1).1, (hE ι h1).2⟩⟩
  · rw [if_neg h1]
    by_cases h2 : ι < u0 + nd sh
    · rw [if_pos h2]
      obtain ⟨q0, q1⟩ := small (x := (ι : ℤ) - u0) (by omega) (by omega)
      refine ⟨cutC sh u0 - 2 ^ sh + stp sh * (ι - u0), 1, 0, by ring, Or.inr ⟨rfl, rfl, ?_, ?_⟩⟩
        <;> omega
    · rw [if_neg h2]
      obtain ⟨q0, q1⟩ :=
        small (x := (ι : ℤ) - (u0 + nd sh : ℕ)) (by push_cast; omega) (by push_cast; omega)
      refine ⟨cutC sh u0 - 2 ^ sh + stp sh * (ι - (u0 + nd sh : ℕ)) + stp sh / 2, 1, 0,
          by ring, Or.inr ⟨rfl, rfl, ?_, ?_⟩⟩ <;> omega

/-- (PA2): a number that bounds f on j ≤ n and is attained there is the maximum. -/
theorem maxTo_eq {f : Vec} {n : ℕ} {m : ℤ} (hle : ∀ j ≤ n, f j ≤ m) (hat : ∃ j ≤ n, f j = m) :
    maxTo f n = m := by
  obtain ⟨h1, j0, hj0, e0⟩ := maxTo_spec f n
  obtain ⟨j1, hj1, e1⟩ := hat
  exact le_antisymm (e0 ▸ hle j0 hj0) (e1 ▸ h1 j1 hj1)

/-! ## Part 2. Step A5 at the entries: what does not read the modulus -/

section Places
variable {D : Dim} {t : Raw → ℤ} {b : ℕ}

theorem gp_M [scl : Scl] (x : ℕ) :
    gp D t .M b x =
      if D.EmptyM x then D.cutC
      else mxV t b (D.mG x) (D.iM x) - scV D t b (D.mG x) (D.iM x) (D.jM x) := rfl

theorem gp_D [scl : Scl] (x : ℕ) :
    gp D t .D b x =
      mxV t b (D.dG x) (D.iD x) - scV D t b (D.dG x) (D.iD x) (D.jD x) +
        if D.MaskedD x then Om D else 0 := rfl

theorem lt_T {R r : ℕ} (hR : R < D.nBlk) (hr : r < D.B) : D.B * R + r < D.T := by
  unfold Dim.T
  nlinarith

theorem mx_abs [scl : Scl] (H : Half1 D t b) {g i : ℕ} (hg : g < D.nG) (hi : i < D.T) :
    |mxV t b g i| ≤ Smax := by
  obtain ⟨js, hjs, e⟩ := H.fa6 g i hg hi
  rw [e]
  exact H.fa5 g i js hg hi (lt_of_le_of_lt hjs hi)

theorem diff_bounds [scl : Scl] (H : Half1 D t b) {g i j : ℕ} (hg : g < D.nG)
    (hi : i < D.T) (hj : j < D.T) :
    -1072693504 ≤ mxV t b g i - scV D t b g i j ∧ mxV t b g i - scV D t b g i j ≤ 1072693504 := by
  have a := abs_le.mp (mx_abs H hg hi)
  have c := abs_le.mp (H.fa5 g i j hg hi hj)
  norm_num [Smax] at a c
  constructor <;> omega

/-- the positions of an entry of M that is not empty -/
theorem posM {x : ℕ} (hx : x < 2 ^ D.lM) (hne : ¬ D.EmptyM x) :
    D.mG x < D.nG ∧ D.iM x < D.T ∧ D.jM x < D.T := by
  have hP : D.mP x < D.hP := Nat.mod_lt _ D.hP_pos
  have hs : D.mS x < D.nBlk := Nat.mod_lt _ D.nBlk_pos
  have hs' : D.mS x < D.nBlk - 1 := by
    unfold Dim.EmptyM at hne
    omega
  obtain ⟨h1, h2, -, -⟩ := D.blk_of_slot hP hs'
  exact ⟨D.mG_lt hx, lt_T h2 (Nat.mod_lt _ D.B_pos), lt_T (lt_trans h1 h2) (Nat.mod_lt _ D.B_pos)⟩

theorem posD {x : ℕ} (hx : x < 2 ^ D.lD) : D.dG x < D.nG ∧ D.iD x < D.T ∧ D.jD x < D.T :=
  ⟨D.dG_lt hx,
    lt_T (Nat.mod_lt _ D.nBlk_pos) (Nat.mod_lt _ D.B_pos),
    lt_T (Nat.mod_lt _ D.nBlk_pos) (Nat.mod_lt _ D.B_pos)⟩

/-- Under the hypotheses below:
"at every place −2 S_max ≤ gp ≤ 2 S_max + Om; this includes the value C at an empty place" -/
theorem gp_bounds [scl : Scl] (hO : ExpOK D.sh D.u0) (H : Half1 D t b) (ρ : Reg)
    {x : ℕ} (hx : x < 2 ^ D.lReg ρ) :
    -1072693504 ≤ gp D t ρ b x ∧ gp D t ρ b x ≤ 2145387008 + D.cutC := by
  obtain ⟨c0, c1⟩ : 0 < D.cutC ∧ D.cutC ≤ 2 ^ 24 - 2 ^ 16 := cutC_bounds hO
  cases ρ with
  | M =>
    rw [gp_M]
    by_cases he : D.EmptyM x
    · rw [if_pos he]
      constructor <;> omega
    · rw [if_neg he]
      obtain ⟨h1, h2, h3⟩ := posM hx he
      have := diff_bounds H h1 h2 h3
      constructor <;> omega
  | D =>
    rw [gp_D]
    obtain ⟨h1, h2, h3⟩ := posD hx
    have := diff_bounds H h1 h2 h3
    by_cases hm : D.MaskedD x
    · rw [if_pos hm]
      have hOm : Om D = 1072693504 + D.cutC := by norm_num [Om, Smax]
      rw [hOm]
      constructor <;> omega
    · rw [if_neg hm]
      constructor <;> omega

end Places

/-! ## Part 3. Step A6: what does not read the modulus -/

/-- (PA3), (PA4) on integers: the weight of position j, for the greatest score m and the scores s -/
def wtP [scl : Scl] (D : Dim) (tb : Tables) (m : ℤ) (s : ℕ → ℤ) (j : ℕ) : ℤ :=
  if (m - s j) / 2 ^ D.sh < D.u0 then tb.Exp ((m - s j) / 2 ^ D.sh) else 0

theorem wtP_bounds [scl : Scl] {D : Dim} {tb : Tables}
    (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) {m : ℤ} {s : ℕ → ℤ}
    {j : ℕ} (hd : 0 ≤ m - s j) :
    0 ≤ wtP D tb m s j ∧ wtP D tb m s j ≤ 2 ^ 12 := by
  unfold wtP
  split_ifs with hc
  · obtain ⟨u, hu⟩ :=
      Int.eq_ofNat_of_zero_le (Int.ediv_nonneg hd (by positivity : (0 : ℤ) ≤ 2 ^ D.sh))
    rw [hu] at hc ⊢
    have := hE u (by exact_mod_cast hc)
    exact ⟨by omega, this.2⟩
  · norm_num

/-! ## Part 5. The program: what does not read the modulus -/

/-- what the link needs: ch and na (positive), the number of live rows and the shift are those of
P -/
structure Fit [scl : Scl] (D : Dim) (P : Params) : Prop where
  ch : D.ch = P.ch
  na : D.na = P.nq / P.nkv
  pos : 0 < D.na
  exp : P.expRows = D.u0
  sh : P.sh = D.sh

theorem maxTo_congr {f g : Vec} : ∀ n : ℕ, (∀ j ≤ n, f j = g j) → maxTo f n = maxTo g n
  | 0, h => h 0 le_rfl
  | n + 1, h => by
    simp only [maxTo]
    rw [maxTo_congr n fun j hj => h j (Nat.le_succ_of_le hj), h (n + 1) le_rfl]

theorem abs_clamp (a : ℤ) : |clamp 2047 a| ≤ 2047 := by
  unfold clamp
  rw [abs_le]
  constructor <;> omega

section Link
variable {D : Dim} {P : Params} {tbP : Tables} {w : LayerW} {L : ℕ} {x : ℕ → Vec}
  {lam : ℕ} {t : Raw → ℤ} {b : ℕ}

/-- "Query head h reads key/value head g = ⌊h/5⌋": under `Fit` (F); 5 is nq / nkv at
`ppref`. -/
theorem kvOf_head [scl : Scl] (F : Fit D P) (g b : ℕ) : Att.kvOf P (D.head g b) = g := by
  unfold Att.kvOf Dim.head Dim.aOf
  rw [← F.na, Nat.mul_add_div F.pos, Nat.div_eq_of_lt (Nat.mod_lt _ F.pos), Nat.add_zero]

/-- Under `InputsAre` (hin): q, kx, v are outputs of clamps: (FL9') for the pairs of the layer -/
theorem inB_of_inputs (hin : InputsAre D P tbP w L x lam t) (hb : b < D.nb) (hl : D.lamOf b = lam) :
    InB D t b := by
  refine ⟨fun g hg i hi n hn => ?_, fun g hg j hj n hn => ?_⟩
  · rw [hin.1 b hb hl g hg i hi n hn]
    exact abs_clamp _
  · rw [hl, (hin.2 g hg j hj n hn).1, (hin.2 g hg j hj n hn).2]
    exact ⟨abs_clamp _, abs_clamp _⟩

/-- (PA1) -/
theorem sc_link [scl : Scl] (F : Fit D P) (hin : InputsAre D P tbP w L x lam t) (hb : b < D.nb)
    (hl : D.lamOf b = lam) {g i j : ℕ} (hg : g < D.nG) (hi : i < D.T) (hj : j < D.T) :
    scV D t b g i j = Att.sc P tbP w L x (D.head g b) i j := by
  unfold scV Att.sc
  rw [kvOf_head F, ← F.ch, hl]
  exact sum_congr rfl fun n hn => by
    rw [hin.1 b hb hl g hg i hi n (mem_range.mp hn), (hin.2 g hg j hj n (mem_range.mp hn)).1]

end Link

/-! ## Part 6. The reference parameters -/

theorem exp_facts {tb : Tables} (hOK : tb.OK ppref) :
    (∀ u : ℕ, u < Dim.ref.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) ∧ tb.Exp 0 = 2 ^ 12 :=
  ⟨fun u hu => hOK.2.2.2.1 u hu, hOK.2.2.2.2⟩

theorem fit_ref [scl : Scl] [law : Lawful] (lam : ℕ) : Fit Dim.ref (refP lam) :=
  ⟨(by decide : Dim.ref.ch = ppref.ch), (by decide : Dim.ref.na = ppref.nq / ppref.nkv),
    by decide, law.rows lam, law.sh lam⟩

/-- for valid scales, their shift and the reference number of live rows are a valid pair -/
theorem exp_ref [scl : Scl] [law : Lawful] : ExpOK Dim.ref.sh Dim.ref.u0 := law.ex

theorem lamOf_lt {D : Dim} {b : ℕ} (hb : b < D.nb) : D.lamOf b < D.nl :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)

end NW2

end Inst.Model.AttSeg
