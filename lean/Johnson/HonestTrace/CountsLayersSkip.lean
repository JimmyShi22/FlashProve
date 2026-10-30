-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsLayersSkip.lean

Under six premises on public numbers, the library's terms G.kvG for the keys of a layers' sub-proof
do not read the planes' matrix b, at the calls below NC and the places below 2^(n_q): two readings
that agree outside that matrix give the same keys ("kvG_congr"). With it: KeysSkipB
(Johnson/HonestTrace/CountsLayers.lean) as a theorem, and the relation after the challenge
(Cb.Lkp.MidP) at cells into which the planes have been laid.

Notation: as in Johnson/HonestTrace/CountsLayers.lean; NGr, Lam and T are fields of P.y.

Why it needs a proof. G.kvG (OnBytes/Tie/Pv/Lookup/Ends/G.lean) reads a tensor's cell by a running
number: feature F of a family of matrices lies in matrix number M0 + F / (columns times features of
a column). A feature past its family's room lands in the next matrix of the list, and after ar that
is b. So it has to be shown that every feature that a key reads lies inside its family.

The steps. "The six premises" are: Layer.layout h pc returns P.y; Road.Switches h; Layer.scalesHeld
h P.sc returns; g < P.y.NGr; h.p4 = true; h.dh is even.
1. "fam_part_lt": in a layout with the facts Road.Laid2, a feature below the number of features in
   use of af, ad or ar lies in one of the family's parts.
2. "AgreeG P cell' cell": the two readings agree at every name but the cells of matrix number G.iB
   P.y. "cG_congr", "cellsOf_congr": under it the library's names of cells, read through
   Road.cellsOf and Road.Alg.cG, have the same value at cell' and at cell, at every valid name. The
   matrices of qa and of the two streams have numbers above b's, whatever the feature.
3. "tiesG_of_layout": the ties Road.Alg.TiesG between the terms of Ends/G.lean and the library's
   arrays, for any cells, under the first four of the six premises.
4. "segG_congr": under the six premises and AgreeG, at a layer of the group on which the family is
   present, an entry of the family and a position: G.segG has the same value at cell' and at cell.
   By Road.Alg.TiesW.key_segG (G.segG is the library's key) and Road.key_agree (the library's key
   reads valid names alone).
5. "kvG_congr": under the six premises and AgreeG, G.kvG P g cell' q X = G.kvG P g cell q X for q
   below NC and X below 2^(n_q). "agree_withBG", "keysSkipB": withBG P g cell agrees with cell in
   that sense, so under the six premises KeysSkipB P g cell holds, for every cell.
6. "lawG_withBG": under the six premises, if for every call c below NC every place of G.kvG P g cell
   c holds the value of a row below 2^(k_c) of the call's table, then for all θ and al Cb.Lkp.MidP
   holds at G.keyG, G.tabG, FoNums.pads and G.bitsG, with keys and bits both read at withBG P g
   cell.

Limits. All six premises speak of public numbers. scalesHeld, g < NGr, p4 and the even dh are
premises of the statements that steps 3 and 4 call; this file does not show that kvG_congr fails
without them. Beyond the places below 2^(n_q) nothing is said. K is any field (with decidable
equality where withBG occurs). That the six premises hold of a parameter file is not shown here.

Not claimed: that a prover's committed cells are withBG P g cell for some cell; that the premise on
the keys holds of any request; that MidP makes any claim of the protocol's lookup argument hold;
completeness of the protocol.

-/
import Johnson.HonestTrace.CountsLayers
import Johnson.Road.Ends.AlgKey
import Johnson.Road.Ends.AlgTies
import Johnson.Road.FormsKeysValid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Layer (Lay layout scalesHeld)
open OnBytes.Road (Switches Laid Laid2 Sized dimOf sized_dimOf sclOf cellsOf Cells arrName segName
  listed matNo mxNo Tied)
open OnBytes.Road.Alg (cG TiesG TiesW wOfG tbG)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr Fam Mx)

/-! ## A feature in use lies in one of its family's parts -/

/-- If m / T and na are positive and F < off, then F divided by (the columns of a part, as
Layer.matrixSizes computes them from off, times m / T) is below na. -/
theorem part_lt {off m T na F : ℕ} (hu : 0 < m / T) (hna : 0 < na) (hF : F < off) :
    F / (roundUp off (na * (m / T)) / (na * (m / T)) * (m / T)) < na := by
  have hw : 0 < na * (m / T) := Nat.mul_pos hna hu
  rw [Road.roundUp_div off hw]
  have h1 : off ≤ (off + na * (m / T) - 1) / (na * (m / T)) * (na * (m / T)) :=
    (Road.ceil_le_iff hw).1 (le_refl _)
  apply Nat.div_lt_of_lt_mul
  calc F < off := hF
    _ ≤ (off + na * (m / T) - 1) / (na * (m / T)) * (na * (m / T)) := h1
    _ = (off + na * (m / T) - 1) / (na * (m / T)) * (m / T) * na := by ring

/-- In a layout with the facts Laid2, for μ below 3 (af, ad, ar): a feature F below the features in
use y.feat[μ] has F / (kcol[μ] * (mrow[μ] / T)) below parts[μ]. -/
theorem fam_part_lt {y : Lay} (L : Laid2 y) {μ F : ℕ} (hμ : μ < 3) (hF : F < y.feat.getD μ 0) :
    F / (y.kcol.getD μ 0 * (y.mrow.getD μ 0 / y.T)) < y.parts.getD μ 0 := by
  have two : 0 < 2 := by norm_num
  have hdiv : ∀ {a : ℕ}, y.h.lt ≤ a → 0 < 2 ^ a / 2 ^ y.h.lt := fun ha =>
    Nat.div_pos (Nat.pow_le_pow_right two ha) (by positivity)
  rw [L.T]
  rcases μ with _ | _ | _ | μ
  · rw [L.feat0] at hF
    rw [L.kcol0, L.mrow0, L.parts0]
    exact part_lt (hdiv L.lt_af) (Nat.pos_of_ne_zero L.NAf0) hF
  · rw [L.feat1] at hF
    rw [L.kcol1, L.mrow1, L.parts1]
    exact part_lt (hdiv L.lt_ad) (Nat.pos_of_ne_zero L.NAd0) hF
  · rw [L.feat2] at hF
    rw [L.kcol2, L.mrow2, L.parts2]
    exact part_lt (hdiv L.lt_ar) Nat.one_pos hF
  · omega

section Cells
variable {K : Type} [Field K]

/-- The readings cell' and cell agree at every name but the cells of matrix number G.iB P.y. -/
def AgreeG (P : Layer.Pub) (cell' cell : G.NameG → K) : Prop :=
  (∀ m r c, m ≠ G.iB P.y → cell' (.cell m r c) = cell (.cell m r c)) ∧
    ∀ r c, cell' (.w r c) = cell (.w r c)

/-- withBG P g cell and cell agree at every name but the cells of matrix number G.iB P.y. -/
theorem agree_withBG [DecidableEq K] (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) :
    AgreeG P (withBG P g cell) cell :=
  ⟨fun _ _ _ hm => if_neg hm, fun _ _ => rfl⟩

omit [Field K] in
/-- In a layout with the facts Laid2, under AgreeG P cell' cell: if F is below the features in use
whenever μ is below 3, then cG reads the same value at (μ, F, i) from cell' and from cell. -/
theorem cG_congr (P : Layer.Pub) {cell' cell : G.NameG → K} (A : AgreeG P cell' cell)
    (L : Laid2 P.y) {μ F : ℕ} (hF : μ < 3 → F < P.y.feat.getD μ 0) (i : ℕ) :
    cG P cell' μ F i = cG P cell μ F i := by
  unfold cG
  by_cases h4 : μ = 4
  · rw [if_pos h4, if_pos h4]
    have hne : G.iXI P.y + F / (P.y.kxb * (P.y.mxb / P.y.T)) ≠ G.iB P.y := by
      generalize F / (P.y.kxb * (P.y.mxb / P.y.T)) = d
      unfold G.iXI G.iB
      omega
    exact A.1 _ _ _ hne
  · rw [if_neg h4, if_neg h4]
    by_cases h5 : μ = 5
    · rw [if_pos h5, if_pos h5]
      have hne : G.iXO P.y + F / (P.y.kxb * (P.y.mxb / P.y.T)) ≠ G.iB P.y := by
        generalize F / (P.y.kxb * (P.y.mxb / P.y.T)) = d
        unfold G.iXO G.iB
        omega
      exact A.1 _ _ _ hne
    · rw [if_neg h5, if_neg h5]
      have hne : G.famM0 P.y μ + F / (P.y.kcol.getD μ 0 * (P.y.mrow.getD μ 0 / P.y.T)) ≠
          G.iB P.y := by
        by_cases h3 : μ < 3
        · have hp := fam_part_lt L h3 (hF h3)
          have p2 : P.y.parts.getD 2 0 = 1 := L.parts2
          have m0 : G.famM0 P.y 0 = 0 := rfl
          have m1 : G.famM0 P.y 1 = P.y.parts.getD 0 0 := rfl
          have m2 : G.famM0 P.y 2 = G.iAR P.y := rfl
          have eB : G.iB P.y = P.y.parts.getD 0 0 + P.y.parts.getD 1 0 + 1 := rfl
          have eR : G.iAR P.y = P.y.parts.getD 0 0 + P.y.parts.getD 1 0 := rfl
          obtain rfl | rfl | rfl : μ = 0 ∨ μ = 1 ∨ μ = 2 := by omega
          · rw [m0, eB]
            generalize F / (P.y.kcol.getD 0 0 * (P.y.mrow.getD 0 0 / P.y.T)) = d at hp ⊢
            omega
          · rw [m1, eB]
            generalize F / (P.y.kcol.getD 1 0 * (P.y.mrow.getD 1 0 / P.y.T)) = d at hp ⊢
            omega
          · rw [m2, eB, eR]
            generalize F / (P.y.kcol.getD 2 0 * (P.y.mrow.getD 2 0 / P.y.T)) = d at hp ⊢
            omega
        · have e0 : (μ == 0) = false := by simp; omega
          have e1 : (μ == 1) = false := by simp; omega
          have e2 : (μ == 2) = false := by simp; omega
          have m3 : G.famM0 P.y μ = G.iAR P.y + 2 := by
            unfold G.famM0
            rw [e0, e1, e2]
            rfl
          have eB : G.iB P.y = G.iAR P.y + 1 := rfl
          rw [m3, eB]
          generalize F / (P.y.kcol.getD μ 0 * (P.y.mrow.getD μ 0 / P.y.T)) = d
          omega
      exact A.1 _ _ _ hne

omit [Field K] in
/-- In a layout with the facts Laid2, under Switches, sizes D that agree with the shape and
AgreeG P cell' cell: at every valid name q, cellsOf D (cG P ·) has the same value at cell' and at
cell. -/
theorem cellsOf_congr {P : Layer.Pub} {cell' cell : G.NameG → K} (A : AgreeG P cell' cell)
    (L : Laid2 P.y) (S : Switches P.y.h) {D : Dim} (Z : Sized P.y.h D) (q : Cell)
    (hv : q.Valid D) : cellsOf D (cG P cell') q = cellsOf D (cG P cell) q := by
  obtain ⟨hk, hi, hj, -⟩ := hv
  have hφ := Inst.Model.FFSeg.IndexFacts.feat_lt D hk hi hj
  obtain ⟨f0, f1, f2, -⟩ := Road.feat_total L S Z
  refine cG_congr P A L (fun h3 => ?_) _
  cases hμ : q.X.mx <;> rw [hμ] at hφ h3
  · exact lt_of_lt_of_eq hφ f0.symm
  · exact lt_of_lt_of_eq hφ f1.symm
  · exact lt_of_lt_of_eq hφ f2.symm
  all_goals exact absurd h3 (by decide)

end Cells

/-! ## The ties between the terms of Ends/G.lean and the library's keys, for any cells -/

section Ties
variable {K : Type} [Field K]

/-- If Layer.layout returns P.y for its own shape, Switches holds, scalesHeld returns and g < NGr,
then TiesG holds of P, g and any cell, at the sizes dimOf P.y.h, the scales sclOf of the group and
the names of cells cellsOf (dimOf P.y.h) (cG P cell). -/
theorem tiesG_of_layout {P : Layer.Pub} {pc : List (List String)}
    (hy : layout P.y.h pc = .ok P.y) (S : Switches P.y.h)
    (hs : scalesHeld P.y.h P.sc = .ok ()) {g : ℕ} (hg : g < P.y.NGr) (cell : G.NameG → K) :
    TiesG (scl := sclOf P.y.h P.sc g P.y.Lam) P g cell (dimOf P.y.h)
      (cellsOf (dimOf P.y.h) (cG P cell)) := by
  letI : Scl := sclOf P.y.h P.sc g P.y.Lam
  have A := Road.admitted_of_layout hy S.p3
  have L := A.laid
  have Z := sized_dimOf P.y.h
  have hK := Road.K_on_group A hs hg
  have odd : ∀ lam, lam % 2 = 1 → (g * P.y.Lam + lam) % 2 = 1 := by
    intro lam ho
    obtain ⟨m, hm⟩ : ∃ m, P.y.Lam = 2 * m := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le L.ll
      exact ⟨2 ^ k, by rw [L.Lam, hk, pow_add, pow_one]⟩
    have e : g * P.y.Lam + lam = 2 * (g * m) + lam := by
      rw [hm]
      ring
    rw [e]
    omega
  have md : ∀ lam, lam < (dimOf P.y.h).nl →
      g * P.y.Lam + lam % P.y.Lam = g * P.y.Lam + lam := by
    intro lam hl
    have hl' : lam < P.y.Lam := by rw [L.Lam]; exact hl
    rw [Nat.mod_eq_of_lt hl']
  have vAll : ∀ X : Arr, listed X = true → ∀ inst j i : ℕ,
      Inst.Model.FFSeg.val (cellsOf (dimOf P.y.h) (cG P cell)) X inst j i =
        G.ten P cell (arrName X) inst j i + ((X.off : ℤ) : K) := by
    intro X hX inst j i
    obtain ⟨ten, hT, hm, hn, -⟩ := Road.ten_of L S X (Or.inl hX)
    have hm4 : ten.mat < 4 := by
      rw [hm]
      cases X <;> first | decide | exact absurd hX (by decide)
    exact Road.Alg.val_of_tied hT (Road.tied_cellsOf L S Z (cG P cell) (Or.inl hX) hT hn) hm4
      inst j i
  have hxl : P.y.xb.nl = 5 := by rw [L.xb]; exact S.xl
  have t0 : Tied (cG P cell) (cellsOf (dimOf P.y.h) (cG P cell)) .x0 4 P.y.xb :=
    ⟨hxl, fun k inst j i => by
      show cG P cell 4 (Inst.Model.FFSeg.feat (dimOf P.y.h) .x0 k inst j) i = _
      rw [(Road.xb_eq_feat L Z k inst j).1]⟩
  have t8 : Tied (cG P cell) (cellsOf (dimOf P.y.h) (cG P cell)) .x8 5 P.y.xb :=
    ⟨hxl, fun k inst j i => by
      show cG P cell 5 (Inst.Model.FFSeg.feat (dimOf P.y.h) .x8 k inst j) i = _
      rw [(Road.xb_eq_feat L Z k inst j).2]⟩
  have hLam : P.y.Lam = (dimOf P.y.h).nl := L.Lam
  refine
    { val := fun X hX inst j i => ?_
      xs := fun s j i _ => ?_
      p3 := S.p3, gcl := S.gcl, rcl := S.rcl, xl := S.xl, hq := S.hq
      hv := S.hv, ho := S.ho, hgD := S.hgD, huD := S.huD, hdD := S.hdD
      hr := S.hr, fe := rfl, NE := rfl, dq := L.dq
      kq := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lkq) (md lam hl).symm
      kk := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lkk) (md lam hl).symm
      kv := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lkv) (md lam hl).symm
      ko := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lko) (md lam hl).symm
      kg := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lkg) (md lam hl).symm
      ku := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lku) (md lam hl).symm
      kd := fun lam hl => congrArg (fun l => P.sc.kl l Layer.Lkd) (md lam hl).symm
      K1 := fun lam hl => congrArg (fun l => P.sc.kl l Layer.LK1) (md lam hl).symm
      K2 := fun lam hl => congrArg (fun l => P.sc.kl l Layer.LK2) (md lam hl).symm
      kr := fun lam hl ho => ?_, kgR := fun lam hl ho => ?_, kuR := fun lam hl ho => ?_
      K1le := fun lam hl => ?_, K2le := fun lam hl => ?_ }
  · exact vAll X (by cases X <;> first | rfl | exact absurd hX (by decide)) inst j i
  · unfold G.xs
    by_cases h0 : s = 0
    · subst h0
      have b0 : ((0 : ℕ) == 0) = true := rfl
      rw [b0, if_pos rfl, Road.xS_first]
      exact Road.Alg.raw_of_border t0 L.xb (fun _ _ => by unfold cG; rw [if_pos rfl]) j i
    · have b0 : (s == 0) = false := by simpa using h0
      rw [b0, if_neg Bool.false_ne_true]
      by_cases h1 : s = 2 * (dimOf P.y.h).nl
      · have b1 : (s == 2 * P.y.Lam) = true := by rw [hLam]; simpa using h1
        rw [b1, if_pos rfl, Road.xS_last _ _ h0 h1]
        exact Road.Alg.raw_of_border t8 L.xb
          (fun _ _ => by unfold cG; rw [if_neg (by decide), if_pos rfl]) j i
      · have b1 : (s == 2 * P.y.Lam) = false := by rw [hLam]; simpa using h1
        rw [b1, if_neg Bool.false_ne_true, Road.xS_mid _ _ h0 h1]
        unfold Road.raw
        rw [vAll .xs rfl]
        simp [arrName, Arr.off]
  · show _ = if (g * P.y.Lam + lam % P.y.Lam) % 2 = 1 then
      P.sc.klM (g * P.y.Lam + lam % P.y.Lam) 0 else 17
    rw [md lam hl, if_pos (odd lam ho)]
  · show _ = if (g * P.y.Lam + lam % P.y.Lam) % 2 = 1 then
      P.sc.klM (g * P.y.Lam + lam % P.y.Lam) 1 else 16
    rw [md lam hl, if_pos (odd lam ho)]
  · show _ = if (g * P.y.Lam + lam % P.y.Lam) % 2 = 1 then
      P.sc.klM (g * P.y.Lam + lam % P.y.Lam) 2 else 20
    rw [md lam hl, if_pos (odd lam ho)]
  · show 16 ≤ P.sc.kl (g * P.y.Lam + lam % P.y.Lam) Layer.LK1
    rw [md lam hl]
    exact (hK lam hl).1
  · show 16 ≤ P.sc.kl (g * P.y.Lam + lam % P.y.Lam) Layer.LK2
    rw [md lam hl]
    exact (hK lam hl).2

end Ties

/-! ## The keys at the places below 2^(n_q) do not read the planes' matrix -/

section Skip
variable {K : Type} [Field K]

/-- Under AgreeG P cell' cell, the weights that Road.Alg.wOfG reads are the same at cell' and at
cell. -/
theorem wOfG_congr (P : Layer.Pub) (g : ℕ) {cell' cell : G.NameG → K} (A : AgreeG P cell' cell) :
    wOfG P g cell' = wOfG P g cell := by
  have e : G.wt P cell' = G.wt P cell := by
    funext X l idx
    simp only [G.wt, A.2]
  funext l
  simp only [wOfG, e]

/-- If Layer.layout P.y.h pc returns P.y, Switches P.y.h holds, scalesHeld P.y.h P.sc returns,
g < P.y.NGr, P.y.h.p4 = true, P.y.h.dh is even and AgreeG P cell' cell holds: for lam < Lam with the
family s present on layer lam, x below the family's length and i < T,
G.segG P g · (segName s) lam x i has the same value at cell' and at cell. -/
theorem segG_congr {P : Layer.Pub} {pc : List (List String)}
    (hy : layout P.y.h pc = .ok P.y) (S : Switches P.y.h)
    (hs : scalesHeld P.y.h P.sc = .ok ()) {g : ℕ} (hg : g < P.y.NGr)
    (hp4 : P.y.h.p4 = true) (hev : P.y.h.dh % 2 = 0) {cell' cell : G.NameG → K}
    (A' : AgreeG P cell' cell) (s : Fam)
    {lam x i : ℕ} (hl : lam < P.y.Lam) (hp : Inst.Model.FFSeg.present s lam = true)
    (hx : x < Inst.Model.FFSeg.len (dimOf P.y.h) s) (hi : i < P.y.T) :
    G.segG P g cell' (segName s) lam x i = G.segG P g cell (segName s) lam x i := by
  letI : Scl := sclOf P.y.h P.sc g P.y.Lam
  have A := Road.admitted_of_layout hy S.p3
  have L := A.laid
  have L2 := Road.laid2_of_layout hy
  have Z := sized_dimOf P.y.h
  obtain ⟨ten, hTo, hmo, hno, -⟩ := Road.ten_of L S .o (Or.inr ⟨rfl, hp4⟩)
  have hm4 : ten.mat < 4 := by
    rw [hmo]
    decide
  have tA := tiesG_of_layout hy S hs hg cell
  have tB := tiesG_of_layout hy S hs hg cell'
  have wA := Road.Alg.tiesW_of_laid g cell L S Z hp4 (Or.inr ⟨rfl, hp4⟩) hTo hno hm4 hev
  have wB := Road.Alg.tiesW_of_laid g cell' L S Z hp4 (Or.inr ⟨rfl, hp4⟩) hTo hno hm4 hev
  have hl' : lam < (dimOf P.y.h).nl := by
    have e : P.y.Lam = (dimOf P.y.h).nl := L.Lam
    rw [← e]
    exact hl
  have hi' : i < (dimOf P.y.h).T := by
    rw [← Road.T_eq L2 Z]
    exact hi
  rw [← wB.key_segG tB s lam x i hl' hp, ← wA.key_segG tA s lam x i hl' hp, wOfG_congr P g A']
  exact Road.key_agree (fun c hc => cellsOf_congr A' L2 S Z c hc) (Road.f_two_fe hy S Z)
    (tbG P) _ _ hl' hp hx hi'

/-- If f and f' agree at the segment, layer, entry and token of place X wherever G.colG finds a
segment that is present on the layer, then G.kvOf P f q X = G.kvOf P f' q X. -/
theorem kvOf_congr (P : Layer.Pub) (f f' : String → ℕ → ℕ → ℕ → K) (q X : ℕ)
    (h : ∀ s x, G.colG P.y q (X / P.y.T % 2 ^ (P.y.calls.getD q default).lJ) = some (s, x) →
      (s.moe && X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ % 2 == 0) = false →
      f s.name (X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ) x (X % P.y.T) =
        f' s.name (X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ) x (X % P.y.T)) :
    G.kvOf P f q X = G.kvOf P f' q X := by
  simp only [G.kvOf]
  cases hc : G.colG P.y q (X / P.y.T % 2 ^ (P.y.calls.getD q default).lJ) with
  | none => rfl
  | some a =>
    obtain ⟨s, x⟩ := a
    simp only
    cases hm : (s.moe && X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ % 2 == 0) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      exact h s x hc hm

/-- **The keys do not read the matrix b.** If Layer.layout h pc returns P.y, Switches h holds,
scalesHeld h P.sc returns, g < P.y.NGr, h.p4 = true and h.dh is even, then two readings cell' and
cell that agree at every name but the cells of matrix number G.iB P.y give the same key
G.kvG P g · q X, for every call q below NC and every place X below 2^(n_q). -/
theorem kvG_congr {h : Layer.Shape} {pc : List (List String)} {P : Layer.Pub}
    (hy : layout h pc = .ok P.y) (S : Switches h) (hs : scalesHeld h P.sc = .ok ()) {g : ℕ}
    (hg : g < P.y.NGr) (hp4 : h.p4 = true) (hev : h.dh % 2 = 0) {cell' cell : G.NameG → K}
    (A' : AgreeG P cell' cell) {q : ℕ} (hq : q < P.y.fo.NC) {X : ℕ}
    (hX : X < 2 ^ FoNums.nOf P.y.fo q) : G.kvG P g cell' q X = G.kvG P g cell q X := by
  have e := (Road.admitted_of_layout hy S.p3).shape
  subst e
  have A := Road.admitted_of_layout hy S.p3
  have L2 := Road.laid2_of_layout hy
  have hNC : P.y.fo.NC = P.y.calls.size :=
    (Road.fo_of_layout hy).2.1.trans (Road.fo_of_layout hy).2.2
  have hq' : q < P.y.calls.size := by omega
  obtain ⟨-, hn, -⟩ := call_facts hy S hq'
  have hlam : X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ < P.y.Lam := by
    rw [hn] at hX
    rw [A.laid.Lam, L2.T]
    apply Nat.div_lt_of_lt_mul
    apply Nat.div_lt_of_lt_mul
    calc X < 2 ^ (P.y.h.ll + (P.y.calls.getD q default).lJ + P.y.h.lt) := hX
      _ = 2 ^ P.y.h.lt * (2 ^ (P.y.calls.getD q default).lJ * 2 ^ P.y.h.ll) := by
        rw [pow_add, pow_add]
        ring
  have hi : X % P.y.T < P.y.T := Nat.mod_lt _ (by rw [L2.T]; positivity)
  have hcd : P.y.calls.getD q default ∈ P.y.calls := by
    apply Array.mem_of_getElem? (i := q)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq']
    rfl
  refine kvOf_congr P _ _ q X fun s x hc hm => ?_
  unfold G.colG at hc
  obtain ⟨s0, hs0, h0⟩ := List.exists_of_findSome?_eq_some hc
  cases hx0 : s0.pos.findIdx? (· == X / P.y.T % 2 ^ (P.y.calls.getD q default).lJ) with
  | none =>
    rw [hx0] at h0
    cases h0
  | some x0 =>
    rw [hx0] at h0
    have e : (s0, x0) = (s, x) := Option.some.inj h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    obtain ⟨hix, -, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx0
    obtain ⟨fam, a1, a2, a3, a4, -⟩ := Road.segs_of_layout hy S _ hcd s0 hs0
    have hpres : Inst.Model.FFSeg.present fam
        (X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ) = true := by
      have e1 := Road.Alg.moe_present fam (X / P.y.T / 2 ^ (P.y.calls.getD q default).lJ)
      rw [← a3, hm] at e1
      simpa using e1.symm
    rw [a1]
    exact segG_congr hy S hs hg hp4 hev A' fam hlam hpres (by rw [← a2, ← a4]; exact hix) hi

/-- If Layer.layout h pc returns P.y, Switches h holds, scalesHeld h P.sc returns, g < P.y.NGr,
h.p4 = true and h.dh is even, then KeysSkipB P g cell holds for every cell: for every call q below
NC and every place X below 2^(n_q), G.kvG reads the same value at withBG P g cell and at cell. -/
theorem keysSkipB [DecidableEq K] {h : Layer.Shape} {pc : List (List String)} {P : Layer.Pub}
    (hy : layout h pc = .ok P.y) (S : Switches h) (hs : scalesHeld h P.sc = .ok ()) {g : ℕ}
    (hg : g < P.y.NGr) (hp4 : h.p4 = true) (hev : h.dh % 2 = 0) (cell : G.NameG → K) :
    KeysSkipB P g cell :=
  fun _ hq _ hX => kvG_congr hy S hs hg hp4 hev (agree_withBG P g cell) hq hX

/-- Under the premises of keysSkipB: if for every call c below NC every place of G.kvG P g cell c
holds the value of a row below 2^(k_c) of tabOf, then for all θ and al Cb.Lkp.MidP holds at
G.keyG P g (withBG P g cell) θ, G.tabG P θ, FoNums.pads P.y.fo and the bits
G.bitsG P.y (withBG P g cell) (u * 32 + j). -/
theorem lawG_withBG [DecidableEq K] {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (hs : scalesHeld h P.sc = .ok ()) {g : ℕ}
    (hg : g < P.y.NGr) (hp4 : h.p4 = true) (hev : h.dh % 2 = 0) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c)) (θ al : K) :
    Cb.Lkp.MidP P.y.fo.v P.y.fo.d 5 32 (G.keyG P g (withBG P g cell) θ) (G.tabG P θ)
      (FoNums.pads P.y.fo) (fun u j => G.bitsG P.y (withBG P g cell) (u * 32 + j)) al :=
  lawG P hy S g _ (inTable_withBG P g cell (keysSkipB hy S hs hg hp4 hev cell) hin)
    (withBG_laid P g cell (keysSkipB hy S hs hg hp4 hev cell)) θ al

end Skip

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.part_lt
#print axioms OnBytes.HonestTrace.fam_part_lt
#print axioms OnBytes.HonestTrace.agree_withBG
#print axioms OnBytes.HonestTrace.cG_congr
#print axioms OnBytes.HonestTrace.cellsOf_congr
#print axioms OnBytes.HonestTrace.tiesG_of_layout
#print axioms OnBytes.HonestTrace.wOfG_congr
#print axioms OnBytes.HonestTrace.segG_congr
#print axioms OnBytes.HonestTrace.kvOf_congr
#print axioms OnBytes.HonestTrace.kvG_congr
#print axioms OnBytes.HonestTrace.keysSkipB
#print axioms OnBytes.HonestTrace.lawG_withBG
