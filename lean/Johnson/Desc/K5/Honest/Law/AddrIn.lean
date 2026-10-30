-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/AddrIn.lean: CONDITIONAL: EVERY VALID NAME OF A CELL OF AN ATTENTION
SEGMENT HAS ITS ADDRESS INSIDE ITS MATRIX. The library's rule of addresses (`addrA`,
Johnson/Road/Lane5AttDef.lean) lays a name at a number in the smallness test's list of matrices, a
row and a column. Shown here, for every shape that the planner of shapes returns: at a valid name
the number is not that of the matrix of the lookup's planes, the row is below the matrix's rows and
the column below its columns. A definition of a premise, and statements with their proofs;
arithmetic on the shape's numbers.

Why. The ties between a witness's matrices and the prover's cells speak of places inside the
matrices alone.

Main names:
  `dvd_roundUp`, `feat_inside`   numbers
  `ColsFit`, `colsFit_of_plan`   the columns of the matrices ah, ao and qa; a plan that the planner
                                 returns
                     has them
  `addr_inside`      **the statement**, name by name over the eleven sorts of names
  `addr_inside_ofPlan`   the same at a plan that is the planner's but for one field

EVERY STATEMENT BUT THE TWO ON NUMBERS IS CONDITIONAL; ALL PREMISES ARE PUBLIC: the shape is the
planner's return; the list's rows (`MatsFit`, Johnson/Road/Rows/AttRead.lean) and columns
(`ColsFit`) are the shape's; there is a part of the matrix "as"; a column of ah holds a feature: the
planner of shapes tests neither; both follow from `PosG`
(Johnson/Desc/First/Att/Claims/TablesSpec.lean).
By the tree's arithmetic on the planner's text (Johnson/Desc/First/Att/Claims/PlacesNum.lean:
`Fills`, `le_roundUp`, `idx_lt`, `pair_lt`, `ten_top`, `as_room`, `placeRow_lt`) and `plan_mats`
(Johnson/Road/Lane5AttLabel.lean).
Limits. That `addrA` is the program's rule is shown by no theorem. Nothing is said of which places
are hit, nor that two names have two addresses (on that: Johnson/Road/Lane5AttInj.lean). No property
is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.PlacesNum
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.First.Att.Claims.TablesSpec
import Johnson.Desc.First.Att.GuardPlan
import Johnson.Desc.First.Att.K05HostPlanesPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open Inst.Model.AttSeg (Raw)
open K5Law (Fills idx_lt le_roundUp pair_lt ten_top as_room placeRow_lt)

/-! ## Numbers -/

/-- A number rounded up to a multiple of w is a multiple of w. -/
theorem dvd_roundUp (x w : ℕ) : w ∣ roundUp x w := by
  unfold roundUp
  exact Dvd.intro_left _ rfl

/-- Feature φ at token i lies inside a matrix with wc features a column, T rows a feature, that is
filled up to F features, F a multiple of wc. -/
theorem feat_inside {wc φ i T F : ℕ} (hw : 0 < wc) (hi : i < T) (hφ : φ < F) (hF : wc ∣ F) :
    φ % wc * T + i < wc * T ∧ φ / wc < F / wc := by
  exact ⟨idx_lt (Nat.mod_lt _ hw) hi, Nat.div_lt_div_of_lt_of_dvd hF hφ⟩

/-! ## The columns of three matrices -/

/-- **The premise on the columns**: the matrices ah, ao and qa of the smallness test's list have the
columns that the shape's numbers of filled features give them. Public. The rows stand in the tree's
`MatsFit` (Johnson/Road/Rows/AttRead.lean). -/
structure ColsFit (S : Attention.Shape) (tl : HTailF2) : Prop where
  ah : (tl.mats.getD S.cf.NAs {}).k = S.fillH / S.cf.wcH
  ao : (tl.mats.getD (S.cf.NAs + 1) {}).k = S.fillO / S.cf.wcO
  qa : (tl.mats.getD (S.cf.NAs + 3) {}).k = S.fillQ / S.cf.wcQ

/-- A plan that the planner returns has them. -/
theorem colsFit_of_plan {settings : Model.Settings} {j : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings j cf = Except.ok X) :
    ColsFit X.S X.seam.tl := by
  have hm := OnBytes.Road.L5.plan_mats h
  have tailAt : ∀ k : ℕ, (Attention.matrices X.S X.inp)[X.S.cf.NAs + k]? =
      (#[Attention.ownMatrix X.inp "ah" (X.S.cf.wcH * X.S.T) (X.S.fillH / X.S.cf.wcH) X.S.cf.NAs
          X.inp.wph,
        Attention.ownMatrix X.inp "ao" (X.S.cf.wcO * X.S.T) (X.S.fillO / X.S.cf.wcO)
          (X.S.cf.NAs + 1) X.inp.wpo,
        Attention.ownMatrix X.inp "bA" (2 ^ X.S.cf.lmb) X.S.kbA (X.S.cf.NAs + 2) X.inp.wpbA,
        { name := "qa", m := X.S.cf.wcQ * X.S.T, k := X.S.fillQ / X.S.cf.wcQ, kind := 1,
          foreign := some 0, aId := X.inp.midQ, wp := X.inp.wpq }] : Array Model.TMat)[k]? := by
    intro k
    unfold Attention.matrices
    exact OnBytes.Road.L5.append_at _ _ k (by simp)
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      show X.S.cf.NAs = X.S.cf.NAs + 0 from rfl, tailAt 0]
    rfl
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map, tailAt 1]
    rfl
  · rw [hm, Array.getD_eq_getD_getElem?, Array.getElem?_map, tailAt 3]
    rfl

/-! ## Every valid name's address lies inside its matrix -/

/-- **The library's rule of addresses (`addrA`, Johnson/Road/Lane5AttDef.lean) lays every valid name
of a cell inside its matrix, which is not the matrix of the lookup's planes.** CONDITIONAL on: the
shape is the planner's; the list's rows and columns are the shape's (`MatsFit`, `ColsFit`); hN:
there is a part of the matrix "as"; hw: a column of ah holds a feature. All public. That a column of
ao and of qa holds a feature is a test of the planner of shapes (`Fills`, Claims/PlacesNum.lean). -/
theorem addr_inside {S : Attention.Shape} {tl : HTailF2} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = .ok (S, fs)) (Mf : MatsFit S tl)
    (Cf : ColsFit S tl) (hN : 0 < S.cf.NAs) (hw : 0 < S.cf.wcH) :
    ∀ q : Raw, q.Valid (L5.dimOf S) →
      (L5.addrA S q).1 ≠ S.cf.NAs + 2 ∧
      (L5.addrA S q).2.1 < (tl.mats.getD (L5.addrA S q).1 {}).m ∧
        (L5.addrA S q).2.2 < (tl.mats.getD (L5.addrA S q).1 {}).k := by
  have Sh := L5.shaped_of_hid hid
  have F := K5Law.fills_of_hid hid
  have N := norm_of_hid hid
  have Z := sizes_of_hid hid
  have hc := Sh.cfg
  have hL : S.Lam = 2 ^ cf.ll := Sh.Lam
  have hdh : S.dh = 2 ^ S.cf.ldh := by rw [Sh.dh, hc]
  have hwH : 0 < cf.wcH := by rw [← hc]; exact hw
  have hwO : 0 < S.cf.wcO := by rw [hc]; exact F.wcO
  have hwQ : 0 < S.cf.wcQ := by rw [hc]; exact F.wcQ
  have hlT : (L5.dimOf S).lT = S.cf.lt := N.lt.symm
  have hT : (L5.dimOf S).T = S.T := by
    rw [Inst.Model.AttSeg.Dim.T_eq, hlT, Z.T]
  have dH : S.cf.wcH ∣ S.fillH := by rw [F.fillH, hc]; exact dvd_roundUp _ _
  have dO : S.cf.wcO ∣ S.fillO := by rw [F.fillO, hc]; exact dvd_roundUp _ _
  have dQ : S.cf.wcQ ∣ S.fillQ := by rw [F.fillQ, hc]; exact dvd_roundUp _ _
  have fQ := le_roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
    2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) F.wcQ
  rw [← F.fillQ] at fQ
  have fO := le_roundUp (2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh)) F.wcO
  rw [← F.fillO] at fO
  have two : 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) =
      2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) := by ring
  -- the three matrices of features
  have inH : ∀ φ i, φ < S.fillH → i < S.T →
      (L5.featCell S S.cf.NAs S.cf.wcH φ i).1 ≠ S.cf.NAs + 2 ∧
      (L5.featCell S S.cf.NAs S.cf.wcH φ i).2.1 <
        (tl.mats.getD (L5.featCell S S.cf.NAs S.cf.wcH φ i).1 {}).m ∧
      (L5.featCell S S.cf.NAs S.cf.wcH φ i).2.2 <
        (tl.mats.getD (L5.featCell S S.cf.NAs S.cf.wcH φ i).1 {}).k := by
    intro φ i hφ hi
    obtain ⟨a, b⟩ := feat_inside hw hi hφ dH
    refine ⟨?_, ?_, ?_⟩
    · show S.cf.NAs ≠ S.cf.NAs + 2
      omega
    · show φ % S.cf.wcH * S.T + i < (tl.mats.getD S.cf.NAs {}).m
      rw [Mf.ahM]
      exact a
    · show φ / S.cf.wcH < (tl.mats.getD S.cf.NAs {}).k
      rw [Cf.ah]
      exact b
  have inO : ∀ φ i, φ < S.fillO → i < S.T →
      (L5.featCell S (S.cf.NAs + 1) S.cf.wcO φ i).1 ≠ S.cf.NAs + 2 ∧
      (L5.featCell S (S.cf.NAs + 1) S.cf.wcO φ i).2.1 <
        (tl.mats.getD (L5.featCell S (S.cf.NAs + 1) S.cf.wcO φ i).1 {}).m ∧
      (L5.featCell S (S.cf.NAs + 1) S.cf.wcO φ i).2.2 <
        (tl.mats.getD (L5.featCell S (S.cf.NAs + 1) S.cf.wcO φ i).1 {}).k := by
    intro φ i hφ hi
    obtain ⟨a, b⟩ := feat_inside hwO hi hφ dO
    refine ⟨?_, ?_, ?_⟩
    · show S.cf.NAs + 1 ≠ S.cf.NAs + 2
      omega
    · show φ % S.cf.wcO * S.T + i < (tl.mats.getD (S.cf.NAs + 1) {}).m
      rw [Mf.aoM]
      exact a
    · show φ / S.cf.wcO < (tl.mats.getD (S.cf.NAs + 1) {}).k
      rw [Cf.ao]
      exact b
  have inQ : ∀ φ i, φ < S.fillQ → i < S.T →
      (L5.featCell S (S.cf.NAs + 3) S.cf.wcQ φ i).1 ≠ S.cf.NAs + 2 ∧
      (L5.featCell S (S.cf.NAs + 3) S.cf.wcQ φ i).2.1 <
        (tl.mats.getD (L5.featCell S (S.cf.NAs + 3) S.cf.wcQ φ i).1 {}).m ∧
      (L5.featCell S (S.cf.NAs + 3) S.cf.wcQ φ i).2.2 <
        (tl.mats.getD (L5.featCell S (S.cf.NAs + 3) S.cf.wcQ φ i).1 {}).k := by
    intro φ i hφ hi
    obtain ⟨a, b⟩ := feat_inside hwQ hi hφ dQ
    refine ⟨?_, ?_, ?_⟩
    · show S.cf.NAs + 3 ≠ S.cf.NAs + 2
      omega
    · show φ % S.cf.wcQ * S.T + i < (tl.mats.getD (S.cf.NAs + 3) {}).m
      rw [Mf.qaM]
      exact a
    · show φ / S.cf.wcQ < (tl.mats.getD (S.cf.NAs + 3) {}).k
      rw [Cf.qa]
      exact b
  -- the matrix "as"
  have room := as_room Sh hN
  have inA : ∀ n, n < 5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) →
      (L5.asCell S n).1 ≠ S.cf.NAs + 2 ∧
      (L5.asCell S n).2.1 < (tl.mats.getD (L5.asCell S n).1 {}).m ∧
      (L5.asCell S n).2.2 < (tl.mats.getD (L5.asCell S n).1 {}).k := by
    intro n hn
    have h1 : n < S.cf.NAs * (S.kAs / S.cf.NAs) * 2 ^ S.cf.lmS := Nat.lt_of_lt_of_le hn room
    have h2 : n / 2 ^ S.cf.lmS < S.cf.NAs * (S.kAs / S.cf.NAs) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)
    have hq : 0 < S.kAs / S.cf.NAs := by
      rcases Nat.eq_zero_or_pos (S.kAs / S.cf.NAs) with h0 | h0
      · rw [h0, Nat.mul_zero] at h2
        exact absurd h2 (Nat.not_lt_zero _)
      · exact h0
    have h3 : n / 2 ^ S.cf.lmS / (S.kAs / S.cf.NAs) < S.cf.NAs :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h2)
    obtain ⟨em, ek⟩ := Mf.asM _ h3
    refine ⟨?_, ?_, ?_⟩
    · show n / 2 ^ S.cf.lmS / (S.kAs / S.cf.NAs) ≠ S.cf.NAs + 2
      omega
    · show n % 2 ^ S.cf.lmS < (tl.mats.getD (n / 2 ^ S.cf.lmS / (S.kAs / S.cf.NAs)) {}).m
      rw [em]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show n / 2 ^ S.cf.lmS % (S.kAs / S.cf.NAs) <
        (tl.mats.getD (n / 2 ^ S.cf.lmS / (S.kAs / S.cf.NAs)) {}).k
      rw [ek]
      exact Nat.mod_lt _ hq
  have dist : 5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) =
      5 * S.Lam * S.HA * 2 ^ S.nM + 5 * S.Lam * S.HA * 2 ^ S.nD := by ring
  intro q hq
  match q, hq with
  | .c .M jj b x, ⟨hj, hb, hx⟩ =>
    obtain ⟨h1, h2, _⟩ := pair_lt Sh F hb (g := 0) (Nat.two_pow_pos _)
    have hx' : x < 2 ^ S.nM := by rw [N.nM]; exact hx
    have a := idx_lt (idx_lt (idx_lt hj h1) h2) hx'
    exact inA _ (by rw [dist]; omega)
  | .c .D jj b x, ⟨hj, hb, hx⟩ =>
    obtain ⟨h1, h2, _⟩ := pair_lt Sh F hb (g := 0) (Nat.two_pow_pos _)
    have hx' : x < 2 ^ S.nD := by rw [N.nD]; exact hx
    have a := idx_lt (idx_lt (idx_lt hj h1) h2) hx'
    exact inA _ (by rw [dist]; omega)
  | .mx k b g i, ⟨hk, hb, hg, hi⟩ =>
    exact inH _ _ ((placeRow_lt Sh F hwH hlT hb hg).1 k hk) (by rw [← hT]; exact hi)
  | .den k b g i, ⟨hk, hb, hg, hi⟩ =>
    exact inH _ _ ((placeRow_lt Sh F hwH hlT hb hg).2.1 k hk) (by rw [← hT]; exact hi)
  | .ib k b g i, ⟨hk, hb, hg, hi⟩ =>
    exact inH _ _ ((placeRow_lt Sh F hwH hlT hb hg).2.2 k hk) (by rw [← hT]; exact hi)
  | .qh b g i n, ⟨hb, hg, hi, hn⟩ =>
    obtain ⟨h1, _, h3⟩ := pair_lt Sh F hb hg
    have hn' : n < S.dh := by rw [hdh]; exact hn
    have t := ten_top (Attention.atRh S) (l := 0) (lam := b / S.HA) (dh := S.dh) (nH := S.cf.H)
      (by show 0 < 1; norm_num) h1 (by show S.dq = _; rw [Sh.dq, hdh, hc]) h3
    have t' : Model.tenCell (Attention.atRh S) 0 (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + S.dh ≤
        S.oRh + 1 * S.Lam * S.dq := t
    rw [Sh.oRh, Sh.dq, hL, Nat.one_mul] at t'
    exact inO _ _ (by omega) (by rw [← hT]; exact hi)
  | .qh' b g i n, ⟨hb, hg, hi, hn⟩ =>
    obtain ⟨h1, _, h3⟩ := pair_lt Sh F hb hg
    have hn' : n < S.dh := by rw [hdh]; exact hn
    have t := ten_top (Attention.atRhp S) (l := 0) (lam := b / S.HA) (dh := S.dh) (nH := S.cf.H)
      (by show 0 < 1; norm_num) h1 (by show S.dq = _; rw [Sh.dq, hdh, hc]) h3
    have t' : Model.tenCell (Attention.atRhp S) 0 (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) +
        S.dh ≤ S.oRhp + 1 * S.Lam * S.dq := t
    rw [Sh.oRhp, Sh.dq, hL, Nat.one_mul] at t'
    exact inO _ _ (by omega) (by rw [← hT]; exact hi)
  | .qry k b g i n, ⟨hk, hb, hg, hi, hn⟩ =>
    obtain ⟨h1, _, h3⟩ := pair_lt Sh F hb hg
    have hn' : n < S.dh := by rw [hdh]; exact hn
    have t := ten_top S.atQ (l := k) (lam := b / S.HA) (dh := S.dh) (nH := S.cf.H)
      (by rw [Sh.atQ]; exact hk) (by rw [Sh.atQ, ← hL]; exact h1) (by rw [Sh.atQ, hdh, hc]) h3
    have e : S.atQ.off + S.atQ.nl * S.atQ.cnt * S.atQ.J =
        0 + 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) := by rw [Sh.atQ]
    rw [e] at t
    exact inQ _ _ (by omega) (by rw [← hT]; exact hi)
  | .out k b g i n, ⟨hk, hb, hg, hi, hn⟩ =>
    obtain ⟨h1, _, h3⟩ := pair_lt Sh F hb hg
    have hn' : n < S.dh := by rw [hdh]; exact hn
    have t := ten_top S.atO (l := k) (lam := b / S.HA) (dh := S.dh) (nH := S.cf.H)
      (by rw [Sh.atO]; exact hk) (by rw [Sh.atO, ← hL]; exact h1) (by rw [Sh.atO, hdh, hc]) h3
    have e : S.atO.off + S.atO.nl * S.atO.cnt * S.atO.J =
        2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
          2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) := by
      rw [Sh.atO]
    rw [e] at t
    exact inQ _ _ (by omega) (by rw [← hT]; exact hi)
  | .key k lam g j n, ⟨hk, hl, hg, hj, hn⟩ =>
    have hl' : lam < S.Lam := hl
    have hg' : g < 2 ^ S.cf.lgk := hg
    have hn' : n < S.dh := by rw [hdh]; exact hn
    have t := ten_top S.atK (l := k) (lam := lam) (dh := S.dh) (nH := 2 ^ S.cf.lgk)
      (by rw [Sh.atK]; exact hk) (by rw [Sh.atK, ← hL]; exact hl') (by rw [Sh.atK, hdh, hc]) hg'
    have e : S.atK.off + S.atK.nl * S.atK.cnt * S.atK.J =
        2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) := by
      rw [Sh.atK]
    rw [e] at t
    exact inQ _ _ (by omega) (by rw [← hT]; exact hj)
  | .val k lam g j n, ⟨hk, hl, hg, hj, hn⟩ =>
    have hl' : lam < S.Lam := hl
    have hg' : g < 2 ^ S.cf.lgk := hg
    have hn' : n < S.dh := by rw [hdh]; exact hn
    have t := ten_top S.atV (l := k) (lam := lam) (dh := S.dh) (nH := 2 ^ S.cf.lgk)
      (by rw [Sh.atV]; exact hk) (by rw [Sh.atV, ← hL]; exact hl') (by rw [Sh.atV, hdh, hc]) hg'
    have e : S.atV.off + S.atV.nl * S.atV.cnt * S.atV.J =
        2 * 2 ^ cf.ll * (cf.H * 2 ^ cf.ldh) + 2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) +
          2 * 2 ^ cf.ll * (2 ^ cf.lgk * 2 ^ cf.ldh) := by
      rw [Sh.atV]
    rw [e] at t
    exact inQ _ _ (by omega) (by rw [← hT]; exact hj)

/-- **The same at a plan that is the planner's but for one field of the smallness test's numbers**
(`OfPlan`, Johnson/Desc/First/Att/Claims/OfPlan.lean: the field is the list of places, not the list
of matrices). CONDITIONAL on that, and on: six numbers of the shape are not 0 (`PosG`,
Claims/TablesSpec.lean), of which two are spent. Public. -/
theorem addr_inside_ofPlan {A : Attention.Plan} (hA : K5Law.OfPlan A)
    (hpos : K5Law.PosG (P.geoOf A.S)) :
    ∀ q : Raw, q.Valid (L5.dimOf A.S) →
      (L5.addrA A.S q).1 ≠ A.S.cf.NAs + 2 ∧
      (L5.addrA A.S q).2.1 < (A.seam.tl.mats.getD (L5.addrA A.S q).1 {}).m ∧
        (L5.addrA A.S q).2.2 < (A.seam.tl.mats.getD (L5.addrA A.S q).1 {}).k := by
  obtain ⟨lid, cf, hid⟩ := K5Law.ofPlan_shape hA
  have Mf := K5Law.ofPlan_matsFit hA
  have Cf : ColsFit A.S A.seam.tl := by
    obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := hA
    obtain ⟨c1, c2, c3⟩ := colsFit_of_plan h0
    exact ⟨c1, c2, c3⟩
  have hN : 0 < A.S.cf.NAs := hpos.nas
  have hw : 0 < A.S.cf.wcH := by
    rcases Nat.eq_zero_or_pos A.S.cf.wcH with h0 | h0
    · have hf : 0 < A.S.fillH := hpos.fillH
      have F := K5Law.fills_of_hid hid
      have hc := (L5.shaped_of_hid hid).cfg
      rw [F.fillH, ← hc, h0] at hf
      unfold roundUp at hf
      rw [Nat.mul_zero] at hf
      exact absurd hf (Nat.lt_irrefl _)
    · exact h0
  exact addr_inside hid Mf Cf hN hw

end H2K5.Honest

#print axioms H2K5.Honest.dvd_roundUp
#print axioms H2K5.Honest.feat_inside
#print axioms H2K5.Honest.colsFit_of_plan
#print axioms H2K5.Honest.addr_inside
#print axioms H2K5.Honest.addr_inside_ofPlan
