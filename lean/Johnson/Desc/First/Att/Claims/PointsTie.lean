-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PointsTie.lean: kind K5: the points that pointsOf
(Johnson/Desc/First/Att/Points.lean) cuts out of the lookup calls' key points ARE the library's
points (Inst/Model/Att/Points.lean), coordinate by coordinate.

Why it holds. A call's key point is (some coordinates of the lookup's tree part | zx), zx the
lookup's point inside a tree. A unit's inner point is the last "bits" coordinates of its call's key
point; where a piece is no longer than a tree, that is a tail of zx. The library's inner point of a
family is the same tail of z_in (inn_tail, Inst/Model/Att/KeyFormsExt/Calls14.lean). So
each side's named point is a stretch of zx, and the tie is a sum of lengths.

Main names:
  `Look ρ fs zx p`: zx has the tree's depth dT as its length, and the library's z reads as zx on
    its first dT coordinates.
  `inner_tail`: the kind's inner point of a unit, read, is a tail of zx.
  `inn_zx`: the library's inner point of a family at C := callsOf fs is the same tail.
  `Cut5 g zk p`, `cut5_of`: what pointsOf lays into the division's points: cuts of the inner points
    of the three units wl, ix, wh, with their lengths.
  `tie_wl`, `tie_ix`, `tie_wh`: zsl is zChi; zgW, ziW, zcW are yg, yi, yn; zgX, ziX are xg, xi; zgH,
    ziH, zcH are yg, yi, yn again (the library cuts these from the family w3 alone).
Premises: CallsFit S fs (Johnson/Road/Lane5CallsOf.lean: a decidable test on public numbers); Look;
each of the three calls' key points ends in zx (`EndsIn`); the shape's lt is the library's lT.
Used: inn_tail; pt, pt_extract; callsFit_deep; guard_some (PointsRows.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Inst.Model.Att.KeyFormsExt.Calls14
import Johnson.Road.Lane5CallsOf
import Johnson.Road.Rows.AttEnds58Proofs
import Johnson.Desc.First.Att.Claims.PointsMore

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts UnitG geoOf)
open Inst.Model.AttSeg (Pub Fam inn sh zChi yg yi yn xg xi uW uX)

variable {Kf : Type} [Field Kf]

/-! ## The two sides as tails of zx -/

/-- The lookup's point inside a tree, and the library's z on its first coordinates. -/
structure Look (ρ : Reading Kf) (fs : Model.Forest.Shape) (zx : Array E) (p : Pub Kf) : Prop where
  size : zx.size = fs.dT
  z : ∀ t < fs.dT, p.z t = pt ρ zx t

/-- The array ends in zx. -/
def EndsIn (key zx : Array E) : Prop := ∃ pre : Array E, key = pre ++ zx

theorem pt_append_right (ρ : Reading Kf) (a b : Array E) (j : ℕ) :
    pt ρ (a ++ b) (a.size + j) = pt ρ b j := by
  unfold pt
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append,
    if_neg (by omega), Nat.add_sub_cancel_left]

/-- **The kind's inner point of a unit, read, is a tail of zx.** -/
theorem inner_tail (ρ : Reading Kf) {key zx : Array E} (hk : EndsIn key zx) (u : UnitG)
    (hb : u.bits ≤ zx.size) {j : ℕ} (hj : j < u.bits) :
    pt ρ (P.inner u key) j = pt ρ zx (zx.size - u.bits + j) := by
  obtain ⟨pre, rfl⟩ := hk
  unfold P.inner
  have hs : (pre ++ zx).size = pre.size + zx.size := Array.size_append
  rw [pt_extract ρ _ (Nat.le_refl _) (by omega), hs,
    show pre.size + zx.size - u.bits + j = pre.size + (zx.size - u.bits + j) by omega,
    pt_append_right]

theorem inner_size {key zx : Array E} (hk : EndsIn key zx) (u : UnitG) (hb : u.bits ≤ zx.size) :
    (P.inner u key).size = u.bits := by
  obtain ⟨pre, rfl⟩ := hk
  unfold P.inner
  have hs : (pre ++ zx).size = pre.size + zx.size := Array.size_append
  rw [Array.size_extract]
  omega

/-- **The library's inner point of a family is the same tail.** -/
theorem inn_zx {ρ : Reading Kf} {S : Attention.Shape} {fs : Model.Forest.Shape} {zx : Array E}
    {p : Pub Kf} (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (f : Fam) {j : ℕ}
    (hj : j < f.l (L5.dimOf S)) :
    inn (L5.dimOf S) (L5.callsOf fs) p.z f j = pt ρ zx (zx.size - f.l (L5.dimOf S) + j) := by
  have hl : f.l (L5.dimOf S) ≤ (L5.callsOf fs).Dk := L5.callsFit_deep hF f
  have hD : (L5.callsOf fs).Dk = fs.dT := rfl
  rw [Inst.Model.AttSeg.KeyFormsExt.inn_tail (L5.dimOf S) (L5.callsOf fs) p.z f hl
    (hF.2.1 f.call) j, hD, L.z _ (by omega), L.size]

/-! ## What pointsOf lays into the division's points -/

/-- The division's points are cuts of the inner points of the units wl, ix, wh. -/
structure Cut5 (g : Geo) (zk : Array (Array E)) (p : Pts) : Prop where
  at' : ∃ uW uX uH : UnitG, g.single .wl = some uW ∧ g.single .ix = some uX ∧
    g.single .wh = some uH ∧
    (P.inner uW (zk.getD uW.call #[])).size = 1 + g.lgk + g.lt + g.ldh ∧
    (P.inner uX (zk.getD uX.call #[])).size = g.lgk + g.lt ∧
    (P.inner uH (zk.getD uH.call #[])).size = g.lgk + g.lt + g.ldh ∧
    p.d.zsl = (P.inner uW (zk.getD uW.call #[])).getD 0 zeroE ∧
    p.d.zgW = (P.inner uW (zk.getD uW.call #[])).extract 1 (1 + g.lgk) ∧
    p.d.ziW = (P.inner uW (zk.getD uW.call #[])).extract (1 + g.lgk) (1 + g.lgk + g.lt) ∧
    p.d.zcW = (P.inner uW (zk.getD uW.call #[])).extract (1 + g.lgk + g.lt)
      (1 + g.lgk + g.lt + g.ldh) ∧
    p.d.zgX = (P.inner uX (zk.getD uX.call #[])).extract 0 g.lgk ∧
    p.d.ziX = (P.inner uX (zk.getD uX.call #[])).extract g.lgk (g.lgk + g.lt) ∧
    p.d.zgH = (P.inner uH (zk.getD uH.call #[])).extract 0 g.lgk ∧
    p.d.ziH = (P.inner uH (zk.getD uH.call #[])).extract g.lgk (g.lgk + g.lt) ∧
    p.d.zcH = (P.inner uH (zk.getD uH.call #[])).extract (g.lgk + g.lt) (g.lgk + g.lt + g.ldh)

theorem cut5_of {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : Cut5 g zk p := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, hW, uX, hX, uH, hH, _, hs, _, hz, e⟩ := hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  subst e
  exact ⟨uW, uX, uH, hW, hX, hH, hz.1.1, hz.1.2, hz.2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## A cut of a unit's inner point is a stretch of a family's -/

section Ties
variable {ρ : Reading Kf} {S : Attention.Shape} {fs : Model.Forest.Shape} {zx : Array E}
  {p : Pub Kf}

theorem fam_le (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (f : Fam) :
    f.l (L5.dimOf S) ≤ zx.size := by
  rw [L.size]
  exact L5.callsFit_deep hF f

/-- A coordinate of a unit's inner point is the family's. -/
theorem inner_tie (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) {key : Array E}
    (hk : EndsIn key zx) (u : UnitG) (f : Fam) (hb : u.bits = f.l (L5.dimOf S)) {j : ℕ}
    (hj : j < u.bits) :
    pt ρ (P.inner u key) j = inn (L5.dimOf S) (L5.callsOf fs) p.z f j := by
  rw [inner_tail ρ hk u (by rw [hb]; exact fam_le hF L f) hj,
    inn_zx hF L f (by rw [← hb]; exact hj), hb]

/-- **A cut of a unit's inner point is a stretch of the family's inner point.** -/
theorem cut_tie (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) {key : Array E} (hk : EndsIn key zx)
    (u : UnitG) (f : Fam) (hb : u.bits = f.l (L5.dimOf S)) {a b j : ℕ} (hbs : b ≤ u.bits)
    (hj : a + j < b) :
    pt ρ ((P.inner u key).extract a b) j = inn (L5.dimOf S) (L5.callsOf fs) p.z f (a + j) := by
  have hs := inner_size hk u (by rw [hb]; exact fam_le hF L f)
  rw [pt_extract ρ _ (by rw [hs]; exact hbs) hj]
  exact inner_tie hF L hk u f hb (by omega)

/-- Two families' inner points are tails of one point: the shorter is a stretch of the longer. -/
theorem inn_shift (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (f f' : Fam) {d : ℕ}
    (hd : f.l (L5.dimOf S) + d = f'.l (L5.dimOf S)) {j : ℕ} (hj : j < f.l (L5.dimOf S)) :
    inn (L5.dimOf S) (L5.callsOf fs) p.z f j = inn (L5.dimOf S) (L5.callsOf fs) p.z f' (d + j) := by
  have h' := fam_le hF L f'
  rw [inn_zx hF L f hj, inn_zx hF L f' (by omega)]
  congr 1
  omega

theorem single_bits {g : Geo} {k : P.Keys} {u : UnitG} (h : g.single k = some u) :
    u.bits = g.keyBits k := by
  unfold P.Geo.single at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨q, _, c, _, rfl⟩ := h
  rfl

/-! ## The division's points -/

/-- **The division's points are the library's**, with their lengths: in the letters of the public
records of Johnson/Road/Rows. -/
structure Tie5 (ρ : Reading Kf) (S : Attention.Shape) (fs : Model.Forest.Shape) (d : P.DivP)
    (p : Pub Kf) : Prop where
  chi : ρ.val d.zsl = zChi (L5.dimOf S) (L5.callsOf fs) p.z
  sgW : d.zgW.size = S.cf.lgk
  siW : d.ziW.size = S.cf.lt
  scW : d.zcW.size = S.cf.ldh
  gW : ∀ j < S.cf.lgk, pt ρ d.zgW j = yg (L5.dimOf S) (L5.callsOf fs) p.z j
  iW : ∀ j < S.cf.lt, pt ρ d.ziW j = yi (L5.dimOf S) (L5.callsOf fs) p.z j
  nW : ∀ j < S.cf.ldh, pt ρ d.zcW j = yn (L5.dimOf S) (L5.callsOf fs) p.z j
  sgX : d.zgX.size = S.cf.lgk
  siX : d.ziX.size = S.cf.lt
  gX : ∀ j < S.cf.lgk, pt ρ d.zgX j = xg (L5.dimOf S) (L5.callsOf fs) p.z j
  iX : ∀ j < S.cf.lt, pt ρ d.ziX j = xi (L5.dimOf S) (L5.callsOf fs) p.z j
  sgH : d.zgH.size = S.cf.lgk
  siH : d.ziH.size = S.cf.lt
  scH : d.zcH.size = S.cf.ldh
  gH : ∀ j < S.cf.lgk, pt ρ d.zgH j = yg (L5.dimOf S) (L5.callsOf fs) p.z j
  iH : ∀ j < S.cf.lt, pt ρ d.ziH j = yi (L5.dimOf S) (L5.callsOf fs) p.z j
  nH : ∀ j < S.cf.ldh, pt ρ d.zcH j = yn (L5.dimOf S) (L5.callsOf fs) p.z j

/-- **From pointsOf's cuts to the library's points, at the division.** hE: the key point of the call
of each unit that one call alone serves ends in zx. -/
theorem tie5_of (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (hlt : S.cf.lt = (L5.dimOf S).lT)
    {zk : Array (Array E)}
    (hE : ∀ u : UnitG, (∃ k, (geoOf S).single k = some u) → EndsIn (zk.getD u.call #[]) zx)
    {P' : Pts} (H : Cut5 (geoOf S) zk P') : Tie5 ρ S fs P'.d p := by
  obtain ⟨uW, uX, uH, hW, hX, hH, sW, sX, sH, e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := H.at'
  have e1 : P'.d.zgW = (P.inner uW (zk.getD uW.call #[])).extract 1 (1 + S.cf.lgk) := e1
  have e2 : P'.d.ziW = (P.inner uW (zk.getD uW.call #[])).extract (1 + S.cf.lgk)
    (1 + S.cf.lgk + S.cf.lt) := e2
  have e3 : P'.d.zcW = (P.inner uW (zk.getD uW.call #[])).extract (1 + S.cf.lgk + S.cf.lt)
    (1 + S.cf.lgk + S.cf.lt + S.cf.ldh) := e3
  have e4 : P'.d.zgX = (P.inner uX (zk.getD uX.call #[])).extract 0 S.cf.lgk := e4
  have e5 : P'.d.ziX = (P.inner uX (zk.getD uX.call #[])).extract S.cf.lgk
    (S.cf.lgk + S.cf.lt) := e5
  have e6 : P'.d.zgH = (P.inner uH (zk.getD uH.call #[])).extract 0 S.cf.lgk := e6
  have e7 : P'.d.ziH = (P.inner uH (zk.getD uH.call #[])).extract S.cf.lgk
    (S.cf.lgk + S.cf.lt) := e7
  have e8 : P'.d.zcH = (P.inner uH (zk.getD uH.call #[])).extract (S.cf.lgk + S.cf.lt)
    (S.cf.lgk + S.cf.lt + S.cf.ldh) := e8
  have kW := hE uW ⟨_, hW⟩
  have kX := hE uX ⟨_, hX⟩
  have kH := hE uH ⟨_, hH⟩
  have bW : uW.bits = Fam.l (L5.dimOf S) .w3 := by
    rw [single_bits hW]
    show 1 + S.cf.lgk + S.cf.lt + S.cf.ldh = 1 + S.cf.lgk + (L5.dimOf S).lT + S.cf.ldh
    rw [hlt]
  have bX : uX.bits = Fam.l (L5.dimOf S) .x3 := by
    rw [single_bits hX]
    show S.cf.lgk + S.cf.lt = S.cf.lgk + (L5.dimOf S).lT
    rw [hlt]
  have bH : uH.bits = Fam.l (L5.dimOf S) .f4 := by
    rw [single_bits hH]
    show S.cf.lgk + S.cf.lt + S.cf.ldh = S.cf.lgk + (L5.dimOf S).lT + S.cf.ldh
    rw [hlt]
  have nW : uW.bits = 1 + S.cf.lgk + S.cf.lt + S.cf.ldh := single_bits hW
  have nX : uX.bits = S.cf.lgk + S.cf.lt := single_bits hX
  have nH : uH.bits = S.cf.lgk + S.cf.lt + S.cf.ldh := single_bits hH
  have sW' : (P.inner uW (zk.getD uW.call #[])).size = 1 + S.cf.lgk + S.cf.lt + S.cf.ldh := sW
  have sX' : (P.inner uX (zk.getD uX.call #[])).size = S.cf.lgk + S.cf.lt := sX
  have sH' : (P.inner uH (zk.getD uH.call #[])).size = S.cf.lgk + S.cf.lt + S.cf.ldh := sH
  have h41 : Fam.l (L5.dimOf S) .f4 + 1 = Fam.l (L5.dimOf S) .w3 := by
    show (L5.dimOf S).lg + (L5.dimOf S).lT + (L5.dimOf S).ln + 1 =
      1 + (L5.dimOf S).lg + (L5.dimOf S).lT + (L5.dimOf S).ln
    omega
  have l4 : Fam.l (L5.dimOf S) .f4 = S.cf.lgk + S.cf.lt + S.cf.ldh := by rw [← bH, nH]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]
    exact inner_tie hF L kW uW .w3 bW (by omega)
  · rw [e1, size_cut _ (by show 1 + S.cf.lgk ≤ _; omega)]
    show 1 + S.cf.lgk - 1 = _
    omega
  · rw [e2, size_cut _ (by show 1 + S.cf.lgk + S.cf.lt ≤ _; omega)]
    show 1 + S.cf.lgk + S.cf.lt - (1 + S.cf.lgk) = _
    omega
  · rw [e3, size_cut _ (by show 1 + S.cf.lgk + S.cf.lt + S.cf.ldh ≤ _; omega)]
    show 1 + S.cf.lgk + S.cf.lt + S.cf.ldh - (1 + S.cf.lgk + S.cf.lt) = _
    omega
  · intro j hj
    rw [e1]
    exact cut_tie hF L kW uW .w3 bW (a := 1) (b := 1 + S.cf.lgk) (by omega) (by omega)
  · intro j hj
    rw [e2]
    exact cut_tie hF L kW uW .w3 bW (a := 1 + S.cf.lgk) (b := 1 + S.cf.lgk + S.cf.lt) (by omega)
      (by omega)
  · intro j hj
    rw [e3, cut_tie hF L kW uW .w3 bW (a := 1 + S.cf.lgk + S.cf.lt)
      (b := 1 + S.cf.lgk + S.cf.lt + S.cf.ldh) (j := j) (by omega) (by omega)]
    show _ = inn _ _ _ .w3 (1 + S.cf.lgk + (L5.dimOf S).lT + j)
    rw [← hlt]
  · rw [e4, size_cut _ (by show S.cf.lgk ≤ _; omega)]
    rfl
  · rw [e5, size_cut _ (by show S.cf.lgk + S.cf.lt ≤ _; omega)]
    show S.cf.lgk + S.cf.lt - S.cf.lgk = _
    omega
  · intro j hj
    rw [e4]
    exact cut_tie hF L kX uX .x3 bX (a := 0) (b := S.cf.lgk) (by omega) (by omega)
  · intro j hj
    rw [e5]
    exact cut_tie hF L kX uX .x3 bX (a := S.cf.lgk) (b := S.cf.lgk + S.cf.lt) (by omega) (by omega)
  · rw [e6, size_cut _ (by show S.cf.lgk ≤ _; omega)]
    rfl
  · rw [e7, size_cut _ (by show S.cf.lgk + S.cf.lt ≤ _; omega)]
    show S.cf.lgk + S.cf.lt - S.cf.lgk = _
    omega
  · rw [e8, size_cut _ (by show S.cf.lgk + S.cf.lt + S.cf.ldh ≤ _; omega)]
    show S.cf.lgk + S.cf.lt + S.cf.ldh - (S.cf.lgk + S.cf.lt) = _
    omega
  · intro j hj
    rw [e6, cut_tie hF L kH uH .f4 bH (a := 0) (b := S.cf.lgk) (j := j) (by omega) (by omega),
      inn_shift hF L .f4 .w3 h41 (by omega)]
    show _ = inn _ _ _ .w3 (1 + j)
    rw [Nat.zero_add]
  · intro j hj
    rw [e7, cut_tie hF L kH uH .f4 bH (a := S.cf.lgk) (b := S.cf.lgk + S.cf.lt) (j := j)
      (by omega) (by omega), inn_shift hF L .f4 .w3 h41 (by omega)]
    show _ = inn _ _ _ .w3 (1 + S.cf.lgk + j)
    congr 1
    omega
  · intro j hj
    rw [e8, cut_tie hF L kH uH .f4 bH (a := S.cf.lgk + S.cf.lt)
      (b := S.cf.lgk + S.cf.lt + S.cf.ldh) (j := j) (by omega) (by omega),
      inn_shift hF L .f4 .w3 h41 (by omega)]
    show _ = inn _ _ _ .w3 (1 + S.cf.lgk + (L5.dimOf S).lT + j)
    rw [← hlt]
    congr 1
    omega

end Ties

end K5Law

#print axioms K5Law.tie5_of
#print axioms K5Law.inner_tail
#print axioms K5Law.inn_zx
#print axioms K5Law.cut5_of
