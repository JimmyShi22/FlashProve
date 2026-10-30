-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/TablesAt.lean: kind K5: the tables' clauses of the public records of
Johnson/Road/Rows, paid of what tablesP itself makes: at h := oldOf S gL i
(Johnson/Desc/First/Att/Claims/Any.lean), where i.t is what tablesP makes of i.p: TabAt, AsAt, QaAt
and AhAt (Johnson/Road/Rows/AttRead.lean, AttEnds58.lean) hold of every named table, and ptM and ptD
are pointM and pointD.

Main names:
  `fits_size`: the placing's own test gives the stored length as those records want it. `tabAt_of`,
    `asAt_of`, `longAt_of`, `scoreTiles_back`.
  `TabsAt tl h zx`: the clauses, gathered. `tabs_at`: they hold.
  `TabsLook tl h phiB0 phiB1 phiP`, `tabs_look`: the three tables on the lookup's matrix (tBit0,
    tBit1, tPin) lie in the list under the three weight vectors that the lookup hands in. That these
    vectors are the right ones is not said here.
Premises: i.g = geoOf S; tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t; PosG i.g
(Johnson/Desc/First/Att/Claims/TablesSpec.lean).
Limit: the public records' other clauses (the points' lengths; the points tied coordinate by
coordinate; "piece b is pair b"; wJv) are not touched here.
Used of OnBytes and Johnson/Road: plain records and definitions alone: TabAt, AsAt, QaAt, AhAt,
lowOf, HTailF2.mats; the pure functions Model.eqTab, blockRows, Attention.tok, scoreTiles, lastN,
lastCoords, pointM, pointD. No routine in a context and no theorem on a run.
Not claimed: that a table is true of a matrix.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds58
import Johnson.Desc.First.Att.Claims.TablesSpec

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf TablesP LookIn Pts)

theorem fits_size {mats : Array TMat} {mat len e : ℕ} (h : P.fits (matsOf mats) mat len e = true) :
    e = (mats.getD mat {}).k * ((mats.getD mat {}).m / len) := by
  unfold P.fits matsOf at h
  rw [Array.getElem?_map] at h
  cases hm : mats[mat]? with
  | none => rw [hm] at h; cases h
  | some M =>
    rw [hm] at h
    simp only [Option.map_some, Bool.and_eq_true, beq_iff_eq] at h
    rw [Array.getD_eq_getD_getElem?, hm]
    exact h.2

variable {tl : HTailF2} {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {n : ℕ}

theorem tabAt_of {a mat len e : ℕ} {phi : Array E} (T : Tab (stOf i.t n) a mat len phi e)
    (hf : P.fits (matsOf tl.mats) mat len e = true) : TabAt tl (oldOf S gL i) a mat len phi := by
  obtain ⟨f, hm, e1, e2, e3, e4⟩ := T.laid
  refine ⟨⟨funBack f, ?_, e1, e2, e3, e4⟩, ?_⟩
  · show funBack f ∈ (i.t.funs.map funBack).toList
    rw [Array.toList_map]
    exact List.mem_map.2 ⟨f, hm, rfl⟩
  · show (i.t.tabLen.lookup a).getD 0 = _
    have hs : i.t.tabLen.lookup a = some e := T.size
    rw [hs, ← fits_size hf]
    rfl

theorem asAt_of {a : ℕ} {phi : Array E} (hg : i.g = geoOf S) (T : AsTabS (stOf i.t n) i.g a phi) :
    AsAt (oldOf S gL i) a phi := by
  rw [hg] at T
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨f, hm, r⟩ := T.laid q hq
    refine ⟨funBack f, ?_, r⟩
    show funBack f ∈ (i.t.funs.map funBack).toList
    rw [Array.toList_map]
    exact List.mem_map.2 ⟨f, hm, rfl⟩
  · show (i.t.tabLen.lookup a).getD 0 = _
    have hs : i.t.tabLen.lookup a = some _ := T.size
    rw [hs]
    rfl

theorem longAt_of {a mat e : ℕ} {zc tokv : Array E} (hg : i.g = geoOf S)
    (Q : QLong i.g (matsOf tl.mats) mat zc tokv e a (stOf i.t n)) :
    TabAt tl (oldOf S gL i) a mat (2 ^ S.cf.la) (blockRows (lowOf S zc) tokv) := by
  rw [hg] at Q
  obtain ⟨c, hc, T, hf⟩ := Q
  have ec : c.2 = zc.extract (zc.size - S.ls) zc.size := by
    unfold P.cutLast at hc
    split at hc
    · cases hc
    · rw [← Option.some.inj hc]
      rfl
  rw [ec] at T
  exact tabAt_of T hf

theorem scoreTiles_back (S : Attention.Shape) (k : P.ScoreP) :
    Attention.scoreTiles S (scoreBack k) = P.scoreTiles (geoOf S) k := by
  unfold Attention.scoreTiles P.scoreTiles scoreBack
  cases k.below <;> rfl

/-- The tables' clauses of the public records, gathered. zx: the lookup's point. -/
structure TabsAt (tl : HTailF2) (h : Attention.Heard) (zx : Array E) : Prop where
  ptM : h.t.ptM = pointM h.S h.d
  ptD : h.t.ptD = pointD h.S h.d
  tA : AsAt h h.t.tA (lastN zx h.S.cf.lmS)
  tVM : AsAt h h.t.tVM (lastN h.t.ptM h.S.cf.lmS)
  tVD : AsAt h h.t.tVD (lastN h.t.ptD h.S.cf.lmS)
  hW : AhAt tl h h.t.hW (eqTab h.d.ziW)
  hX : AhAt tl h h.t.hX (eqTab h.d.ziX)
  hE : TabAt tl h h.t.hE h.S.cf.NAs h.S.T (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt)))
  hT : AhAt tl h h.t.hT (eqTab h.x.ti)
  hPi : AhAt tl h h.t.hPi (eqTab (h.x.pi h.S))
  hR2 : AhAt tl h h.t.hR2 (eqTab (h.x.ri2 h.S))
  tO : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la) (blockRows (lowOf h.S h.d.zcW) (eqTab h.d.ziW))
  qO : TabAt tl h h.t.qO (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S h.d.zcW) (eqTab (h.d.scE.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.cf.lt))))
  qVM : TabAt tl h h.t.qVM (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S h.d.zcW) (tok h.S h.d.wJv (lastCoords h.d.vpm.r h.S.cf.lB)))
  qVD : QaAt tl h h.t.qVD h.d.zcW
    (tok h.S (eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT))) (lastCoords h.d.vpd.r h.S.cf.lB))
  qF : QaAt tl h h.t.qF (h.x.rc h.S) (eqTab (h.x.ri h.S))
  qKx : QaAt tl h h.t.qKx (h.x.rc h.S) (eqTab (h.x.pj h.S))
  score : List.Forall₂ (fun (k : Score) (tb : ScoreTables) =>
      AhAt tl h tb.tM (tok h.S k.wI k.zi) ∧
      TabAt tl h tb.tQ (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
        (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).1 k.zi)) ∧
      TabAt tl h tb.tK (h.S.cf.NAs + 3) (2 ^ h.S.cf.la)
        (blockRows (lowOf h.S (lastCoords k.sc.r h.S.cf.ldh)) (tok h.S (scoreTiles h.S k).2 k.zj)))
    h.scores.toList h.t.score.toList

/-- **The tables' clauses hold of what tablesP itself makes.** -/
theorem tabs_at {nW : ℕ} {lk : LookIn} (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g) :
    TabsAt tl (oldOf S gL i) lk.zx := by
  obtain ⟨n, T⟩ := tables_are ht hp
  have row : ∀ {a : ℕ} {psi : Array E}, QRow i.g (matsOf tl.mats) psi a (stOf i.t n) →
      TabAt tl (oldOf S gL i) a S.cf.NAs S.T psi := by
    intro a psi Q
    rw [hg] at Q
    exact tabAt_of Q.1 Q.2
  have eM : (oldOf S gL i).t.ptM = pointM S (oldOf S gL i).d := by
    show i.t.ptM = _
    rw [T.ptM, hg]
    rfl
  have eD : (oldOf S gL i).t.ptD = pointD S (oldOf S gL i).d := by
    show i.t.ptD = _
    rw [T.ptD, hg]
    rfl
  have aM := asAt_of (gL := gL) hg T.tVM.1
  have aD := asAt_of (gL := gL) hg T.tVD.1
  have aA := asAt_of (gL := gL) hg T.tA.1
  rw [hg] at aM aD aA
  refine ⟨eM, eD, aA, ?_, ?_, row T.hW, row T.hX, ?_, row T.hT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eM]; exact aM
  · rw [eD]; exact aD
  · have := row T.hE; rw [hg] at this; exact this
  · have := row T.hPi; rw [hg] at this; exact this
  · have := row T.hR2; rw [hg] at this; exact this
  · have := longAt_of (gL := gL) hg T.tO; rw [hg] at this; exact this
  · have := longAt_of (gL := gL) hg T.qO; rw [hg] at this; exact this
  · have := longAt_of (gL := gL) hg T.qVM; rw [hg] at this; exact this
  · have := longAt_of (gL := gL) hg T.qVD; rw [hg] at this; exact this
  · have := longAt_of (gL := gL) hg T.qF; rw [hg] at this; exact this
  · have := longAt_of (gL := gL) hg T.qKx; rw [hg] at this; exact this
  · show List.Forall₂ _ (i.p.scores.map scoreBack).toList (i.t.score.map _).toList
    rw [Array.toList_map, Array.toList_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine T.score.imp fun k y q => ?_
    have q1 := row q.1
    have q2 := longAt_of (gL := gL) hg q.2.1
    have q3 := longAt_of (gL := gL) hg q.2.2
    rw [hg] at q1 q2 q3
    rw [← scoreTiles_back] at q2 q3
    exact ⟨q1, q2, q3⟩

/-- The three tables on the lookup's matrix: the two planes of bits and the pins. -/
structure TabsLook (tl : HTailF2) (h : Attention.Heard) (phiB0 phiB1 phiP : Array E) : Prop where
  tBit0 : TabAt tl h h.t.tBit0 (h.S.cf.NAs + 2) (2 ^ h.S.cf.lmb) phiB0
  tBit1 : TabAt tl h h.t.tBit1 (h.S.cf.NAs + 2) (2 ^ h.S.cf.lmb) phiB1
  tPin : TabAt tl h h.t.tPin (h.S.cf.NAs + 2) (2 ^ h.S.cf.lmb) phiP

/-- **They too lie where tablesP itself lays them**, under the three weight vectors that the lookup hands in. -/
theorem tabs_look {nW : ℕ} {lk : LookIn} (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g) :
    TabsLook tl (oldOf S gL i) lk.phiB0 lk.phiB1 lk.phiP := by
  obtain ⟨n, T⟩ := tables_are ht hp
  have look : ∀ {a : ℕ} {phi : Array E}, QLook i.g (matsOf tl.mats) phi a (stOf i.t n) →
      TabAt tl (oldOf S gL i) a (S.cf.NAs + 2) (2 ^ S.cf.lmb) phi := by
    intro a phi Q
    rw [hg] at Q
    exact tabAt_of Q.1 Q.2
  exact ⟨look T.tBit0, look T.tBit1, look T.tPin⟩

end K5Law
