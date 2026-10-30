-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Back.lean: the back of the hearing (the leaves' sumcheck, the zero
point, the bits' sumcheck) with the run "planes" behind it, against the last three stretches of the
course and its row on the counts.

Main names:
  rowOfC, cB, bvOf, cBits_rows: the rows that the course's last stretch adds, written out.
  rowsF_snoc: the kind's rows in the order of groupRows, written out.
  back_sim: THE BACK: row by row, the kind's rows, read, and the course's have the same terms on the
    bits and the same value of "mask form - target".

Limits. One world W of mask entries; where the flat functions return.

-/
import Johnson.Desc.First.Look.KeyLaw.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World eqTab orderDefault ofNat)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried)
open Lk6.PortSim (noClaim sBits sLeaves byVarF)
open Lk6.Mid (Dt Cs RowF pscC eqPairsF ordDown cClo cZero cBits cntRowF)

/-- The row that a sumcheck of the course adds. -/
def rowOfC (D : Dt) (c : PscF.Claim) (S : PscF.Summand) (keys : Bool) (kept : ℕ)
    (place : List GE → List GE) (s : Cs) : RowF :=
  ⟨(oOf D c S keys s).rowMasks, ((oOf D c S keys s).rowMaps.take kept).map fun a =>
    (a, eqPairsF (place (oOf D c S keys s).point)), (oOf D c S keys s).rowTarget⟩

/-- The claim of the bits' sumcheck. -/
def cB (D : Dt) (zt : List GE) : PscF.Claim :=
  ⟨(ordDown (D.S.mu + D.S.d)).map fun t => PscF.Weight.equality (zt.getD t 0) 3, [], 0⟩

/-- The row on the bits' value. -/
def bvOf (o : PscF.Out) : RowF :=
  ⟨(o.ends.getD 0 noClaim).masks, [(1, eqPairsF (o.ends.getD 0 noClaim).point)],
    (o.ends.getD 0 noClaim).value⟩

theorem cBits_rows (D : Dt) (s : Cs) : (cBits D s).rows =
    (s.rows ++ [rowOfC D (cB D s.zt) sBits false 0 (byVarF · (ordDown (D.S.mu + D.S.d))) s]) ++
      [bvOf (pscC D (cB D s.zt) sBits false 0 (byVarF · (ordDown (D.S.mu + D.S.d))) s).1] := rfl

theorem rowsF_snoc (G : Fork) (home : ℕ → Slot) (as : List Aff) (b : Aff) (c1 c2 c3 : PlaneClaim) :
    rowsF G home (as ++ [b]) [c1, c2, c3] = as.map (rowA G home) ++
      [rowP G home true c1, rowA G home b, rowP G home false c2, rowP G home true c3] := by
  unfold rowsF
  simp

variable {W : PscF.World} {home : ℕ → Slot}

theorem rowsRel_ne {F : Fork} {as : List Aff} {rs : List RowF} (h : RowsRel W home F as rs) :
    ∀ a ∈ as, NoEnt a := by
  induction h with
  | nil => intro a ha; cases ha
  | cons x _ ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact x.2.1
    · exact ih a ha

set_option maxHeartbeats 1000000 in
/-- **The back.** -/
theorem back_sim {D : Dt} {f : Face} (hD : DataIs D f)
    (hleaf : ∀ al (z : Array E), readE (f.leaf zeroE al z) =
      readE al - 1 - D.tabAt ((z.toList.reverse.map readE).drop D.S.mu))
    (hcount : f.count = D.S.allKeys - D.S.padCount)
    {s5 : Cs} {F11 F13 F14 F15 G : Fork} {t11 t13 t14 t15 u : Tape} {table : Carried}
    {alpha : E} {lv0 lv : Psc} {zb0 x5 : Array E} {bits : Whole} {g : HeardG}
    (st5 : St W home D F11 t11 s5 (own (1 + (2 * f.d + f.mu)) ++
      (own (1 + 2 * (f.mu + f.d) + 2 + 1) ++ [])) table.rows.toList)
    (hT : RC W home F11 table.form s5.top)
    (hTp : s5.top.point = table.point.toList.reverse.map readE)
    (hTs : table.point.size = f.mu + f.d) (halpha : s5.alpha = readE alpha)
    (e13 : Fl.pscBegin table.form F11 t11 = some (lv0, F13, t13))
    (e14 : Fl.roundsIn .eq lv0 ((List.range (f.mu + f.d)).map fun j =>
      (table.point.getD j zeroE, if j < f.d then 2 else 1)) F13 t13 = some ((zb0, lv), F14, t14))
    (e15 : Fl.point .zero (f.mu + f.d) F14 t14 = some (x5, F15, t15))
    (e16 : wholeStandIn (Aff.ofConst zeroE) x5.reverse.toList 2 1 (fun x =>
      subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE)) F15 t15 = some (bits, G, u))
    (g1 : g.theta = zeroE) (g2 : g.alpha = alpha) (g3 : g.rows = table.rows.push bits.row)
    (g4 : g.leaves = lv) (g5 : g.sBit = bits.sEnd) (g7 : g.zb0 = zb0)
    (g8 : g.zb1 = (bits.challenges.take (f.mu + f.d)).toArray) :
    Later F11 G ∧ Sized G ∧
      Shp t11 u (pscShape ((List.range (f.mu + f.d)).map fun j => (if j < f.d then 2 else 1 : ℕ))
          none
        ++ ([(RoundName.zero.name, 0, f.mu + f.d, 0)] ++
          pscShape (List.replicate (f.mu + f.d) 2) (some (2, 1)))) ∧
      ∀ (H H' : Fork) (pl : List PlaneClaim) (u' : Tape), Later G H →
        planesG f g H [] = some (pl, H', u') →
        Later H H' ∧ (∀ a ∈ g.rows.toList ++ pl.map (·.lead), NoEnt a) ∧
        ∀ K, Later H' K → List.Forall₂ (EvEq W) (rowsF K home g.rows.toList pl)
          ((cBits D (cZero D (cClo D s5))).rows ++ [cntRowF D]) := by
  have hm : D.S.mu + D.S.d = f.mu + f.d := by rw [hD.mu, hD.d]
  have hzs2 : ((List.range (f.mu + f.d)).map fun j =>
      (table.point.getD j zeroE, if j < f.d then 2 else 1)).map (·.2) =
      (List.range (f.mu + f.d)).map fun j => (if j < f.d then 2 else 1 : ℕ) := by
    rw [List.map_map]; rfl
  have hne : ((List.range (f.mu + f.d)).map fun j =>
      (table.point.getD j zeroE, if j < f.d then 2 else 1)) ≠ [] := by
    intro h0
    have := congrArg List.length h0
    have h1 := hD.oneD
    simp at this
    omega
  -- the leaves' sumcheck
  obtain ⟨r6, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10⟩ := open_sim
    (c := ⟨(ordDown (D.S.mu + D.S.d)).map fun t => PscF.Weight.equality (s5.top.point.getD t 0)
      (if t < D.S.mu then 2 else 3), s5.top.masks, s5.top.value⟩)
    (factor := fun p => s5.alpha - 1 - D.tabAt ((byVarF p (ordDown (D.S.mu + D.S.d))).drop D.S.mu))
    (place := (byVarF · (ordDown (D.S.mu + D.S.d)))) e13 e14 hne
    (by rw [hzs2, degs_sum]; exact st5)
    (by
      show (ordDown (D.S.mu + D.S.d)).map _ = _
      rw [hm, List.map_map]
      apply List.ext_getElem
      · simp [ordDown]
      · intro j h1 h2
        have hj : j < f.mu + f.d := by simpa [ordDown] using h1
        simp only [List.getElem_map, List.getElem_range, ordDown, List.getElem_reverse,
          Function.comp, List.length_range]
        rw [hTp, read_getD, rev_getD _ _ _ (by rw [Array.length_toList, hTs]; omega),
          Array.length_toList, hTs, arr_getD, hD.mu,
          show f.mu + f.d - 1 - (f.mu + f.d - 1 - j) = j by omega]
        congr 1
        by_cases hjd : j < f.d
        · rw [if_pos hjd, if_neg (by omega)]
        · rw [if_neg hjd, if_pos (by omega)])
    hT
  rw [hzs2] at o10
  rw [hzs2, degs_sum] at o6 o8
  have hclo : cClo D s5 = (pscC D ⟨(ordDown (D.S.mu + D.S.d)).map fun t =>
      PscF.Weight.equality (s5.top.point.getD t 0) (if t < D.S.mu then 2 else 3), s5.top.masks,
      s5.top.value⟩ (sLeaves fun p => s5.alpha - 1 -
        D.tabAt ((byVarF p (ordDown (D.S.mu + D.S.d))).drop D.S.mu)) false 1
      (byVarF · (ordDown (D.S.mu + D.S.d))) s5).2 := rfl
  rw [← hclo] at o1 o2
  obtain ⟨s6, hs6⟩ : ∃ s, s = cClo D s5 := ⟨_, rfl⟩
  rw [← hs6] at o1 o2 ⊢
  -- the zero point
  obtain ⟨rfl, z1, z2, z3, z4⟩ := point_st e15 o2
  have z2' : s6.draws = x5.toList.map readE := z2
  have hx5 : x5.reverse.toList.length = f.mu + f.d := by simp [z3]
  -- the bits' sumcheck, on the stand without the leaves' row
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := step (W := W) (home := home) (D := D)
    (s := { (cZero D s6) with rows := s5.rows }) (c := cB D s6.draws) (S := sBits) (keys := false)
    (place := (byVarF · (ordDown (D.S.mu + D.S.d)))) (pat := []) (rows := table.rows.toList) e16
    (by rw [hx5]; exact z1.congr rfl rfl rfl rfl)
    (by
      show (ordDown (D.S.mu + D.S.d)).map (fun t => PscF.Weight.equality (s6.draws.getD t 0) 3) = _
      have hl : D.S.mu + D.S.d = s6.draws.length := by rw [z2', List.length_map, hm]; simp [z3]
      have := down_getD (0 : GE) s6.draws
      have e1 : (ordDown s6.draws.length).map
          (fun t => PscF.Weight.equality (s6.draws.getD t 0) 3) =
          ((ordDown s6.draws.length).map fun t => s6.draws.getD t 0).map
            (fun a => PscF.Weight.equality a 3) := by
        rw [List.map_map]; rfl
      rw [hl, e1, this, z2']
      simp [List.map_reverse])
    ((Reads.const F15 zeroE).congr rfl readE_zero.symm) rfl rfl (by decide)
    (fun pt y => by
      show (y.map readE).getD 0 0 * (y.map readE).getD 0 0 - (y.map readE).getD 0 0 = _
      rw [readE_sub, readE_mul, read_getD])
  rw [hx5] at q2 q3 q6
  obtain ⟨k1, k2⟩ := snoc_inv (show List.Forall₂ (RowIs W home G) (table.rows.toList ++ [bits.row])
    (s5.rows ++ [rowOfC D (cB D s6.draws) sBits false 0 (byVarF · (ordDown (D.S.mu + D.S.d)))
      (cZero D s6)]) from q1.rows)
  obtain ⟨b0p, b0⟩ := q4 0 (by decide)
  obtain ⟨P, hP⟩ : ∃ P, P = (pscC D (cB D s6.draws) sBits false 0
    (byVarF · (ordDown (D.S.mu + D.S.d))) (cZero D s6)).1 := ⟨_, rfl⟩
  have b0p' : (P.ends.getD 0 noClaim).point = P.point := by rw [hP]; exact b0p
  have q2' : P.point = byVarF ((bits.challenges.take (f.mu + f.d)).map readE)
      (ordDown (D.S.mu + D.S.d)) := by rw [hP]; exact q2
  have b0' : RC W home G (Aff.slot (bits.sEnd + 0)) (P.ends.getD 0 noClaim) := by
    rw [hP]; exact b0
  refine ⟨o9.trans q5, q1.base.sized, o10.trans (z4.trans q6), ?_⟩
  intro H H' pl u' hGH hpl
  -- the run "planes"
  unfold planesG at hpl
  replace hpl := bind_some hpl
  obtain ⟨⟨row, lv'⟩, G1, u1, h1, hpl⟩ := hpl
  cases pure_some hpl
  rw [g4] at h1
  obtain ⟨hh, -, rfl⟩ := row_fl h1
  have hSH : Sized H := hGH.sized q1.base.sized
  obtain ⟨-, -, p3, -⟩ := PscRun.hideRun_ok _ _ _ _ _ hSH hh
  have lH : Later H H' := PscRun.hideRun_later hSH hh
  refine ⟨lH, ?_, ?_⟩
  · intro a ha
    rw [g3, Array.toList_push] at ha
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact rowsRel_ne k1 a ha
      · obtain rfl : a = bits.row := by simpa using ha
        exact k2.2.1
    · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact o7
      · exact noEnt_slot _
      · exact noEnt_const _
  intro G' hK
  have lG : Later G G' := hGH.trans (lH.trans hK)
  have hrow6 := o8 G' (q5.trans lG) (fun i hi => by
    obtain ⟨-, -, c3, c4, c5⟩ := p3 i (by simpa [o6] using hi)
    rw [o5] at c3 c4 c5
    obtain ⟨-, k2', k3'⟩ := hK.keep _ c3
    show readE (G'.vp.getD _ zeroE) - readE (G'.mf.getD _ zeroE) * W.mask (home _) = _
    have : (Array.replicate lv.walk.1.length zeroE).getD i zeroE = zeroE := by
      simp [Array.getD]
    rw [k2', k3', c4, c5, this, readE_sub, readE_zero, readE_one]
    ring)
  have hrows : (cBits D (cZero D s6)).rows ++ [cntRowF D] = s5.rows ++ [r6,
      rowOfC D (cB D s6.draws) sBits false 0 (byVarF · (ordDown (D.S.mu + D.S.d))) (cZero D s6),
      bvOf P, cntRowF D] := by
    rw [cBits_rows, hP]
    show ((s6.rows ++ _) ++ _) ++ _ = _
    rw [o1]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [hrows, g3, Array.toList_push, rowsF_snoc]
  have hzb0 : byVarF (zb0.toList.map readE) (ordDown (D.S.mu + D.S.d)) =
      zb0.toList.reverse.map readE := by
    rw [byVar_down _ _ (by rw [List.length_map, Array.length_toList, o4, hm]; simp),
      List.map_reverse]
  refine List.rel_append ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ List.Forall₂.nil))))
  · rw [List.forall₂_map_left_iff]
    exact List.Forall₂.imp (fun a r x => evEq_rowA x) (RowsRel.later k1 lG)
  · -- the leaves' row
    refine ⟨?_, ?_⟩
    · show [(readE (mulE g.leaves.eps (f.leaf g.theta g.alpha g.zb0)),
        pairsF (eqPairs (f.mu + f.d) g.zb0))] = r6.maps
      rw [o3, g4, g1, g2, g7, readE_mul, hleaf, hzb0, halpha,
        eqPairs_read _ _ (by rw [o4]; simp)]
    · show W.form (PscF.scaleForm (-1) (mfOf G' home (lv.rowForm oneE {}))) -
        -valOf G' (lv.rowForm oneE {}) = _
      rw [← hrow6, hidV_eq, PscF.World.form_scale]
      ring
  · exact evEq_rowA ⟨k2.1, k2.2.1, fun H hH => k2.2.2 H (lG.trans hH)⟩
  · -- the bits' value
    have b1 := b0'.later lG
    have hv : valOf G' (Aff.slot (bits.sEnd + 0)) = _ := (pubV_eq _ _).symm.trans b1.pub
    have hh2 := b1.hid
    rw [hidV_eq, hv] at hh2
    refine ⟨?_, ?_⟩
    · show [(-readE (subE zeroE oneE), pairsF (eqPairs (f.mu + f.d) g.zb1))] =
        [(1, eqPairsF _)]
      show _ = [(1, eqPairsF (P.ends.getD 0 noClaim).point)]
      rw [b0p', q2', g8, readE_sub, readE_zero, readE_one, eqPairs_read _ _ (by
        simp [q3]),
        byVar_down _ _ (by rw [List.length_map, List.length_take, q3, hm]; omega)]
      simp [List.map_reverse]
    · show W.form (mfOf G' home (Aff.slot g.sBit)) - valOf G' (Aff.slot g.sBit) = _
      rw [g5]
      show W.form (mfOf G' home (Aff.slot (bits.sEnd + 0))) -
        valOf G' (Aff.slot (bits.sEnd + 0)) =
          W.form (P.ends.getD 0 noClaim).masks - (P.ends.getD 0 noClaim).value
      rw [hv]
      linear_combination -hh2
  · -- the counts' row
    refine ⟨?_, ?_⟩
    · show [(readE oneE, pairsF (((List.range f.mu).map fun t => (oneE, ofNat (2 ^ 2 ^ t))) ++
        List.replicate f.d (oneE, oneE)))] = (cntRowF D).maps
      unfold cntRowF pairsF
      rw [hD.mu, hD.d]
      simp [readE_one, OnBytes.Ends.A.readE_ofNat, Function.comp_def]
    · show W.form [] - -(readE (subE zeroE (ofNat f.count)) + 0) = W.form [] - _
      rw [readE_sub, readE_zero, OnBytes.Ends.A.readE_ofNat, hcount]
      show _ = W.form [] - ((D.S.allKeys - D.S.padCount : ℕ) : GE)
      ring

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.back_sim
