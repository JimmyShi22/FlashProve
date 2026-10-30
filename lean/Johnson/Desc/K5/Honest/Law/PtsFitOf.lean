-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PtsFitOf.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE PREMISE ON LENGTHS AND PIECES OF THE MEETINGS (`PtsFit`,
Johnson/Desc/K5/Honest/Law/MeetsOf.lean) AT WHAT THE VERIFIER's FUNCTION OF THE POINTS MAKES. A
definition of a premise, and statements with their proofs.

Main names:
  `piecesFit_of_pairs`   a list with a piece for each pair names layers and heads of the shape
  `ChalLens`         the premise on what was heard: the numbers of challenges and of drawn elements
  `ptsFit_of`        **`PtsFit`**

`ptsFit_of` IS CONDITIONAL. The premises, and who is meant to show each:
  the shape is the planner's; "piece b is pair b" and the lists' lengths: public.
  the verifier's function of the points and its function for the tables return: the caller's, of a
    state behind the rounds. Out of the second return come the two tests on values
    (`tablesP_isSome`, Johnson/Desc/First/Att/Claims/ReadsReturn.lean).
  `ChalLens`: whoever ties the hearing to the planner's numbers.
  hkey: the key point of each plane claim's call has at least the coordinates of the claim's region:
    THE LOOKUP's, of what it hands on: no test of the two functions asks it at a remainder-table
    unit.
By the tree's `points_are` (Claims/PointsRows.lean), `cutU_of` (Claims/PointsCut.lean), `cut5_of`
(Claims/PointsTie.lean), `cut5w_of` (Claims/KeysPub.lean), and `points_chal`, `unit_chal`
(Johnson/Desc/K5/Honest/Law/PointsIs.lean).
Limits. A plan in which the layers of the group have more than one shift is not reached: a unit's
list has there fewer pieces than there are pairs. Nothing here says that a premise holds at any
place or run. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.MeetsOf
import Johnson.Desc.K5.Honest.Law.PointsIs
import Johnson.Desc.First.Att.Claims.ReadsReturn
import Johnson.Desc.First.Att.Claims.KeysPub
import Johnson.Desc.First.Att.Claims.PointsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP Pts Geo geoOf)

/-! ## Pieces -/

/-- A list with a piece for each pair, in the pairs' order, names layers and heads of the shape. -/
theorem piecesFit_of_pairs {S : Attention.Shape} {pw : Array W1} (pr : PairsAre (geoOf S) pw)
    (hn : pw.size = S.NP) : PiecesFit S pw := by
  intro p hp
  obtain ⟨b, hb, e⟩ := getD_of_mem hp
  rw [hn] at hb
  have hb' : b < S.Lam * S.HA := hb
  obtain ⟨e1, e2⟩ := pr b hb
  rw [e] at e1 e2
  have e1' : p.lam = b / S.HA := e1
  have e2' : p.a = b % S.HA := e2
  have hHA : 0 < S.HA := by
    rcases Nat.eq_zero_or_pos S.HA with h0 | h0
    · rw [h0, Nat.mul_zero] at hb'
      exact absurd hb' (Nat.not_lt_zero _)
    · exact h0
  exact ⟨by rw [e1']; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb'),
    by rw [e2']; exact Nat.mod_lt _ hHA⟩

/-! ## The numbers of challenges -/

/-- **The premise on what was heard**: each sumcheck's challenges, and the round that draws many
elements, are as many as the shape's numbers ask. Who ties the hearing to the planner's numbers
shows it: Johnson/Desc/K5/Honest/Law/PtsPublic.lean (`chalLens_of_lengths`) draws it from the
lengths of what was heard and the planner's numbers (`Planned`, Law/Weights.lean). -/
structure ChalLens (S : Attention.Shape) (hh : P.Heard) : Prop where
  units : ∀ o ∈ hh.scores.toList, S.cf.lgk + S.cf.ldh ≤ (P.chal o.2).size
  division : S.cf.lgk + S.cf.lt ≤ (P.chal hh.division).size
  below : S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB ≤ (P.chal hh.below).size
  on : S.cf.lgk + S.lnT + S.cf.lB ≤ (P.chal hh.on).size
  atIndex : (P.chal hh.atIndex).size = S.nvF
  key : (P.chal hh.key).size = 2 * S.cf.lt + S.cf.lgk
  cells : (P.chal hh.cells).size = S.nvH
  point : S.cf.lgk + S.cf.lt ≤ hh.point.size

/-! ## The premise of the meetings -/

/-- **`PtsFit` at what the verifier's function of the points makes.** CONDITIONAL on: the shape is
the planner's; that function and the function for the tables return; `ChalLens`; hkey: THE KEY POINT
OF EACH PLANE CLAIM's CALL HAS AT LEAST THE COORDINATES OF THE CLAIM's REGION: the lookup's, of what
it hands on; each plane claim's list and the three lists of the division have a piece for each pair,
in the pairs' order (public). A unit's list is its plane claim's (`cutU_of`, Claims/PointsCut.lean):
so nothing is asked of the units' lists by themselves. -/
theorem ptsFit_of {S : Attention.Shape} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hid : Attention.shapeHid lid cf = .ok (S, fs)) {zk : Array (Array E)} {hh : P.Heard}
    {L : P.Left} {p : Pts} (hP : P.pointsOf (geoOf S) zk hh L = some p) {mats : Array (ℕ × ℕ)}
    {nW : ℕ} {lk : P.LookIn} {t : P.TablesP} (ht : P.tablesP (geoOf S) mats nW lk p = some t)
    (Cl : ChalLens S hh)
    (hkey : ∀ pc ∈ p.planes.toList,
      (if pc.isD = true then S.nD else S.nM) ≤ (zk.getD pc.call #[]).size)
    (prP : ∀ pc ∈ p.planes.toList, PairsAre (geoOf S) pc.pw ∧ pc.pw.size = S.NP)
    (prW : PairsAre (geoOf S) p.d.pwW) (prX : PairsAre (geoOf S) p.d.pwX)
    (prH : PairsAre (geoOf S) p.d.pwH) : PtsFit S lk.zx p := by
  have N := norm_of_hid hid
  have Z := sizes_of_hid hid
  have hn := Z.lnT
  have hlt := N.lt
  have hM := N.nM
  have hD := N.nD
  have PA := K5Law.points_are hP
  have CU := K5Law.cutU_of hP
  obtain ⟨cw, ctg, cti⟩ := points_chal hP
  obtain ⟨uW, uX, uH, _, _, _, nW', nX', nH', _, gW, iW, cW, gX, iX, gH, iH, cH⟩ :=
    (K5Law.cut5_of hP).at'
  obtain ⟨_, _, _, _, _, _, _, _, _, sW, sX, sH⟩ := (K5Law.cut5w_of hP).at'
  have nW2 : (P.inner uW (zk.getD uW.call #[])).size = 1 + S.cf.lgk + S.cf.lt + S.cf.ldh := nW'
  have nX2 : (P.inner uX (zk.getD uX.call #[])).size = S.cf.lgk + S.cf.lt := nX'
  have nH2 : (P.inner uH (zk.getD uH.call #[])).size = S.cf.lgk + S.cf.lt + S.cf.ldh := nH'
  have ok : K5Law.placeOk (geoOf S) mats nW lk p = true := by
    rw [← K5Law.tablesP_isSome, ht]
    rfl
  unfold K5Law.placeOk at ok
  simp only [Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨m1, m2⟩, _⟩, _⟩, _⟩, _⟩ := ok
  have rE : p.d.scE.r = P.chal hh.division := by rw [PA.scE]; rfl
  have rM : p.d.vpm.r = P.chal hh.below := by rw [PA.vpm]; rfl
  have rD : p.d.vpd.r = P.chal hh.on := by rw [PA.vpd]; rfl
  have rF : p.x.scF.r = P.chal hh.atIndex := by rw [PA.scF]; rfl
  have rK : p.x.scd.r = P.chal hh.key := by rw [PA.scd]; rfl
  have rH : p.x.scH.r = P.chal hh.cells := by rw [PA.scH]; rfl
  have ziW : p.d.ziW.size = S.cf.lt := by
    rw [iW, size_extract_le _ (by rw [nW2]; show 1 + S.cf.lgk + S.cf.lt ≤ _; omega)]
    show 1 + S.cf.lgk + S.cf.lt - (1 + S.cf.lgk) = _
    omega
  have zcW : p.d.zcW.size = S.cf.ldh := by
    rw [cW, size_extract_le _ (by rw [nW2]; exact Nat.le_refl _)]
    show 1 + S.cf.lgk + S.cf.lt + S.cf.ldh - (1 + S.cf.lgk + S.cf.lt) = _
    omega
  have ziH : p.d.ziH.size = S.cf.lt := by
    rw [iH, size_extract_le _ (by rw [nH2]; show S.cf.lgk + S.cf.lt ≤ _; omega)]
    show S.cf.lgk + S.cf.lt - S.cf.lgk = _
    omega
  have mT : p.d.ziW ++ p.d.zcW = p.d.ziH ++ p.d.zcH := by
    unfold P.mergedTokens at m2
    simp only [Bool.and_eq_true, beq_iff_eq] at m2
    exact m2.1
  obtain ⟨eI, eC⟩ := Array.append_inj mT (ziW.trans ziH.symm)
  have zilo : (p.d.zilo (geoOf S)).size = S.cf.lB := by
    show (p.d.ziW.extract S.lnT (S.lnT + S.cf.lB)).size = _
    rw [size_extract_le _ (by rw [ziW]; omega)]
    omega
  have bel := Cl.below
  have onn := Cl.on
  refine
    { planeZ := fun u hu => ?_
      planeN := fun u hu => ?_
      planeP := fun u hu => piecesFit_of_pairs (prP u hu).1 (prP u hu).2
      planeL := fun u hu => ?_
      unitG := fun k hk => ?_
      unitR := fun k hk => ?_
      unitP := fun k hk => ?_
      gW := ?_
      iW := ziW
      cW := zcW
      gX := ?_
      iX := ?_
      gH := ?_
      iH := eI.symm
      cH := eC.symm
      pW := piecesFit_of_pairs prW sW
      pX := piecesFit_of_pairs prX sX
      pH := piecesFit_of_pairs prH sH
      nW := sW
      rE := by rw [rE]; exact Cl.division
      rM := by rw [rM]; omega
      rD := by rw [rD]; omega
      ptM := ?_
      ptD := ?_
      wJv := ?_
      tg := ?_
      ti := ?_
      rF := by rw [rF]; exact Cl.atIndex
      rK := by rw [rK]; exact Cl.key
      rH := by rw [rH]; exact Cl.cells }
  · obtain ⟨c, k, _, hk, ez, _⟩ := CU.planes u hu
    have hb := hkey u hu
    have bits : (geoOf S).keyBits k = if u.isD = true then S.nD else S.nM := by
      rcases hk with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> cases u.isD
      · show S.cf.lgk + 2 * S.cf.lt - 1 = S.nM
        omega
      · show S.cf.lgk + S.cf.lt + S.cf.lB = S.nD
        omega
      · show S.cf.lgk + 2 * S.cf.lt - 1 = S.nM
        omega
      · show S.cf.lgk + S.cf.lt + S.cf.lB = S.nD
        omega
    rw [ez]
    show ((zk.getD u.call #[]).extract ((zk.getD u.call #[]).size - (geoOf S).keyBits k)
      (zk.getD u.call #[]).size).size = _
    rw [size_extract_le _ (Nat.le_refl _), bits]
    omega
  · obtain ⟨_, _, _, hk, _, _⟩ := CU.planes u hu
    rcases hk with ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> omega
  · unfold P.mergedPlanes at m1
    rw [Array.all_eq_true_iff_forall_mem] at m1
    exact beq_iff_eq.1 (m1 u (Array.mem_toList_iff.1 hu))
  · obtain ⟨pc, _, C⟩ := CU.units k hk
    have hs := C.size
    have hc : S.cf.lgk ≤ K5Law.cutB (geoOf S) k.below := by
      unfold K5Law.cutB
      cases k.below
      · show S.cf.lgk ≤ S.cf.lgk + S.lnT
        omega
      · show S.cf.lgk ≤ S.cf.lgk + (S.lnT - 1) + S.lnT
        omega
    rw [C.zg, size_extract_le _ (by show S.cf.lgk ≤ _; omega)]
    rfl
  · obtain ⟨n, hn'⟩ := List.mem_iff_getElem?.1 hk
    rw [Array.getElem?_toList] at hn'
    obtain ⟨o, ho, e⟩ := unit_chal hP hn'
    rw [e]
    exact Cl.units o (Array.mem_toList_iff.2 (Array.mem_of_getElem? ho))
  · obtain ⟨pc, hpc, C⟩ := CU.units k hk
    have hm : pc ∈ p.planes.toList := Array.mem_toList_iff.2 (Array.mem_of_getElem? hpc)
    rw [← C.pw]
    exact piecesFit_of_pairs (prP pc hm).1 (prP pc hm).2
  · rw [gW, size_extract_le _ (by rw [nW2]; show 1 + S.cf.lgk ≤ _; omega)]
    show 1 + S.cf.lgk - 1 = _
    omega
  · rw [gX, size_extract_le _ (by rw [nX2]; show S.cf.lgk ≤ _; omega)]
    rfl
  · rw [iX, size_extract_le _ (by rw [nX2]; exact Nat.le_refl _)]
    show S.cf.lgk + S.cf.lt - S.cf.lgk = _
    omega
  · rw [gH, size_extract_le _ (by rw [nH2]; show S.cf.lgk ≤ _; omega)]
    rfl
  · show (p.d.vpm.r.extract 0 (S.cf.lgk + 2 * S.lnT - 1) ++ p.d.zilo (geoOf S) ++
      p.d.vpm.r.extract (p.d.vpm.r.size - S.cf.lB) p.d.vpm.r.size).size = _
    rw [Array.size_append, Array.size_append, zilo, size_extract_le _ (by rw [rM]; omega),
      size_extract_le _ (Nat.le_refl _), rM]
    omega
  · show (p.d.vpd.r.extract 0 (S.cf.lgk + S.lnT) ++ p.d.zilo (geoOf S) ++
      p.d.vpd.r.extract (p.d.vpd.r.size - S.cf.lB) p.d.vpd.r.size).size = _
    rw [Array.size_append, Array.size_append, zilo, size_extract_le _ (by rw [rD]; omega),
      size_extract_le _ (Nat.le_refl _), rD]
    omega
  · rw [cw, rM]
    rfl
  · rw [ctg, size_extract_le _ (by have := Cl.point; show S.cf.lgk ≤ _; omega)]
    rfl
  · rw [cti]
    show (hh.point.extract S.cf.lgk (S.cf.lgk + S.cf.lt)).size = _
    rw [size_extract_le _ Cl.point]
    omega

end H2K5.Honest

#print axioms H2K5.Honest.piecesFit_of_pairs
#print axioms H2K5.Honest.ptsFit_of
