-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LoneUnits.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the premises under which the prover's scalars are the library's rule values
(`LoneReads`, Johnson/Desc/K5/Honest/Law/RuleAll.lean), FROM WHAT THE LOOKUP HANDS ON AND THE TEXT
OF THE VERIFIER's FUNCTION OF THE POINTS. A definition of a premise, and statements with their
proofs.

It is a second source beside `loneReads_of_linPub` (Law/RuleAll.lean). That one stands on a bundle
of the tree's that holds the public test `CallsFit` whole, which says no at small made-up places.
Beside `UnitsAll`, whose clauses on the calls' sizes have a test with code, this one asks of the
lookup's numbers five clauses (`LookFits`).

Main names:
  `piecesRead_of_unit`, `planeReads_of_unit`   the pieces, and a plane claim, of a unit that is a
                                               family
                     of the library's
  `maxReads_below_of`, `maxReads_on_of`   the premises at a softmax-table unit's maximum
  `LookFits`, `lookFits_of_callsFit`   five public conditions on the lookup's numbers; the tree's
                                       test
                     `CallsFit` gives them
  `loneReads_of_units`   `LoneReads` at what the verifier's function of the points makes

EVERY STATEMENT IS CONDITIONAL. The premises that are left, and who is meant to show each:
  `Sized`, `UnitsAll` (Johnson/Desc/First/Att/K05UnitsOk.lean; it has a test with code, `unitsOk`),
    `LookFits`, `PairsAre`: public, the caller's.
  that the verifier's function of the points returns: tests on lengths alone, the caller's.
  `KeyPtsAre` (Johnson/Desc/First/Att/K05LookAll.lean): each lookup call's key point, read, is the
    library's: the lookup's to show of what it hands on.
By the tree's statements on what that function lays: `planes_are` (Claims/PlanesAre.lean), `cutU_of`
(Claims/PointsCut.lean), `cut5_of` (Claims/PointsTie.lean), `cut5w_of` (Claims/KeysPub.lean).
All the public premises say yes together, by evaluation, at two small places that the planner makes
(Johnson/Desc/K5/Honest/Law/LoneUnitsToy.lean).
Limits. `UnitsAll` says that the place has two remainder-table units and two softmax-table units: a
plan in which the layers of the group have more than one shift is not reached. `KeyPtsAre` speaks of
four lookup calls. Nothing here says that a premise holds at any place. No property is claimed by a
definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RuleAll
import Johnson.Desc.K5.Honest.Law.UnitPts
import Johnson.Desc.First.Att.K05UnitsOk
import Johnson.Desc.First.Att.Claims.PlanesAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open OnBytes.Road.L5 (callsOf)
open VerifiableInference.Desc.First.Att.P (Geo W1 RemP ScoreP DivP UnitG Heard Left Pts eqTab
  pointsOf piecesOf inner pcsSorted KeyPtsAre UnitIs UnitsAll inner_read inner_size weight_read
  unitIs_m1 unitIs_d1 u4_eq)
open K5Law (cutB UnitCut)
open Inst.Model.AttSeg hiding ibV
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## Pieces and plane claims -/

section Unit
variable {P : Pub5} {C : Calls} {z : ℕ → K} {zk : Array (Array E)} {fam : Fam} {q : Fin 4}
  {u : UnitG}

/-- **The pieces of a unit that is a family of the library's.** CONDITIONAL on: the key points,
read, are the library's; the unit is the family (public); piece b is pair b (public). -/
theorem piecesRead_of_unit (Kp : KeyPtsAre ρ C z zk) (U : UnitIs P.D C fam q u)
    (pr : PairsAre P.g (piecesOf u (zk.getD u.call #[]))) :
    PiecesRead ρ P C z fam (piecesOf u (zk.getD u.call #[])) := by
  refine ⟨?_, fun b hb => ?_, pr⟩
  · rw [← np_of_unitIs U, pieces_eq]
    simp [pcsSorted]
  · rw [pieces_wp]
    exact weight_read Kp U b hb

/-- **A plane claim whose inner point and pieces are such a unit's.** CONDITIONAL as
`piecesRead_of_unit`, and on: the claim's flag is the family's region. -/
theorem planeReads_of_unit (Kp : KeyPtsAre ρ C z zk) (U : UnitIs P.D C fam q u) {pc : RemP}
    (hz : pc.z = inner u (zk.getD u.call #[])) (hw : pc.pw = piecesOf u (zk.getD u.call #[]))
    (hr : regOf pc.isD = fam.reg) (pr : PairsAre P.g pc.pw) : PlaneReads ρ P C z fam pc := by
  refine ⟨hr, ?_, fun j hj => ?_, ?_⟩
  · rw [hz]
    exact inner_size Kp U
  · rw [hz]
    exact inner_read Kp U j hj
  · rw [hw] at pr ⊢
    exact piecesRead_of_unit ρ Kp U pr

end Unit

/-! ## The maxima -/

section Max
variable {P : Pub5} {C : Calls} {z : ℕ → K} {zk : Array (Array E)} {u : UnitG} {k : ScoreP}
  {pc : RemP}

/-- **The maximum of the unit below the diagonal.** CONDITIONAL on: `Sized`; the key points, read,
are the library's; the first two calls have one size, the unit is the library's family, piece b is
pair b (public); the unit's points are cuts of its plane claim's point, which is the unit's inner
point (the text of the verifier's function of the points). -/
theorem maxReads_below_of (H : Sized P) (Kp : KeyPtsAre ρ C z zk) (h01 : C.a 0 = C.a 1)
    (U : UnitIs P.D C .m2 1 u) (hbel : k.below = true) (Ck : UnitCut P.g k pc)
    (hz : pc.z = inner u (zk.getD u.call #[])) (hw : k.pw = piecesOf u (zk.getD u.call #[]))
    (pr : PairsAre P.g k.pw) :
    MaxReads ρ P C z .m2 k (zg P.D C z) (blkRow P.D (zP P.D C z) (zs P.D C z)) := by
  have U1 := unitIs_m1 h01 U
  have hn := H.Z.lnT
  have hs : pc.z.size =
      P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB := by
    rw [hz]
    exact inner_size Kp U1
  have rd : ∀ j, j < P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB →
      pt ρ pc.z j = uM P.D C z j := fun j hj => by
    rw [hz]
    exact inner_read Kp U1 j hj
  have cB : cutB P.g k.below = P.S.cf.lgk + (P.S.lnT - 1) + P.S.lnT := by rw [hbel]; rfl
  have ezg : k.zg = pc.z.extract 0 P.S.cf.lgk := Ck.zg
  have ezi : k.zi = pc.z.extract (P.S.cf.lgk + (P.S.lnT - 1) + P.S.lnT)
      (P.S.cf.lgk + (P.S.lnT - 1) + P.S.lnT + P.S.cf.lB) := by rw [Ck.zi, cB]; rfl
  have ew : k.wI = (OnBytes.Attention.tileSums P.S
      (OnBytes.Model.eqTab (pc.z.extract P.S.cf.lgk (P.S.cf.lgk + (P.S.lnT - 1))))
      (OnBytes.Model.eqTab (pc.z.extract (P.S.cf.lgk + (P.S.lnT - 1))
        (P.S.cf.lgk + (P.S.lnT - 1) + P.S.lnT)))).1 := by
    rw [Ck.wI, hbel, if_pos rfl, ← hbel, cB]
    rfl
  refine ⟨by rw [hw] at pr ⊢; exact piecesRead_of_unit ρ Kp U pr, ?_, fun j hj => ?_,
    fun I hI => ?_, ?_, fun j hj => ?_⟩
  · rw [ezg, size_extract_le _ (by omega)]
    rfl
  · have hj' : j < P.S.cf.lgk := hj
    rw [ezg, pt_extract ρ _ _ _ j (by omega)]
    exact rd _ (by omega)
  · rw [ew]
    refine OnBytes.Road.Rows.tiles_row ρ H.Z ?_ ?_ (fun j hj => ?_) (fun j hj => ?_)
      (by rw [OnBytes.Road.Rows.dim_nBlk H.Z]; exact hI)
    · rw [size_extract_le _ (by omega)]
      omega
    · rw [size_extract_le _ (by omega)]
      omega
    · rw [pt_extract ρ _ _ _ j (by omega)]
      exact rd _ (by omega)
    · rw [pt_extract ρ _ _ _ j (by omega)]
      exact rd _ (by omega)
  · rw [ezi, size_extract_le _ (by omega)]
    show _ = P.S.cf.lB
    omega
  · have hj' : j < P.S.cf.lB := hj
    rw [ezi, pt_extract ρ _ _ _ j (by omega), rd _ (by omega)]
    show uM P.D C z _ = uM P.D C z (P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + j)
    congr 1
    omega

/-- **The maximum of the unit on the diagonal.** CONDITIONAL as `maxReads_below_of`, and on: a piece
of the list below the diagonal is no longer than its call (public). -/
theorem maxReads_on_of (H : Sized P) (Kp : KeyPtsAre ρ C z zk) (h01 : C.a 0 = C.a 1)
    (U : UnitIs P.D C .d2 1 u) (hM : P.D.lM ≤ C.a 0) (hbel : k.below = false)
    (Ck : UnitCut P.g k pc) (hz : pc.z = inner u (zk.getD u.call #[]))
    (hw : k.pw = piecesOf u (zk.getD u.call #[])) (pr : PairsAre P.g k.pw) :
    MaxReads ρ P C z .d2 k (zgD P.D C z) (Blocks.eqN (P.D.lP + 1) 0 (zID P.D C z)) := by
  have U1 := unitIs_d1 h01 U
  have hn := H.Z.lnT
  have hM' : P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB ≤ C.a 0 := hM
  have hs : pc.z.size = P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB := by
    rw [hz]
    exact inner_size Kp U1
  have rd : ∀ j, j < P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB →
      pt ρ pc.z j = uD P.D C z j := fun j hj => by
    rw [hz]
    exact inner_read Kp U1 j hj
  have cB : cutB P.g k.below = P.S.cf.lgk + P.S.lnT := by rw [hbel]; rfl
  have ezg : k.zg = pc.z.extract 0 P.S.cf.lgk := Ck.zg
  have ezi : k.zi = pc.z.extract (P.S.cf.lgk + P.S.lnT) (P.S.cf.lgk + P.S.lnT + P.S.cf.lB) := by
    rw [Ck.zi, cB]
    rfl
  have ew : k.wI = eqTab (pc.z.extract P.S.cf.lgk (P.S.cf.lgk + P.S.lnT)) := by
    rw [Ck.wI, hbel, if_neg (by decide), ← hbel, cB]
    rfl
  refine ⟨by rw [hw] at pr ⊢; exact piecesRead_of_unit ρ Kp U pr, ?_, fun j hj => ?_,
    fun I hI => ?_, ?_, fun j hj => ?_⟩
  · rw [ezg, size_extract_le _ (by omega)]
    rfl
  · have hj' : j < P.S.cf.lgk := hj
    rw [ezg, pt_extract ρ _ _ _ j (by omega)]
    exact rd _ (by omega)
  · rw [ew]
    refine read_eqTab ρ ?_ (fun j hj => ?_) (by rw [Cb.Pv.Att.nBlk_pow]; exact hI)
    · rw [size_extract_le _ (by omega)]
      show P.S.cf.lgk + P.S.lnT - P.S.cf.lgk = P.S.lnT - 1 + 1
      omega
    · have hj' : j < P.S.lnT - 1 + 1 := hj
      rw [pt_extract ρ _ _ _ j (by omega)]
      exact rd _ (by omega)
  · rw [ezi, size_extract_le _ (by omega)]
    show _ = P.S.cf.lB
    omega
  · have hj' : j < P.S.cf.lB := hj
    rw [ezi, pt_extract ρ _ _ _ j (by omega), rd _ (by omega)]
    show C.zC 0 z (C.a 0 - (P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB) +
        (P.S.cf.lgk + P.S.lnT + j)) =
      C.zC 0 z (C.a 0 - (P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB) +
        (P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + j))
    congr 1
    omega

end Max

/-! ## The whole, at what the verifier's function of the points makes -/

/-- A list whose image under f has two members has two members. -/
theorem two_of_map {α β : Type} {f : α → β} {l : List α} {b0 b1 : β} (h : l.map f = [b0, b1]) :
    ∃ a0 a1, l = [a0, a1] ∧ f a0 = b0 ∧ f a1 = b1 := by
  match l, h with
  | [a0, a1], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨a0, a1, rfl, h.1, h.2⟩

/-- **The public conditions on the lookup's numbers** that the ties between the lists' inner points
spend: the first two calls have one size; a piece of the list below the diagonal is no longer than
its call; a piece of the list of the remainders' low bits is no longer than a tree, and a tree no
longer than the last two calls. They are fewer than the tree's public test `CallsFit`
(Johnson/Road/Lane5CallsOf.lean) asks: `lookFits_of_callsFit`. -/
structure LookFits (D : Dim) (C : Calls) : Prop where
  a01 : C.a 0 = C.a 1
  lM : D.lM ≤ C.a 0
  lW : D.lW ≤ C.Dk
  a2 : C.Dk ≤ C.a 2
  a3 : C.Dk ≤ C.a 3

/-- The tree's public test on the lookup's numbers gives the five. -/
theorem lookFits_of_callsFit {S : OnBytes.Attention.Shape} {fs : OnBytes.Model.Forest.Shape}
    (h : OnBytes.Road.L5.CallsFit S fs) : LookFits (OnBytes.Road.L5.dimOf S) (callsOf fs) :=
  ⟨OnBytes.Road.L5.callsFit_a01 h, (OnBytes.Road.L5.callsFit_deep h .m1).trans (h.2.1 0),
    OnBytes.Road.L5.callsFit_deep h .w3, h.2.1 2, h.2.1 3⟩

/-- **`LoneReads` at what the verifier's function of the points makes.** pM, pD: its first two plane
claims; kM, kD: its two units, with the plane claims cM, cD. CONDITIONAL on: `Sized`, `UnitsAll`
(Johnson/Desc/First/Att/K05UnitsOk.lean: the place's seven units are the library's seven families;
it has a test with code), `LookFits`, seven times "piece b is pair b": public; the function returns
(tests on lengths alone); `KeyPtsAre`: the key points, read, are the library's: the lookup's to show
of what it hands on. -/
theorem loneReads_of_units {P : Pub5} {fs : OnBytes.Model.Forest.Shape}
    {r1 r2 u1 u2 wl ix wh : UnitG} (H : Sized P) (U : UnitsAll P.S fs r1 r2 u1 u2 wl ix wh)
    (F : LookFits P.D (callsOf fs)) {zk : Array (Array E)} {h : Heard} {L : Left} {pts : Pts}
    (hp : pointsOf P.g zk h L = some pts) {p : Pub K} (Kp : KeyPtsAre ρ (callsOf fs) p.z zk)
    {pM pD cM cD : RemP} {kM kD : ScoreP} (e0 : pts.planes[0]? = some pM)
    (e1 : pts.planes[1]? = some pD) (k0 : pts.scores[0]? = some kM)
    (k1 : pts.scores[1]? = some kD) (c0 : pts.planes[kM.claim]? = some cM)
    (c1 : pts.planes[kD.claim]? = some cD) (prM : PairsAre P.g pM.pw) (prD : PairsAre P.g pD.pw)
    (qrM : PairsAre P.g kM.pw) (qrD : PairsAre P.g kD.pw) (prW : PairsAre P.g pts.d.pwW)
    (prX : PairsAre P.g pts.d.pwX) (prH : PairsAre P.g pts.d.pwH) :
    LoneReads ρ P (callsOf fs) p pM pD cM cD kM kD pts.d := by
  have hn := H.Z.lnT
  have htok : P.S.cf.lt = P.S.lnT + P.S.cf.lB := H.tok
  have Pl := K5Law.planes_are hp
  have PA := K5Law.points_are hp
  have CU := K5Law.cutU_of hp
  -- the two remainder-table units
  obtain ⟨a0, a1, hu0, f0, f1⟩ := two_of_map U.rem
  have hu : P.g.units .kr [.rm, .rd] = [a0, a1] := hu0
  have hsco : P.g.scores = [u1, u2] := U.sco
  have nR : h.remainders.size = 2 := by rw [← Pl.nR, hu]; rfl
  have m0 : a0 ∈ P.g.units .kr [.rm, .rd] := by rw [hu]; exact List.mem_cons_self
  have m1 : a1 ∈ P.g.units .kr [.rm, .rd] := by
    rw [hu]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have q0 := Pl.rem 0 a0 _ (by rw [hu]; rfl) (Array.getElem?_eq_getElem (by omega : 0 < _))
  have q1 := Pl.rem 1 a1 _ (by rw [hu]; rfl) (Array.getElem?_eq_getElem (by omega : 1 < _))
  obtain rfl : K5Law.remAt P.g zk a0 _ = pM := Option.some.inj (q0.symm.trans e0)
  obtain rfl : K5Law.remAt P.g zk a1 _ = pD := Option.some.inj (q1.symm.trans e1)
  have b0 : P.g.keyBits a0.2.2 =
      P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB := by
    have hb := U.m1.bits
    rw [← f0] at hb
    exact hb
  have b1 : P.g.keyBits a1.2.2 = P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB := by
    have hb := U.d1.bits
    rw [← f1] at hb
    exact hb
  have t0 : a0.2.2 = .rm := by
    have hk := K5Law.units_keys P.g _ _ a0 m0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hk | hk
    · exact hk
    · rw [hk] at b0
      have b0' : P.S.cf.lgk + P.S.cf.lt + P.S.cf.lB =
        P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB := b0
      omega
  have t1 : a1.2.2 = .rd := by
    have hk := K5Law.units_keys P.g _ _ a1 m1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hk | hk
    · rw [hk] at b1
      have b1' : P.S.cf.lgk + 2 * P.S.cf.lt - 1 =
        P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB := b1
      omega
    · exact hk
  -- the two softmax-table units
  have nS : h.scores.size = 2 := by rw [← PA.nH, hsco]; rfl
  obtain ⟨x0, y0, _, z0, _, w0, v0, _⟩ := Pl.unit 0 u1 _ (by rw [hsco]; rfl)
    (Array.getElem?_eq_getElem (by omega : 0 < _))
  obtain ⟨x1, y1, _, z1, _, w1, v1, _⟩ := Pl.unit 1 u2 _ (by rw [hsco]; rfl)
    (Array.getElem?_eq_getElem (by omega : 1 < _))
  obtain rfl : x0 = kM := Option.some.inj (y0.symm.trans k0)
  obtain rfl : x1 = kD := Option.some.inj (y1.symm.trans k1)
  obtain rfl : K5Law.remOfUnit zk u1 _ = cM := Option.some.inj (z0.symm.trans c0)
  obtain rfl : K5Law.remOfUnit zk u2 _ = cD := Option.some.inj (z1.symm.trans c1)
  obtain ⟨pc0, g0, C0⟩ := CU.units x0 (Array.mem_toList_iff.2 (Array.mem_of_getElem? k0))
  obtain ⟨pc1, g1, C1⟩ := CU.units x1 (Array.mem_toList_iff.2 (Array.mem_of_getElem? k1))
  obtain rfl := Option.some.inj (g0.symm.trans c0)
  obtain rfl := Option.some.inj (g1.symm.trans c1)
  -- the three lists that one call alone serves
  obtain ⟨uW, uX, uH, sW, sX, sH, nW, nX, nH, _, gW, iW, cW, gX, iX, gH, iH, cH⟩ :=
    (K5Law.cut5_of hp).at'
  obtain ⟨uW', uX', uH', sW', sX', sH', pW, pX, pH, _, _, _⟩ := (K5Law.cut5w_of hp).at'
  obtain rfl : wl = uW := Option.some.inj (U.sWl.symm.trans sW)
  obtain rfl : wl = uW' := Option.some.inj (U.sWl.symm.trans sW')
  obtain rfl : ix = uX := Option.some.inj (U.sIx.symm.trans sX)
  obtain rfl : wh = uH := Option.some.inj (U.sWh.symm.trans sH)
  obtain rfl : ix = uX' := Option.some.inj (U.sIx.symm.trans sX')
  obtain rfl : wh = uH' := Option.some.inj (U.sWh.symm.trans sH')
  have nW' : (inner wl (zk.getD wl.call #[])).size =
      1 + P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh := nW
  have nX' : (inner ix (zk.getD ix.call #[])).size = P.S.cf.lgk + P.S.cf.lt := nX
  have nH' : (inner wh (zk.getD wh.call #[])).size = P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh := nH
  have hlT : P.D.lT = P.S.cf.lt := H.lt.symm
  have rW : ∀ j, j < 1 + P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh →
      pt ρ (inner wl (zk.getD wl.call #[])) j = uW P.D (callsOf fs) p.z j := fun j hj =>
    inner_read Kp U.w3 j (by
      show j < 1 + P.D.lg + P.D.lT + P.D.ln
      rw [hlT]
      exact hj)
  have rX : ∀ j, j < P.S.cf.lgk + P.S.cf.lt →
      pt ρ (inner ix (zk.getD ix.call #[])) j = uX P.D (callsOf fs) p.z j := fun j hj =>
    inner_read Kp U.x3 j (by
      show j < P.D.lg + P.D.lT
      rw [hlT]
      exact hj)
  have rH : ∀ j, j < P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh →
      pt ρ (inner wh (zk.getD wh.call #[])) j = uW P.D (callsOf fs) p.z (1 + j) := fun j hj => by
    refine (inner_read Kp U.f4 j (by
      show j < P.D.lg + P.D.lT + P.D.ln
      rw [hlT]
      exact hj)).trans ?_
    show u4 P.D (callsOf fs) p.z j = _
    rw [u4_eq P.D (callsOf fs) p.z F.lW F.a2 F.a3]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_, ?_⟩
  · refine planeReads_of_unit ρ Kp U.m1 ?_ ?_ ?_ prM
    · rw [← f0]
      rfl
    · rw [← f0]
      rfl
    · show regOf (a0.2.2 == .rd) = _
      rw [t0]
      rfl
  · refine planeReads_of_unit ρ Kp U.d1 ?_ ?_ ?_ prD
    · rw [← f1]
      rfl
    · rw [← f1]
      rfl
    · show regOf (a1.2.2 == .rd) = _
      rw [t1]
      rfl
  · refine planeReads_of_unit ρ Kp U.m2 rfl rfl ?_ (by
      have h1 := qrM
      rw [v0] at h1
      exact h1)
    show regOf (!u1.below) = _
    rw [U.below]
    rfl
  · refine planeReads_of_unit ρ Kp U.d2 rfl rfl ?_ (by
      have h1 := qrD
      rw [v1] at h1
      exact h1)
    show regOf (!u2.below) = _
    rw [U.on]
    rfl
  · exact maxReads_below_of ρ H Kp F.a01 U.m2 (w0.trans U.below) C0 rfl v0 qrM
  · exact maxReads_on_of ρ H Kp F.a01 U.d2 F.lM (w1.trans U.on) C1 rfl v1 qrD
  · refine (lonePts_iff ρ (callsOf fs) p).2 ⟨by
      rw [pW] at prW ⊢
      exact piecesRead_of_unit ρ Kp U.w3 prW, ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_,
      fun j hj => ?_⟩
    · rw [gW, size_extract_le _ (by rw [nW']; show 1 + P.S.cf.lgk ≤ _; omega)]
      show 1 + P.S.cf.lgk - 1 = P.S.cf.lgk
      omega
    · have hj' : j < P.S.cf.lgk := hj
      rw [gW, pt_extract ρ _ _ _ j (by show 1 + j < 1 + P.S.cf.lgk; omega)]
      exact rW _ (by omega)
    · rw [iW, size_extract_le _ (by rw [nW']; show 1 + P.S.cf.lgk + P.S.cf.lt ≤ _; omega), hlT]
      show 1 + P.S.cf.lgk + P.S.cf.lt - (1 + P.S.cf.lgk) = _
      omega
    · have hj' : j < P.S.cf.lt := by rw [← hlT]; exact hj
      rw [iW, pt_extract ρ _ _ _ j (by
        show 1 + P.S.cf.lgk + j < 1 + P.S.cf.lgk + P.S.cf.lt
        omega)]
      exact rW _ (by show 1 + P.S.cf.lgk + j < _; omega)
    · rw [cW, size_extract_le _ (by rw [nW']; exact Nat.le_refl _)]
      show 1 + P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh - (1 + P.S.cf.lgk + P.S.cf.lt) = P.S.cf.ldh
      omega
    · have hj' : j < P.S.cf.ldh := hj
      rw [cW, pt_extract ρ _ _ _ j (by
        show 1 + P.S.cf.lgk + P.S.cf.lt + j < 1 + P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh
        omega), rW _ (by show 1 + P.S.cf.lgk + P.S.cf.lt + j < _; omega)]
      show uW P.D (callsOf fs) p.z (1 + P.S.cf.lgk + P.S.cf.lt + j) =
        uW P.D (callsOf fs) p.z (1 + P.S.cf.lgk + P.D.lT + j)
      rw [hlT]
  · rw [pX] at prX ⊢
    exact piecesRead_of_unit ρ Kp U.x3 prX
  · rw [gX, size_extract_le _ (by rw [nX']; show P.S.cf.lgk ≤ _; omega)]
    rfl
  · have hj' : j < P.S.cf.lgk := hj
    rw [gX, pt_extract ρ _ _ _ j (by show 0 + j < P.S.cf.lgk; omega)]
    exact rX _ (by omega)
  · rw [iX, size_extract_le _ (by rw [nX']; exact Nat.le_refl _), hlT]
    show P.S.cf.lgk + P.S.cf.lt - P.S.cf.lgk = _
    omega
  · have hj' : j < P.S.cf.lt := by rw [← hlT]; exact hj
    rw [iX, pt_extract ρ _ _ _ j (by show P.S.cf.lgk + j < P.S.cf.lgk + P.S.cf.lt; omega)]
    exact rX _ (by show P.S.cf.lgk + j < _; omega)
  · rw [pH] at prH ⊢
    exact piecesRead_of_unit ρ Kp U.f4 prH
  · refine ⟨?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_⟩
    · rw [gH, size_extract_le _ (by rw [nH']; show P.S.cf.lgk ≤ _; omega)]
      rfl
    · have hj' : j < P.S.cf.lgk := hj
      rw [gH, pt_extract ρ _ _ _ j (by show 0 + j < P.S.cf.lgk; omega), rH _ (by omega)]
      show uW P.D (callsOf fs) p.z (1 + (0 + j)) = uW P.D (callsOf fs) p.z (1 + j)
      rw [Nat.zero_add]
    · rw [iH, size_extract_le _ (by rw [nH']; show P.S.cf.lgk + P.S.cf.lt ≤ _; omega), hlT]
      show P.S.cf.lgk + P.S.cf.lt - P.S.cf.lgk = _
      omega
    · have hj' : j < P.S.cf.lt := by rw [← hlT]; exact hj
      rw [iH, pt_extract ρ _ _ _ j (by show P.S.cf.lgk + j < P.S.cf.lgk + P.S.cf.lt; omega),
        rH _ (by show P.S.cf.lgk + j < _; omega)]
      show uW P.D (callsOf fs) p.z (1 + (P.S.cf.lgk + j)) =
        uW P.D (callsOf fs) p.z (1 + P.S.cf.lgk + j)
      rw [Nat.add_assoc]
    · rw [cH, size_extract_le _ (by rw [nH']; exact Nat.le_refl _)]
      show P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh - (P.S.cf.lgk + P.S.cf.lt) = P.S.cf.ldh
      omega
    · have hj' : j < P.S.cf.ldh := hj
      rw [cH, pt_extract ρ _ _ _ j (by
          show P.S.cf.lgk + P.S.cf.lt + j < P.S.cf.lgk + P.S.cf.lt + P.S.cf.ldh
          omega), rH _ (by show P.S.cf.lgk + P.S.cf.lt + j < _; omega)]
      show uW P.D (callsOf fs) p.z (1 + (P.S.cf.lgk + P.S.cf.lt + j)) =
        uW P.D (callsOf fs) p.z (1 + P.S.cf.lgk + P.D.lT + j)
      rw [hlT]
      congr 1
      omega

end H2K5.Honest

#print axioms H2K5.Honest.piecesRead_of_unit
#print axioms H2K5.Honest.planeReads_of_unit
#print axioms H2K5.Honest.maxReads_below_of
#print axioms H2K5.Honest.maxReads_on_of
#print axioms H2K5.Honest.two_of_map
#print axioms H2K5.Honest.lookFits_of_callsFit
#print axioms H2K5.Honest.loneReads_of_units
