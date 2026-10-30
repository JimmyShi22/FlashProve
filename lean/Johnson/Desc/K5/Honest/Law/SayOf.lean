-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/SayOf.lean: CONDITIONAL: what the claims of an attention segment's own
rounds say (Say3, UnitAt, Johnson/Desc/First/Att/Claims/Say.lean; Say5 .. Say8, Claims/Say58.lean),
claim by claim, FROM TWO HALVES: "the written form is worth the slot less the prover's value, read",
or "the reader's form is worth the prover's value, read" (Meets..); and "the slot is worth the
prover's value, read" (Under..). Definitions of propositions, and statements with their proofs. The
world is any; the reading is the library's own. No frame of a prover is imported.

All values are those of the prover's functions AT THE VERIFIER's OWN NAMED POINTS i.p: no list of
challenges of the prover's occurs.

  MeetsPlanes, MeetsUnit, Meets5, MeetsV, Meets7, Meets8   the first half, clause by clause, each
                 clause in the form in which Johnson/Desc/K5/Honest/Law/AloneMeets.lean,
                 EndsMeet.lean and EndsMeetIndex.lean conclude it, at oldOf S gL i
  UnderPlanes, UnderUnit, Under5, UnderV, Under7, Under8   the second half
  planes_of, say3_of, unit_of, say5_of, say6_of, say7_of, say8_of
                 CONDITIONAL: **the claim's sentence, from the two halves** and the worth 0 of the
                 rows that the claim's sumchecks leave; say6_of also from the equation of the value
                 product on the four values that lie under its slots

Who is meant to show the premises. Meets..: whoever lays the world, the matrices and the tables.
Under..: whoever says what lies under a slot. The rows: whoever shows that a masked sumcheck's row
is worth 0. NOTHING HERE SHOWS THAT ANY OF THESE HOLDS ANYWHERE.

Limits. Rewriting alone. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.EndsMeet
import Johnson.Desc.K5.Honest.Law.EndsMeetIndex
import Johnson.Desc.First.Att.Claims.SayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Reading Aff World Forest.Heard)
open OnBytes.Slice (GE)
open OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (RemP ScoreP ScoreT DivP MaxP SumP geoOf)
open K5Law (oldOf remBack scoreBack tbBack sum3Back PlanesSay Say3 UnitAt Say5 ProdSay Say6 Say7
  Say8)

variable (W : World GE) (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (K : Nat) (w : K5In)

/-! ## 1 The plane claims: claim 3, and a part of claim 4 -/

/-- A member of a plane claim is worth the slot less the prover's value. It is a definition. -/
def MeetsPlanes : Prop :=
  ∀ u ∈ i.p.planes.toList, ∀ y, y < u.np →
    (Fo.planeMember (oldOf S gL i) K (remBack u) y).value Reading.gl W =
      W.slot (u.s0 + y) - Reading.gl.val (planeOf (geoOf S) w u y)

/-- Under a plane claim's slots lie the prover's values. It is a definition. -/
def UnderPlanes : Prop :=
  ∀ u ∈ i.p.planes.toList, ∀ y, y < u.np →
    W.slot (u.s0 + y) = Reading.gl.val (planeOf (geoOf S) w u y)

variable {W S gL i K w}

theorem planes_of (M : MeetsPlanes W S gL i K w) (U : UnderPlanes W S i w) {u : RemP}
    (hu : u ∈ i.p.planes.toList) : PlanesSay Reading.gl W (oldOf S gL i) K (remBack u) :=
  fun y hy => by rw [M u hu y hy, U u hu y hy, sub_self]

/-- **Claim 3.** CONDITIONAL: the two halves on the plane claims. -/
theorem say3_of (M : MeetsPlanes W S gL i K w) (U : UnderPlanes W S i w) :
    Say3 Reading.gl W (oldOf S gL i) K := by
  intro x _ _ pc hpc _
  have h1 : pc ∈ (i.p.planes.map remBack).toList := hpc
  rw [Array.toList_map] at h1
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 h1
  exact planes_of M U hu

/-! ## 2 A softmax-table unit: claim 4 -/

variable (W S gL i K w)

/-- The first half at a unit k with the tables tb. It is a definition. -/
structure MeetsUnit (k : ScoreP) (tb : ScoreT) : Prop where
  maximum : (Fo.lessF (Aff.slot (k.s0 + 5)) (K5Law.pwBack k.pw) fun x =>
      Fo.readMaximumF (oldOf S gL i) K tb.tM k.zg x.lam x.a).value Reading.gl W =
    W.slot (k.s0 + 5) - Reading.gl.val (maxAt (geoOf S) w k)
  ends : ∀ j, j < 2 * k.pw.size →
    (K5Law.endsU (oldOf S gL i) K (scoreBack k) (tbBack tb) j).value Reading.gl W =
      Reading.gl.val (if j % 2 = 0 then unitA (geoOf S) w k k.sc.r (j / 2)
        else unitB (geoOf S) w k k.sc.r (j / 2))

/-- The second half at a unit. It is a definition. -/
structure UnderUnit (k : ScoreP) : Prop where
  maximum : W.slot (k.s0 + 5) = Reading.gl.val (maxAt (geoOf S) w k)
  ends : ∀ j, j < 2 * k.pw.size → W.slot (k.sc.ends + j) =
    Reading.gl.val (if j % 2 = 0 then unitA (geoOf S) w k k.sc.r (j / 2)
      else unitB (geoOf S) w k k.sc.r (j / 2))

variable {W S gL i K w}

/-- **A unit of claim 4.** CONDITIONAL: the halves on the plane claims and on the unit; pc is one of
the plane claims of i.p; the row is worth 0. -/
theorem unit_of (MP : MeetsPlanes W S gL i K w) (UP : UnderPlanes W S i w) {k : ScoreP}
    {tb : ScoreT} {pc : RemP} (hpc : pc ∈ i.p.planes.toList) (M : MeetsUnit W S gL i K w k tb)
    (U : UnderUnit W S w k) (hr : k.sc.row.value Reading.gl W = 0) :
    UnitAt Reading.gl W (oldOf S gL i) K (scoreBack k) (tbBack tb) (remBack pc) :=
  { planes := planes_of MP UP hpc
    maximum := by
      show (Fo.lessF (Aff.slot (k.s0 + 5)) (K5Law.pwBack k.pw) fun x =>
        Fo.readMaximumF (oldOf S gL i) K tb.tM k.zg x.lam x.a).value Reading.gl W = 0
      rw [M.maximum, U.maximum, sub_self]
    row := hr
    ends := fun j hj => by
      have hj' : j < 2 * k.pw.size := by
        have e : (scoreBack k).pw.size = k.pw.size := Array.size_map ..
        rw [e] at hj
        exact hj
      rw [M.ends j hj']
      exact U.ends j hj' }

/-! ## 3 The division: claim 5 -/

variable (W S gL i K w)

/-- The first half of claim 5. It is a definition. -/
structure Meets5 : Prop where
  zc : (Fo.lessF (Aff.slot (i.p.d.s5 + 2)) (K5Law.pwBack i.p.d.pwW) fun x =>
      Fo.readDenominatorF (oldOf S gL i) K i.t.hW i.p.d.zgW x.lam x.a).value Reading.gl W =
    W.slot (i.p.d.s5 + 2) -
      Reading.gl.val (atRow (geoOf S) i.p.d.pwW i.p.d.zgW i.p.d.ziW w.zd)
  rh : (Fo.lessF (Aff.slot (i.p.d.s5 + 3)) (K5Law.pwBack i.p.d.pwW) fun x =>
      Fo.readHeadT (oldOf S gL i) K i.t.tO (atRh S) i.p.d.zgW i.p.d.zcW x.lam x.a).value
        Reading.gl W =
    W.slot (i.p.d.s5 + 3) -
      Reading.gl.val (atChan (geoOf S) i.p.d.pwW i.p.d.zgW i.p.d.ziW i.p.d.zcW w.rh)
  rhp : (Fo.lessF (Aff.slot (i.p.d.s5 + 4)) (K5Law.pwBack i.p.d.pwW) fun x =>
      Fo.readHeadT (oldOf S gL i) K i.t.tO (atRhp S) i.p.d.zgW i.p.d.zcW x.lam x.a).value
        Reading.gl W =
    W.slot (i.p.d.s5 + 4) -
      Reading.gl.val (atChan (geoOf S) i.p.d.pwW i.p.d.zgW i.p.d.ziW i.p.d.zcW w.rhp)
  ib : ∀ k, k < S.cf.lt → (Fo.lessF (Aff.slot (i.p.d.sIB + k)) (K5Law.pwBack i.p.d.pwX) fun x =>
      Fo.readIndexBitF (oldOf S gL i) K i.t.hX i.p.d.zgX x.lam x.a k).value Reading.gl W =
    W.slot (i.p.d.sIB + k) -
      Reading.gl.val (atRow (geoOf S) i.p.d.pwX i.p.d.zgX i.p.d.ziX (w.ibit k))
  r2 : (Fo.lessF (Aff.slot i.p.d.s5h) (K5Law.pwBack i.p.d.pwH) fun x =>
      Fo.readHeadT (oldOf S gL i) K i.t.tO (atRh S) i.p.d.zgH i.p.d.zcH x.lam x.a).value
        Reading.gl W =
    W.slot i.p.d.s5h -
      Reading.gl.val (atChan (geoOf S) i.p.d.pwH i.p.d.zgH i.p.d.ziH i.p.d.zcH w.rh)
  r2p : (Fo.lessF (Aff.slot (i.p.d.s5h + 1)) (K5Law.pwBack i.p.d.pwH) fun x =>
      Fo.readHeadT (oldOf S gL i) K i.t.tO (atRhp S) i.p.d.zgH i.p.d.zcH x.lam x.a).value
        Reading.gl W =
    W.slot (i.p.d.s5h + 1) -
      Reading.gl.val (atChan (geoOf S) i.p.d.pwH i.p.d.zgH i.p.d.ziH i.p.d.zcH w.rhp)
  ends : ∀ j, j < 2 * S.NP → (K5Law.endsE (oldOf S gL i) K j).value Reading.gl W =
    Reading.gl.val (if j % 2 = 0 then seA (geoOf S) w i.p.d.pwW i.p.d.scE.r (j / 2)
      else seB (geoOf S) w i.p.d.pwW (P.eqTab i.p.d.zcW) i.p.d.scE.r (j / 2))

/-- The second half of claim 5. It is a definition. -/
structure Under5 : Prop where
  zc : W.slot (i.p.d.s5 + 2) = Reading.gl.val (zcAt (geoOf S) w i.p.d)
  rh : W.slot (i.p.d.s5 + 3) = Reading.gl.val (rhAt (geoOf S) w i.p.d)
  rhp : W.slot (i.p.d.s5 + 4) = Reading.gl.val (rhpAt (geoOf S) w i.p.d)
  ib : ∀ k, k < S.cf.lt → W.slot (i.p.d.sIB + k) =
    Reading.gl.val (atRow (geoOf S) i.p.d.pwX i.p.d.zgX i.p.d.ziX (w.ibit k))
  r2 : W.slot i.p.d.s5h = Reading.gl.val (rh2At (geoOf S) w i.p.d)
  r2p : W.slot (i.p.d.s5h + 1) = Reading.gl.val (rhp2At (geoOf S) w i.p.d)
  ends : ∀ j, j < 2 * S.NP → W.slot (i.p.d.scE.ends + j) =
    Reading.gl.val (if j % 2 = 0 then seA (geoOf S) w i.p.d.pwW i.p.d.scE.r (j / 2)
      else seB (geoOf S) w i.p.d.pwW (P.eqTab i.p.d.zcW) i.p.d.scE.r (j / 2))

variable {W S gL i K w}

/-- **Claim 5.** CONDITIONAL: the two halves; the row is worth 0. -/
theorem say5_of (M : Meets5 W S gL i K w) (U : Under5 W S i w)
    (hr : i.p.d.scE.row.value Reading.gl W = 0) : Say5 Reading.gl W (oldOf S gL i) K :=
  { zc := (M.zc.trans (by rw [U.zc]; exact sub_self _))
    rh := (M.rh.trans (by rw [U.rh]; exact sub_self _))
    rhp := (M.rhp.trans (by rw [U.rhp]; exact sub_self _))
    ib := fun k hk => ((M.ib k hk).trans (by rw [U.ib k hk]; exact sub_self _))
    r2 := (M.r2.trans (by rw [U.r2]; exact sub_self _))
    r2p := (M.r2p.trans (by rw [U.r2p]; exact sub_self _))
    row := hr
    ends := fun j hj => (U.ends j hj).trans (M.ends j hj).symm }

/-! ## 4 The value product: claim 6 -/

variable (W S gL i K w)

/-- The first half of claim 6: the end values of the two sumchecks. It is a definition. -/
structure MeetsV : Prop where
  below : ∀ j, j < 2 * S.NP →
    (K5Law.endsV (oldOf S gL i) K (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM j).value
        Reading.gl W =
      Reading.gl.val (if j % 2 = 0 then vmA (geoOf S) w i.p.d i.p.d.vpm.r (j / 2)
        else vmB (geoOf S) w i.p.d (P.eqTab i.p.d.zcW) i.p.d.vpm.r (j / 2))
  on : ∀ j, j < 2 * S.NP →
    (K5Law.endsV (oldOf S gL i) K (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD j).value
        Reading.gl W =
      Reading.gl.val (if j % 2 = 0 then vdA (geoOf S) w i.p.d i.p.d.vpd.r (j / 2)
        else vdB (geoOf S) w i.p.d (P.eqTab i.p.d.zcW) i.p.d.vpd.r (j / 2))

/-- The second half of claim 6. v0, v1, vA, vZ: the four values under the slots of its first clause:
the two sums, the accumulated output, the denominator. It is a definition. -/
structure UnderV (v0 v1 vA vZ : E) : Prop where
  cl0 : W.slot i.p.d.sCl = Reading.gl.val v0
  cl1 : W.slot (i.p.d.sCl + 1) = Reading.gl.val v1
  acc : W.slot i.p.d.s5 = Reading.gl.val vA
  zc : W.slot (i.p.d.s5 + 2) = Reading.gl.val vZ
  below : ∀ j, j < 2 * S.NP → W.slot (i.p.d.vpm.ends + j) =
    Reading.gl.val (if j % 2 = 0 then vmA (geoOf S) w i.p.d i.p.d.vpm.r (j / 2)
      else vmB (geoOf S) w i.p.d (P.eqTab i.p.d.zcW) i.p.d.vpm.r (j / 2))
  on : ∀ j, j < 2 * S.NP → W.slot (i.p.d.vpd.ends + j) =
    Reading.gl.val (if j % 2 = 0 then vdA (geoOf S) w i.p.d i.p.d.vpd.r (j / 2)
      else vdB (geoOf S) w i.p.d (P.eqTab i.p.d.zcW) i.p.d.vpd.r (j / 2))

variable {W S gL i K w}

/-- **Claim 6.** CONDITIONAL: the two halves; the two rows are worth 0; he: the equation of the
value product on the four values. -/
theorem say6_of (M : MeetsV W S gL i K w) {v0 v1 vA vZ : E} (U : UnderV W S i w v0 v1 vA vZ)
    (he : Reading.gl.val v0 + Reading.gl.val v1 - Reading.gl.val vA -
      Reading.gl.val i.p.d.gam * Reading.gl.val vZ = 0)
    (hM : i.p.d.vpm.row.value Reading.gl W = 0) (hD : i.p.d.vpd.row.value Reading.gl W = 0) :
    Say6 Reading.gl W (oldOf S gL i) K :=
  { acc := by
      show W.slot i.p.d.sCl + W.slot (i.p.d.sCl + 1) - W.slot i.p.d.s5 -
        Reading.gl.val i.p.d.gam * W.slot (i.p.d.s5 + 2) = 0
      rw [U.cl0, U.cl1, U.acc, U.zc]
      exact he
    below := ⟨hM, fun j hj => (U.below j hj).trans (M.below j hj).symm⟩
    on := ⟨hD, fun j hj => (U.on j hj).trans (M.on j hj).symm⟩ }

/-! ## 5 The maximum and its index: claim 7 -/

variable (W S gL i K w)

/-- The first half of claim 7. It is a definition. -/
structure Meets7 : Prop where
  maxima : ∀ b, b < S.NP →
    (Fo.readMaximumF (oldOf S gL i) K i.t.hT i.p.x.tg (b / S.HA) (b % S.HA)).value Reading.gl W =
      Reading.gl.val (under (P.eqTab i.p.x.tg) fun hk => under (P.eqTab i.p.x.ti) fun t =>
        w.mx b hk t)
  endsF : ∀ b, b < S.NP →
    (Fo.readHeadT (oldOf S gL i) K i.t.qF S.atQ ((oldOf S gL i).x.rg S) ((oldOf S gL i).x.rc S)
      (b / S.HA) (b % S.HA)).value Reading.gl W =
      Reading.gl.val (under3 S.cf.lt S.cf.lgk S.cf.ldh i.p.x.scF.r (sfTab (geoOf S) w (2 * b)))
  lam : ∀ l, l < S.Lam → (K5Law.endsK (oldOf S gL i) K l).value Reading.gl W =
    Reading.gl.val (kcAt (geoOf S) i.p.x.scd.r (kcTab (geoOf S) w i.p.x.scF.r l))
  bit : ∀ b k, b < S.NP → k < S.cf.lt →
    (K5Law.endsK (oldOf S gL i) K (S.Lam + b * S.cf.lt + k)).value Reading.gl W =
      Reading.gl.val (ibpAt (geoOf S) w i.p.x.scd.r k b)

/-- The second half of claim 7. It is a definition. -/
structure Under7 : Prop where
  maxima : ∀ b, b < S.NP → W.slot (i.p.x.sM6 + b) =
    Reading.gl.val (under (P.eqTab i.p.x.tg) fun hk => under (P.eqTab i.p.x.ti) fun t =>
      w.mx b hk t)
  endsF : ∀ b, b < S.NP → W.slot (i.p.x.scF.ends + 2 * b) =
    Reading.gl.val (under3 S.cf.lt S.cf.lgk S.cf.ldh i.p.x.scF.r (sfTab (geoOf S) w (2 * b)))
  lam : ∀ l, l < S.Lam → W.slot (i.p.x.scd.ends + l) =
    Reading.gl.val (kcAt (geoOf S) i.p.x.scd.r (kcTab (geoOf S) w i.p.x.scF.r l))
  bit : ∀ b k, b < S.NP → k < S.cf.lt → W.slot (i.p.x.scd.ends + (S.Lam + b * S.cf.lt + k)) =
    Reading.gl.val (ibpAt (geoOf S) w i.p.x.scd.r k b)

variable {W S gL i K w}

/-- **Claim 7.** CONDITIONAL: the two halves; the two rows are worth 0. -/
theorem say7_of (M : Meets7 W S gL i K w) (U : Under7 W S i w)
    (hF : i.p.x.scF.row.value Reading.gl W = 0) (hK : i.p.x.scd.row.value Reading.gl W = 0) :
    Say7 Reading.gl W (oldOf S gL i) K :=
  { maxima := fun b hb => (U.maxima b hb).trans (M.maxima b hb).symm
    rowF := hF
    endsF := fun b hb => (U.endsF b hb).trans (M.endsF b hb).symm
    rowK := hK
    endsK := fun j hj => by
      have hj' : j < S.Lam + S.NP * S.cf.lt := hj
      show W.slot (i.p.x.scd.ends + j) = _
      by_cases hl : j < S.Lam
      · exact (U.lam j hl).trans (M.lam j hl).symm
      · have hpos : 0 < S.cf.lt := by
          rcases Nat.eq_zero_or_pos S.cf.lt with e | e
          · rw [e, Nat.mul_zero] at hj'
            omega
          · exact e
        have hb : (j - S.Lam) / S.cf.lt < S.NP :=
          Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
        have hk : (j - S.Lam) % S.cf.lt < S.cf.lt := Nat.mod_lt _ hpos
        have ej : j = S.Lam + (j - S.Lam) / S.cf.lt * S.cf.lt + (j - S.Lam) % S.cf.lt := by
          have := Nat.div_add_mod' (j - S.Lam) S.cf.lt
          omega
        rw [ej]
        exact (U.bit _ _ hb hk).trans (M.bit _ _ hb hk).symm }

/-! ## 6 The index's cells are bits: claim 8 -/

variable (W S gL i K w)

/-- The first half of claim 8. It is a definition. -/
def Meets8 : Prop :=
  ∀ j, j < 2 * S.NP → (K5Law.endsH (oldOf S gL i) K j).value Reading.gl W =
    Reading.gl.val (if j % 2 = 0 then hbA (geoOf S) w i.p.x.scH.r (j / 2)
      else subE (hbA (geoOf S) w i.p.x.scH.r (j / 2)) oneE)

/-- The second half of claim 8. It is a definition. -/
def Under8 : Prop :=
  ∀ j, j < 2 * S.NP → W.slot (i.p.x.scH.ends + j) =
    Reading.gl.val (if j % 2 = 0 then hbA (geoOf S) w i.p.x.scH.r (j / 2)
      else subE (hbA (geoOf S) w i.p.x.scH.r (j / 2)) oneE)

variable {W S gL i K w}

/-- **Claim 8.** CONDITIONAL: the two halves; the row is worth 0. -/
theorem say8_of (M : Meets8 W S gL i K w) (U : Under8 W S i w)
    (hr : i.p.x.scH.row.value Reading.gl W = 0) : Say8 Reading.gl W (oldOf S gL i) K :=
  ⟨hr, fun j hj => (U j hj).trans (M j hj).symm⟩

end H2K5.Honest

#print axioms H2K5.Honest.planes_of
#print axioms H2K5.Honest.say3_of
#print axioms H2K5.Honest.unit_of
#print axioms H2K5.Honest.say5_of
#print axioms H2K5.Honest.say6_of
#print axioms H2K5.Honest.say7_of
#print axioms H2K5.Honest.say8_of
