-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/MeetsOf.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE FIRST HALVES OF WHAT THE CLAIMS SAY (`MeetsPlanes`, `MeetsUnit`, `Meets5`,
`MeetsV`, `Meets7`, `Meets8`, Johnson/Desc/K5/Honest/Law/SayOf.lean: "the written form is worth the
slot less the prover's value, read", "the reader's form is worth the prover's value, read"), AT THE
VERIFIER's OWN NAMED POINTS AND TABLES, from the tree's own bundles of public premises. A definition
of a premise, and statements with their proofs. No algebra is in this file: it lays
Law/AloneMeets.lean, Law/EndsMeet.lean and Law/EndsMeetIndex.lean at the verifier's values.

Main names:
  `PtsFit`           what is asked of the named points, tables aside: lengths, pieces, three
                     equations
  `getD_of_mem`, `back_of_mem`   a member of a list of pieces has a number
  `meetsPlanes_of`, `meetsUnit_of`, `meets5_of`, `meetsV_of`, `meets7_of`, `meets8_of`

EVERY STATEMENT ON A HALF IS CONDITIONAL. The premises, and who is meant to show each:
  `AttAt` (Johnson/Road/Rows/AttRead.lean), at the claims' values made of the kind's own: the shape
          is the planner's, the matrices fit, and EVERY TABLE OF THE LIST IS TRUE OF THE MATRICES IN
          THE WORLD: whoever lays the world.
  `CellsAre` (Law/AloneMeets.lean): whoever lays the matrices of the prover's input.
  `TabsAt` (Johnson/Desc/First/Att/Claims/TablesAt.lean): every named table lies in the list with
           its
    weights: the tree has it from the return of the verifier's function for the tables (`tabs_at`).
  `InTail`, `InUnit` (Claims/EndsAll.lean), `PlaneIn`, `MaxIn`, `DenIn`, `HighIn`, `BitIn`
    (Claims/KeysIn.lean): the indices read lie in the tables: the tree has them from the returns of
    the runs "first" and "second" (Claims/InRunAll.lean, Claims/KeysIn.lean).
  `PtsFit`: lengths, pieces and three equations of words; its docstring lists the clauses by their
    sources. One clause hangs on the lengths of the lookup's key points. Not shown here.
Limits. `AttAt` IS THE PREMISE THROUGH WHICH THE COMMITTED ARRAY ENTERS: that the world's entries
are true tables of the matrices. Johnson/Desc/K5/Honest/Law/Planes.lean (`attAt_stated`) has it from
a named premise on the world; it is not called here. Nothing here says that a premise holds at any
place. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.SayOf
import Johnson.Desc.First.Att.Claims.TablesAt
import Johnson.Desc.First.Att.Claims.KeysIn
import Johnson.Desc.First.Att.Claims.EndsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP ScoreT DivP MaxP Pts geoOf)
open K5Law (oldOf pwBack remBack scoreBack tbBack divBack maxBack InLong InLongG TabsAt InTail
  InUnit PlaneIn MaxIn DenIn HighIn BitIn)

/-! ## The premise on lengths and pieces -/

/-- **What the meetings ask of the verifier's named points, tables aside.** zx: the lookup's point.
The clauses by their sources, none of which is spent here:
the tests of the verifier's function of the points: gW, iW, cW, gX, iX, gH, nW, unitG, planeN, and
planeZ at a softmax-table unit's plane claim; its own line: wJv;
THE KEY POINTS' LENGTHS, which are the lookup's: planeZ at a remainder-table unit's plane claim:
that function tests nothing of that point's length;
the two tests on values of the verifier's function for the tables: planeL, iH, cH;
the numbers of challenges and drawn elements that were heard, with the planner's numbers: unitR, rE,
rM, rD, rF, rK, rH, tg, ti, and with these ptM, ptD;
"piece b is pair b" and the lists' lengths: planeP, unitP, pW, pX, pH. -/
structure PtsFit (S : Attention.Shape) (zx : Array E) (p : Pts) : Prop where
  planeZ : ∀ u ∈ p.planes.toList, u.z.size = if u.isD = true then S.nD else S.nM
  planeN : ∀ u ∈ p.planes.toList, u.np ≤ 5
  planeP : ∀ u ∈ p.planes.toList, PiecesFit S u.pw
  planeL : ∀ u ∈ p.planes.toList, lastCoords u.z S.cf.lmS = lastCoords zx S.cf.lmS
  unitG : ∀ k ∈ p.scores.toList, k.zg.size = S.cf.lgk
  unitR : ∀ k ∈ p.scores.toList, S.cf.lgk + S.cf.ldh ≤ k.sc.r.size
  unitP : ∀ k ∈ p.scores.toList, PiecesFit S k.pw
  gW : p.d.zgW.size = S.cf.lgk
  iW : p.d.ziW.size = S.cf.lt
  cW : p.d.zcW.size = S.cf.ldh
  gX : p.d.zgX.size = S.cf.lgk
  iX : p.d.ziX.size = S.cf.lt
  gH : p.d.zgH.size = S.cf.lgk
  iH : p.d.ziH = p.d.ziW
  cH : p.d.zcH = p.d.zcW
  pW : PiecesFit S p.d.pwW
  pX : PiecesFit S p.d.pwX
  pH : PiecesFit S p.d.pwH
  nW : p.d.pwW.size = S.NP
  rE : S.cf.lgk + S.cf.lt ≤ p.d.scE.r.size
  rM : S.cf.lgk ≤ p.d.vpm.r.size
  rD : S.cf.lgk ≤ p.d.vpd.r.size
  ptM : (P.pointM (geoOf S) p.d).size = S.nM
  ptD : (P.pointD (geoOf S) p.d).size = S.nD
  wJv : p.d.wJv = (belowAt (geoOf S) p.d p.d.vpm.r).wJv
  tg : p.x.tg.size = S.cf.lgk
  ti : p.x.ti.size = S.cf.lt
  rF : p.x.scF.r.size = S.nvF
  rK : p.x.scd.r.size = 2 * S.cf.lt + S.cf.lgk
  rH : p.x.scH.r.size = S.nvH

/-! ## Pieces: a member, by its number -/

/-- A member of a list of pieces has a number. -/
theorem getD_of_mem {pw : Array W1} {p : W1} (hp : p ∈ pw.toList) :
    ∃ b, b < pw.size ∧ pw.getD b ⟨0, 0, zeroE⟩ = p := by
  obtain ⟨b, hb, e⟩ := List.mem_iff_getElem.1 hp
  rw [Array.length_toList] at hb
  refine ⟨b, hb, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb]
  rw [Array.getElem_toList] at e
  exact e

/-- The same in the type of pieces of the written claims. -/
theorem back_of_mem {pw : Array W1} {p : W1} (hp : p ∈ pw.toList) :
    ∃ b, b < (pwBack pw).size ∧ ((pwBack pw).getD b default).lam = p.lam ∧
      ((pwBack pw).getD b default).a = p.a ∧
      (pwBack pw)[b]? = some ((pwBack pw).getD b default) := by
  obtain ⟨b, hb, e⟩ := getD_of_mem hp
  have hb' : b < (pwBack pw).size := by
    unfold K5Law.pwBack
    rw [Array.size_map]
    exact hb
  refine ⟨b, hb', ?_, ?_, ?_⟩
  · rw [pwBack_getD pw hb, e]
  · rw [pwBack_getD pw hb, e]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb']
    rfl

/-! ## The first halves -/

variable {W : World GE} {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ}
  {w : K5In} {tl : HTailF2} {M : Mats GE} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {zx : Array E}

/-- **The plane claims.** CONDITIONAL on what the head lists. -/
theorem meetsPlanes_of (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs)
    (hc : CellsAre Reading.gl S M w) (T : TabsAt tl (oldOf S gL i) zx) (F : PtsFit S zx i.p)
    (I : ∀ u ∈ i.p.planes.toList, PlaneIn (oldOf S gL i) (remBack u)) :
    MeetsPlanes W S gL i K w := by
  intro u hu y hy
  have Tb : AsAt (oldOf S gL i) (oldOf S gL i).t.tA (lastN u.z S.cf.lmS) := by
    have e : lastN u.z S.cf.lmS = lastN zx S.cf.lmS := by
      unfold lastN
      rw [F.planeL u hu]
    rw [e]
    exact T.tA
  have hy5 : y < 5 := Nat.lt_of_lt_of_le hy (F.planeN u hu)
  have hz := F.planeZ u hu
  cases hD : u.isD with
  | false =>
    rw [hD, if_neg (by decide)] at hz
    refine plane_meets_below A w hc hD Tb hz (F.planeP u hu) hy5 fun p hp hi hhi => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := I u hu y hy b hb hi (by
      show hi < (eqTab (u.z.extract 0 ((if u.isD = true then S.nD else S.nM) - S.cf.lmS))).size
      rw [hD]
      exact hhi)
    have h2 : Rows.planeFirst S y ((pwBack u.pw).getD b default).lam
        ((pwBack u.pw).getD b default).a u.isD >>> S.cf.lmS + hi <
        ((oldOf S gL i).t.tabLen.lookup (oldOf S gL i).t.tA).getD 0 := h1
    rw [e1, e2, hD] at h2
    exact h2
  | true =>
    rw [hD, if_pos rfl] at hz
    refine plane_meets_on A w hc hD Tb hz (F.planeP u hu) hy5 fun p hp hi hhi => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := I u hu y hy b hb hi (by
      show hi < (eqTab (u.z.extract 0 ((if u.isD = true then S.nD else S.nM) - S.cf.lmS))).size
      rw [hD]
      exact hhi)
    have h2 : Rows.planeFirst S y ((pwBack u.pw).getD b default).lam
        ((pwBack u.pw).getD b default).a u.isD >>> S.cf.lmS + hi <
        ((oldOf S gL i).t.tabLen.lookup (oldOf S gL i).t.tA).getD 0 := h1
    rw [e1, e2, hD] at h2
    exact h2

/-- **A softmax-table unit** k with the tables tb. Tk: the unit's three tables lie in the list, in
the words of the tree's `TabsAt`. CONDITIONAL on what the head lists. -/
theorem meetsUnit_of (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs)
    (hc : CellsAre Reading.gl S M w) (F : PtsFit S zx i.p) {k : ScoreP} {tb : ScoreT}
    (hk : k ∈ i.p.scores.toList)
    (Tk : AhAt tl (oldOf S gL i) tb.tM (tok S k.wI k.zi) ∧
      TabAt tl (oldOf S gL i) tb.tQ (S.cf.NAs + 3) (2 ^ S.cf.la)
        (blockRows (lowOf S (lastCoords k.sc.r S.cf.ldh))
          (tok S (scoreTiles S (scoreBack k)).1 k.zi)) ∧
      TabAt tl (oldOf S gL i) tb.tK (S.cf.NAs + 3) (2 ^ S.cf.la)
        (blockRows (lowOf S (lastCoords k.sc.r S.cf.ldh))
          (tok S (scoreTiles S (scoreBack k)).2 k.zj)))
    (IM : MaxIn (oldOf S gL i) (scoreBack k) tb.tM)
    (IU : InUnit (oldOf S gL i) (scoreBack k) (tbBack tb)) : MeetsUnit W S gL i K w k tb := by
  have hG : S.G = 2 ^ S.cf.lgk := (shapedG_of_hid A.shape).G
  obtain ⟨T1, T2, T3⟩ := Tk
  rw [K5Law.scoreTiles_back] at T2 T3
  refine ⟨mv_meets A w hc T1 (F.unitG k hk) (F.unitP k hk) fun p hp g hg l hl => ?_,
    fun j hj => endsU_meets A w hc (tb := tbBack tb) (F.unitR k hk) T2 T3 (F.unitP k hk)
      (fun p hp => ?_) (fun p hp => ?_) hj⟩
  · obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := IM b hb g (lt_of_lt_of_eq hg hG.symm) l hl
    have h2 : S.oMr + (l * S.Lam + ((pwBack k.pw).getD b default).lam) * S.cf.H +
        (g * S.HA + ((pwBack k.pw).getD b default).a) <
        ((oldOf S gL i).t.tabLen.lookup tb.tM).getD 0 := h1
    rw [e1, e2] at h2
    exact h2
  · obtain ⟨b, _, e1, e2, e3⟩ := back_of_mem hp
    have h1 := IU.tQ b _ e3
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨b, _, e1, _, e3⟩ := back_of_mem hp
    have h1 := IU.tK b _ e3
    rw [e1] at h1
    exact h1

/-- **Claim 5: the division.** I5: what the tree draws from the return of the run "first" at claim
5. CONDITIONAL on what the head lists. -/
theorem meets5_of (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs)
    (hc : CellsAre Reading.gl S M w) (T : TabsAt tl (oldOf S gL i) zx) (F : PtsFit S zx i.p)
    (I5 : DenIn (oldOf S gL i) ∧
      HighIn (oldOf S gL i) (oldOf S gL i).d.pwW (oldOf S gL i).d.zcW ∧
      HighIn (oldOf S gL i) (oldOf S gL i).d.pwH (oldOf S gL i).d.zcH ∧ BitIn (oldOf S gL i))
    (IT : InTail (oldOf S gL i)) : Meets5 W S gL i K w := by
  have hG : S.G = 2 ^ S.cf.lgk := (shapedG_of_hid A.shape).G
  obtain ⟨ID, IW, IH, IB⟩ := I5
  have TO : TabAt tl (oldOf S gL i) i.t.tO (S.cf.NAs + 1) (2 ^ S.cf.la)
      (blockRows (lowOf S i.p.d.zcW) (eqTab i.p.d.ziW)) := T.tO
  have TH : TabAt tl (oldOf S gL i) i.t.tO (S.cf.NAs + 1) (2 ^ S.cf.la)
      (blockRows (lowOf S i.p.d.zcH) (eqTab i.p.d.ziH)) := by
    rw [F.iH, F.cH]
    exact TO
  have iH : i.p.d.ziH.size = S.cf.lt := by rw [F.iH]; exact F.iW
  have cH : i.p.d.zcH.size = S.cf.ldh := by rw [F.cH]; exact F.cW
  refine ⟨?_, ?_, ?_, fun k hk => ?_, ?_, ?_, fun j hj => ?_⟩
  · refine zc_meets A w hc (T.hW : TabAt _ _ _ _ _ _) F.gW F.iW F.pW fun p hp g hg l hl => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := ID b hb g (lt_of_lt_of_eq hg hG.symm) l hl
    have h2 : S.oZr + (l * S.Lam + ((pwBack i.p.d.pwW).getD b default).lam) * S.cf.H +
        (g * S.HA + ((pwBack i.p.d.pwW).getD b default).a) <
        ((oldOf S gL i).t.tabLen.lookup i.t.hW).getD 0 := h1
    rw [e1, e2] at h2
    exact h2
  · refine rh_meets A w hc TO F.gW F.iW F.cW F.pW fun p hp => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := (IW.1 b hb).long hG
    have h2 : InLong (oldOf S gL i) i.t.tO (atRh S) ((pwBack i.p.d.pwW).getD b default).lam
        (fun g => g * S.HA + ((pwBack i.p.d.pwW).getD b default).a) i.p.d.zcW := h1
    rw [e1, e2] at h2
    exact h2
  · refine rhp_meets A w hc TO F.gW F.iW F.cW F.pW fun p hp => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := (IW.2 b hb).long hG
    have h2 : InLong (oldOf S gL i) i.t.tO (atRhp S) ((pwBack i.p.d.pwW).getD b default).lam
        (fun g => g * S.HA + ((pwBack i.p.d.pwW).getD b default).a) i.p.d.zcW := h1
    rw [e1, e2] at h2
    exact h2
  · refine ib_meets A w hc hk (T.hX : TabAt _ _ _ _ _ _) F.gX F.iX F.pX fun p hp g hg l hl => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := IB k hk b hb g (lt_of_lt_of_eq hg hG.symm) l hl
    have h2 : S.oIb + (l * S.Lam + ((pwBack i.p.d.pwX).getD b default).lam) *
        (S.cf.lt * S.cf.H) + (k * S.cf.H + g * S.HA + ((pwBack i.p.d.pwX).getD b default).a) <
        ((oldOf S gL i).t.tabLen.lookup i.t.hX).getD 0 := h1
    rw [e1, e2] at h2
    exact h2
  · refine rh_meets A w hc TH F.gH iH cH F.pH fun p hp => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := (IH.1 b hb).long hG
    have h2 : InLong (oldOf S gL i) i.t.tO (atRh S) ((pwBack i.p.d.pwH).getD b default).lam
        (fun g => g * S.HA + ((pwBack i.p.d.pwH).getD b default).a) i.p.d.zcH := h1
    rw [e1, e2] at h2
    exact h2
  · refine rhp_meets A w hc TH F.gH iH cH F.pH fun p hp => ?_
    obtain ⟨b, hb, e1, e2, _⟩ := back_of_mem hp
    have h1 := (IH.2 b hb).long hG
    have h2 : InLong (oldOf S gL i) i.t.tO (atRhp S) ((pwBack i.p.d.pwH).getD b default).lam
        (fun g => g * S.HA + ((pwBack i.p.d.pwH).getD b default).a) i.p.d.zcH := h1
    rw [e1, e2] at h2
    exact h2
  · refine endsE_meets A w hc rfl F.rE F.cW T.hE T.qO F.pW F.nW (fun p hp => ?_) (fun p hp => ?_) hj
    · obtain ⟨b, hb, e1, e2, e3⟩ := back_of_mem hp
      have hb' : b < S.NP := by
        have e : (pwBack i.p.d.pwW).size = i.p.d.pwW.size := Array.size_map ..
        rw [e, F.nW] at hb
        exact hb
      have h1 := IT.hE b hb' _ e3
      rw [e1, e2] at h1
      exact h1
    · obtain ⟨b, hb, e1, e2, e3⟩ := back_of_mem hp
      have hb' : b < S.NP := by
        have e : (pwBack i.p.d.pwW).size = i.p.d.pwW.size := Array.size_map ..
        rw [e, F.nW] at hb
        exact hb
      have h1 := IT.qO b hb' _ e3
      rw [e1, e2] at h1
      exact h1

/-- **Claim 6: the end values of the value product's two sumchecks.** CONDITIONAL on what the head
lists. -/
theorem meetsV_of (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs)
    (hc : CellsAre Reading.gl S M w) (T : TabsAt tl (oldOf S gL i) zx) (F : PtsFit S zx i.p)
    (IT : InTail (oldOf S gL i)) : MeetsV W S gL i K w := by
  have nb : ∀ {p : W1}, p ∈ i.p.d.pwW.toList → ∃ b, b < S.NP ∧
      ((pwBack i.p.d.pwW).getD b default).lam = p.lam ∧
      ((pwBack i.p.d.pwW).getD b default).a = p.a ∧
      (pwBack i.p.d.pwW)[b]? = some ((pwBack i.p.d.pwW).getD b default) := fun hp => by
    obtain ⟨b, hb, e1, e2, e3⟩ := back_of_mem hp
    have e : (pwBack i.p.d.pwW).size = i.p.d.pwW.size := Array.size_map ..
    rw [e, F.nW] at hb
    exact ⟨b, hb, e1, e2, e3⟩
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · refine endsV_below_meets A w hc rfl T.ptM F.ptM F.wJv F.rM F.cW T.tVM T.qVM F.pW F.nW
      (fun p hp => ?_) (fun p hp => ?_) hj
    · obtain ⟨b, hb, e1, e2, e3⟩ := nb hp
      have h1 := IT.tVM b hb _ e3
      rw [e1, e2] at h1
      exact h1
    · obtain ⟨b, hb, e1, _, e3⟩ := nb hp
      have h1 := IT.qVM b hb _ e3
      rw [e1] at h1
      exact h1
  · refine endsV_on_meets A w hc rfl T.ptD F.ptD F.rD F.cW T.tVD T.qVD F.pW F.nW
      (fun p hp => ?_) (fun p hp => ?_) hj
    · obtain ⟨b, hb, e1, e2, e3⟩ := nb hp
      have h1 := IT.tVD b hb _ e3
      rw [e1, e2] at h1
      exact h1
    · obtain ⟨b, hb, e1, _, e3⟩ := nb hp
      have h1 := IT.qVD b hb _ e3
      rw [e1] at h1
      exact h1

/-- **Claim 7: the maximum and its index.** CONDITIONAL on what the head lists. -/
theorem meets7_of (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs)
    (hc : CellsAre Reading.gl S M w) (T : TabsAt tl (oldOf S gL i) zx) (F : PtsFit S zx i.p)
    (IT : InTail (oldOf S gL i)) : Meets7 W S gL i K w := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun l hl => ?_, fun b k hb hk => ?_⟩
  · exact m6_meets A w hc hb (T.hT : TabAt _ _ _ _ _ _) F.tg F.ti (IT.hT b hb)
  · exact endsF_meets A w hc rfl F.rF hb T.qF (IT.qF b hb)
  · exact endsK_lam_meets A w hc rfl F.rF F.rK hl T.qKx (IT.qKx l hl)
  · exact endsK_bit_meets A w hc rfl F.rK hb hk T.hPi (IT.hPi b hb k hk)

/-- **Claim 8: the index's cells are bits.** CONDITIONAL on what the head lists. -/
theorem meets8_of (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs)
    (hc : CellsAre Reading.gl S M w) (T : TabsAt tl (oldOf S gL i) zx) (F : PtsFit S zx i.p)
    (IT : InTail (oldOf S gL i)) : Meets8 W S gL i K w := by
  intro j hj
  exact endsH_meets A w hc rfl F.rH hj T.hR2 (IT.hR2 (j / 2) (show j / 2 < S.NP by omega))

end H2K5.Honest

#print axioms H2K5.Honest.getD_of_mem
#print axioms H2K5.Honest.back_of_mem
#print axioms H2K5.Honest.meetsPlanes_of
#print axioms H2K5.Honest.meetsUnit_of
#print axioms H2K5.Honest.meets5_of
#print axioms H2K5.Honest.meetsV_of
#print axioms H2K5.Honest.meets7_of
#print axioms H2K5.Honest.meets8_of
