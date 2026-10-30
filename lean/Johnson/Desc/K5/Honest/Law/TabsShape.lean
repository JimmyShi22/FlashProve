-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TabsShape.lean: CONDITIONAL: THE SHAPES OF THE TABLES THAT THE QUIET STEP
BEHIND AN ATTENTION SEGMENT's SENDING OF ITS READS MAKES (readsAtSO,
Johnson/Desc/First/Att/ReadsO.lean: by ptsFrom, Att/RunsK.lean, and tablesP, Att/TablesP.lean) ARE A
FUNCTION OF THE PLAN ALONE, WHERE A TEST ON LENGTHS SAYS YES. Over the library and the shapes of
Johnson/Desc/First/Shape/ alone: no prover's text is read. Definitions, and statements with their
proofs.

Why. A table's shape (FunSh, Shape/Tail.lean) is five numbers: its matrix, the rows to an entry, THE
NUMBER OF ITS WEIGHTS, the vector that holds it, its first entry. The library has four of them as
terms of the plan's shape (`tablesP_shapes`, `funs_laid`, Att/Door/Law/K5FunsSkel.lean). The tables'
maker asks no length of the weights where it lays a table; its other tests give "as many weights as
rows" at all reads but ten (`forced`, `fit_eq_ten`, Att/Claims/ReadsReturn.lean). Here the ten are
paid by one Bool on the shapes of what the segment's own rounds handed on and of what the lookup
returned.

Main names:
  `attFuns`   **the tables' shapes: a function of the plan alone**
  `lenM`, `lenD`, `lenB`, `tabsFitB`   **the test on lengths at the ten reads**
  `sumOfP_size`, `pointM_size`, `pointD_size`, `ti_of`, `phiB_size`   lengths
  `fitTen_of`, `of_mem_layFrom`, `funs_fit`   as many weights as rows to an entry, at every table
  `tabs_carries`   **the shapes of the tables that are made are attFuns A**
  `tabsFitB_bites`   two controls: the test can say no
  `planFitB`, `tabsFitB_at`   at the shape that the kind's own step lays the test reads the plan's
                              numbers and the
    lookup's lengths alone

EVERY STATEMENT ON THE MAKERS IS CONDITIONAL. `tabs_carries`: the two makers return at the plan's
numbers; the test on lengths says yes. `fitTen_of`: the function of the points returns; the test;
the lookup's test on its planes. `funs_fit`: the tables' maker returns; every read has as many
weights as cells.
Limits. ONE HALF: where the makers return. That they return (a Bool on the shape, and the maker's
two tests on values, mergedPlanes and mergedTokens) is not here: Law/TabsReturns.lean has it, where
that Bool and the two tests say yes. The test on lengths is sufficient, not necessary. NO THEOREM
HERE ENDS IN A YES; that a run's lookup hands on points of these lengths the library has as one Bool
on the state (k3OnOut, Johnson/Desc/First/Look/K3Borders.lean; see Law/TabsReturns.lean's Limits).
Shapes alone: nothing on
the weights themselves.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ShapeK5
import Johnson.Desc.First.Shape.Tail
import Johnson.Desc.First.Att.Door.Law.K5FunsSkel
import Johnson.Desc.First.Att.Claims.ReadsReturn
import Johnson.Desc.First.Att.Claims.PointsTie
import Johnson.Desc.First.Att.ReadsO
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo geoOf LookIn Pts TablesP Heard Left Fun1 Read)
open VerifiableInference.Desc.First.Shape (FunSh funSh HeardAll heardAll Heard5Sh heard5Sh)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf attShapes nScores)

/-! ## 1 The names -/

/-- **THE SHAPES OF THE TABLES OF AN ATTENTION SEGMENT: A FUNCTION OF THE PLAN ALONE**: of each
table its matrix, the rows to an entry and its first entry as the library's `attShapes` has them
(OnBytes/Tie/Pv/Tail/ShapesAtt.lean); as many weights as rows to an entry; vector number 2 (the
maker's own literal: `add`, Johnson/Desc/First/Att/TablesP.lean). -/
def attFuns (A : Attention.Plan) : List FunSh :=
  (attShapes A.S (nScores A.S)).map fun t =>
    { mat := t.mat, len := t.len, weights := t.len, tree := 2, start := t.start }

/-- The number of coordinates of the value product's point below the diagonal, of the number R of
its sumcheck's challenges. -/
def lenM (g : Geo) (R : Nat) : Nat :=
  min (g.lgk + 2 * g.lnT - 1) R + (min (g.lnT + g.lB) g.lt - g.lnT) + min g.lB R

/-- The like on the diagonal. -/
def lenD (g : Geo) (R : Nat) : Nat :=
  min (g.lgk + g.lnT) R + (min (g.lnT + g.lB) g.lt - g.lnT) + min g.lB R

/-- The number of coordinates under the lookup's weights on the planes' rows, of the number Z of
coordinates of its point. -/
def lenB (h : Forest.Shape) (lmb Z : Nat) : Nat :=
  (min h.kT Z - (h.kT + 5 - lmb)) + (Z - (h.kT + h.cK))

/-- **THE TEST ON LENGTHS AT THE TEN READS** at which the tables' maker asks no length of the
weights (`theTen`, Johnson/Desc/First/Att/Claims/ReadsReturn.lean): on the place's numbers g, the
shape H of what the segment's own rounds handed on and the shape K of what the lookup returned. The
tenth read's weights are made of the place's numbers alone: nothing is asked for it. -/
def tabsFitB (g : Geo) (H : Heard5Sh) (K : HeardAll) : Bool :=
  decide (g.lmS ≤ K.zx) && decide (g.lmS ≤ lenM g (H.below.r - 1)) &&
    decide (g.lmS ≤ lenD g (H.on.r - 1)) && (2 ^ g.lt == g.T) && decide (g.lgk + g.lt ≤ H.point) &&
    decide (2 * g.lt + g.lgk ≤ H.key.r - 1) && decide (g.lt ≤ H.cells.r - 1) &&
    (lenB K.shape g.lmb K.zb0 == g.lmb) && (lenB K.shape g.lmb K.zb1 == g.lmb)

/-! ## 2 Lengths -/

/-- A sumcheck's point has one coordinate fewer than there are challenges. -/
theorem sumOfP_size (x : MaskedSum.Heard) (row : Aff) :
    (P.sumOfP x row).r.size = x.r.length - 1 := by
  show (x.r.dropLast.toArray).size = _
  rw [List.size_toArray, List.length_dropLast]

theorem pointM_size (g : Geo) (d : P.DivP) (hW : d.ziW.size = g.lt) :
    (P.pointM g d).size = lenM g d.vpm.r.size := by
  unfold P.pointM P.DivP.zilo P.lastCoords lenM
  simp only [Array.size_append, Array.size_extract, hW]
  omega

theorem pointD_size (g : Geo) (d : P.DivP) (hW : d.ziW.size = g.lt) :
    (P.pointD g d).size = lenD g d.vpd.r.size := by
  unfold P.pointD P.DivP.zilo P.lastCoords lenD
  simp only [Array.size_append, Array.size_extract, hW]
  omega

/-- The drawn point's cut. -/
theorem ti_of {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : p.x.ti = h.point.extract g.lgk (g.lgk + g.lt) := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, hW, uX, hX, uH, hH, _, hs, _, hz, e⟩ := hp
  subst e
  rfl

/-- The lookup's weights on the planes' rows. -/
theorem phiB_size (gl : Forest.Heard) (lmb e : Nat)
    (hok : VerifiableInference.Desc.First.Look.planesOk gl.shape lmb = true) :
    ((VerifiableInference.Desc.First.Look.phiBOwn gl lmb e).getD #[]).size =
      2 ^ lenB gl.shape lmb (gl.zb e).size := by
  unfold VerifiableInference.Desc.First.Look.phiBOwn
  simp only [hok, if_true, Option.getD_some]
  rw [OnBytes.Road.eqTab_size]
  unfold lenB
  simp only [Array.size_append, Array.size_extract]
  congr 1
  omega

/-! ## 3 As many weights as rows -/

/-- **At the ten reads the weights are as many as the cells.** CONDITIONAL on: the function of the
points returns; the test on lengths says yes; the lookup's test on its planes says yes. -/
theorem fitTen_of {g : Geo} {gl : Forest.Heard} {h : Heard} {L : Left} {p : Pts}
    (hp : P.pointsOf g gl.zk h L = some p)
    (hG : tabsFitB g (heard5Sh h) (heardAll gl) = true)
    (hok : (P.lookOfO g.lmb gl).planesOk = true) :
    K5Law.fitTen g (P.lookOfO g.lmb gl) p = true := by
  have PA := K5Law.points_are hp
  obtain ⟨uW, uX, uH, _, _, _, sW, sX, _, _, _, eW, _, _, eX, _, _, _⟩ := (K5Law.cut5_of hp).at'
  have hW : p.d.ziW.size = g.lt := by
    rw [eW, Array.size_extract, sW]
    omega
  have hX : p.d.ziX.size = g.lt := by
    rw [eX, Array.size_extract, sX]
    omega
  simp only [tabsFitB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hG
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩ := hG
  have g1' : g.lmS ≤ gl.zx.size := g1
  have g2' : g.lmS ≤ lenM g (h.below.r.length - 1) := g2
  have g3' : g.lmS ≤ lenD g (h.on.r.length - 1) := g3
  have g5' : g.lgk + g.lt ≤ h.point.size := g5
  have g6' : 2 * g.lt + g.lgk ≤ h.key.r.length - 1 := g6
  have g7' : g.lt ≤ h.cells.r.length - 1 := g7
  have g8' : lenB gl.shape g.lmb gl.zb0.size = g.lmb := g8
  have g9' : lenB gl.shape g.lmb gl.zb1.size = g.lmb := g9
  have rM : p.d.vpm.r.size = h.below.r.length - 1 := by rw [PA.vpm, sumOfP_size]
  have rD : p.d.vpd.r.size = h.on.r.length - 1 := by rw [PA.vpd, sumOfP_size]
  have rK : p.x.scd.r.size = h.key.r.length - 1 := by rw [PA.scd, sumOfP_size]
  have rH : p.x.scH.r.size = h.cells.r.length - 1 := by rw [PA.scH, sumOfP_size]
  simp only [K5Law.fitTen, K5Law.theTen, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, beq_iff_eq, P.Read.of, P.Weights.array, P.Weights.len]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (P.eqTab (P.lastCoords gl.zx g.lmS)).size = _
    rw [K5Law.eqTab_size, K5Law.lastCoords_size _ _ g1']
  · show (P.eqTab (P.lastCoords (P.pointM g p.d) g.lmS)).size = _
    rw [K5Law.eqTab_size, K5Law.lastCoords_size _ _ (by rw [pointM_size g p.d hW, rM]; exact g2')]
  · show (P.eqTab (P.lastCoords (P.pointD g p.d) g.lmS)).size = _
    rw [K5Law.eqTab_size, K5Law.lastCoords_size _ _ (by rw [pointD_size g p.d hW, rD]; exact g3')]
  · rw [K5Law.eqTab_size, hX, g4]
  · rw [K5Law.eqTab_size, ti_of hp, Array.size_extract, ← g4]
    congr 1
    omega
  · rw [K5Law.eqTab_size, ← g4]
    unfold P.MaxP.pi
    rw [Array.size_extract, rK]
    congr 1
    omega
  · rw [K5Law.eqTab_size, ← g4]
    unfold P.MaxP.ri2
    rw [Array.size_extract, rH]
    congr 1
    omega
  · show ((VerifiableInference.Desc.First.Look.phiBOwn gl g.lmb 0).getD #[]).size = _
    rw [phiB_size gl g.lmb 0 hok]
    show 2 ^ lenB gl.shape g.lmb gl.zb0.size = _
    rw [g8']
  · show ((VerifiableInference.Desc.First.Look.phiBOwn gl g.lmb 1).getD #[]).size = _
    rw [phiB_size gl g.lmb 1 hok]
    show 2 ^ lenB gl.shape g.lmb gl.zb1.size = _
    rw [g9']
  · show (Forest.phiP g.lmb).size = _
    simp [Forest.phiP]

/-- What is laid from an entry on: vector number 2; weights and rows of a table of the list. -/
theorem of_mem_layFrom : ∀ (Ls : List K5Law.Table) (m : Nat) (f : Fun1), f ∈ K5Law.layFrom m Ls →
    f.tree = 2 ∧ ∃ T ∈ Ls, f.phi = T.phi ∧ f.len = T.len
  | [], _, _, h => by cases h
  | T :: Ls, m, f, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨rfl, T, List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨a, T', hT, b⟩ := of_mem_layFrom Ls _ f h'
      exact ⟨a, T', List.mem_cons_of_mem _ hT, b⟩

/-- **Every table that the maker lays lies in vector number 2 and has as many weights as rows to an
entry.** CONDITIONAL on: the maker returns; every read has as many weights as cells (`fit`,
Johnson/Desc/First/Att/ReadsOf.lean). -/
theorem funs_fit {g : Geo} {mats : Array (Nat × Nat)} {nW : Nat} {lk : LookIn} {p : Pts}
    {t : TablesP} (ht : P.tablesP g mats nW lk p = some t) (hfit : P.fit g lk p = true) :
    ∀ f ∈ t.funs.toList, f.tree = 2 ∧ f.phi.size = f.len := by
  intro f hf
  rw [H2K5.Door.funs_laid ht] at hf
  obtain ⟨a, T, hT, e1, e2⟩ := of_mem_layFrom _ _ f hf
  refine ⟨a, ?_⟩
  rw [K5Law.laidBy_eq] at hT
  obtain ⟨r, hr, hTr⟩ := List.mem_flatMap.1 hT
  unfold K5Law.tabs at hTr
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hTr
  rw [e1, e2]
  exact beq_iff_eq.1 (List.all_eq_true.1 hfit r hr)

/-! ## 4 Carries -/

/-- **CARRIES: THE SHAPES OF THE TABLES THAT ARE MADE ARE attFuns A.** CONDITIONAL on: the two
makers return (the function of the points, behind the function of the forms that are left; the
tables' maker) at the plan's numbers; the test on lengths says yes at the shapes of what was heard
and of what the lookup returned. -/
theorem tabs_carries (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork} {p : Pts}
    {t : TablesP} (hp : P.ptsFrom (P.parCOf A).geo gl.zk h F = some p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb gl) p = some t)
    (hG : tabsFitB (P.parCOf A).geo (heard5Sh h) (heardAll gl) = true) :
    (tabsBack t).funs.toList.map funSh = attFuns A := by
  obtain ⟨L, _, hP⟩ := Option.bind_eq_some_iff.1 hp
  have hP' : P.pointsOf (geoOf A.S) gl.zk h L = some p := hP
  have hok : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb gl) p = true := by
    rw [← K5Law.tablesP_isSome, ht]
    rfl
  have hpl : (P.lookOfO (P.parCOf A).geo.lmb gl).planesOk = true := by
    unfold K5Law.placeOk at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.2
  have hfit : P.fit (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb gl) p = true := by
    rw [K5Law.fit_eq_ten hok]
    exact fitTen_of hP hG hpl
  have hall := funs_fit ht hfit
  have hsh := H2K5.Door.tablesP_shapes hP' ht
  unfold attFuns
  rw [← hsh]
  unfold shapesOf
  rw [List.map_map]
  refine List.map_congr_left fun Fn hFn => ?_
  have hFn' : Fn ∈ (t.funs.map funBack).toList := hFn
  rw [Array.toList_map] at hFn'
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hFn'
  obtain ⟨a, b⟩ := hall f hf
  show FunSh.mk f.mat f.len f.phi.size f.tree f.start = FunSh.mk f.mat f.len f.len 2 f.start
  rw [a, b]

/-- Two controls: the test on lengths says no where the lookup's point is too short, and where the
number of positions is not the power of two. -/
theorem tabsFitB_bites (g : Geo) (H : Heard5Sh) (K : HeardAll) :
    (K.zx < g.lmS → tabsFitB g H K = false) ∧ (2 ^ g.lt ≠ g.T → tabsFitB g H K = false) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e : decide (g.lmS ≤ K.zx) = false := decide_eq_false (by omega)
    simp [tabsFitB, e]
  · have e : (2 ^ g.lt == g.T) = false := by simpa using h
    simp [tabsFitB, e]

/-! ## 5 At the shape that the segment's own rounds lay -/

/-- **The test on lengths as a test on the plan's numbers and the lookup's lengths**: g: the place's
numbers; x: the plan's numbers of the segment's own rounds; K: the shape of what the lookup
returned. -/
def planFitB (g : Geo) (x : Params.AttentionRounds) (K : HeardAll) : Bool :=
  decide (g.lmS ≤ K.zx) && decide (g.lmS ≤ lenM g x.valueM) && decide (g.lmS ≤ lenD g x.valueD) &&
    (2 ^ g.lt == g.T) && decide (g.lgk + g.lt ≤ 2 * x.lgk + 2 * x.lt + 4) &&
    decide (2 * g.lt + g.lgk ≤ x.lt + x.lgk + x.lt) && decide (g.lt ≤ x.bits) &&
    (lenB K.shape g.lmb K.zb0 == g.lmb) && (lenB K.shape g.lmb K.zb1 == g.lmb)

/-- **At the shape that the kind's own step lays** (`heard5At`,
Johnson/Desc/K5/Honest/Law/ShapeK5.lean) the test on lengths is that test: it reads no slot's
number. On nothing. -/
theorem tabsFitB_at (g : Geo) (x : Params.AttentionRounds) (n : Nat) (K : HeardAll) :
    tabsFitB g (heard5At x n) K = planFitB g x K := by
  have b1 : (heard5At x n).below.r - 1 = x.valueM := by
    show (List.replicate x.valueM (MaskedSum.Var.plain 4)).length + 1 - 1 = _
    rw [List.length_replicate, Nat.add_sub_cancel]
  have b2 : (heard5At x n).on.r - 1 = x.valueD := by
    show (List.replicate x.valueD (MaskedSum.Var.plain 4)).length + 1 - 1 = _
    rw [List.length_replicate, Nat.add_sub_cancel]
  have b3 : (heard5At x n).point = 2 * x.lgk + 2 * x.lt + 4 := rfl
  have b4 : (heard5At x n).key.r - 1 = x.lt + x.lgk + x.lt := by
    show ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++
      List.replicate x.lt (x.lt + 2)).map MaskedSum.Var.plain).length + 1 - 1 = _
    simp only [List.length_map, List.length_append, List.length_replicate, Nat.add_sub_cancel]
  have b5 : (heard5At x n).cells.r - 1 = x.bits := by
    show (List.replicate x.bits (MaskedSum.Var.plain 4)).length + 1 - 1 = _
    rw [List.length_replicate, Nat.add_sub_cancel]
  unfold tabsFitB planFitB
  rw [b1, b2, b3, b4, b5]

end H2K5.Honest

#print axioms H2K5.Honest.sumOfP_size
#print axioms H2K5.Honest.pointM_size
#print axioms H2K5.Honest.pointD_size
#print axioms H2K5.Honest.ti_of
#print axioms H2K5.Honest.phiB_size
#print axioms H2K5.Honest.fitTen_of
#print axioms H2K5.Honest.of_mem_layFrom
#print axioms H2K5.Honest.funs_fit
#print axioms H2K5.Honest.tabs_carries
#print axioms H2K5.Honest.tabsFitB_bites
#print axioms H2K5.Honest.tabsFitB_at
