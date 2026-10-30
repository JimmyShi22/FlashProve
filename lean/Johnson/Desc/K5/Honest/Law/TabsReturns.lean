-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TabsReturns.lean: CONDITIONAL: THE TABLES OF THE QUIET STEP BEHIND AN
ATTENTION SEGMENT's SENDING OF ITS READS ARE MADE WHERE ONE BOOL ON THE SHAPE AND TWO TESTS ON
VALUES SAY YES, AND THEN THEIR SHAPES ARE A FUNCTION OF THE PLAN ALONE. The second half beside
Johnson/Desc/K5/Honest/Law/TabsShape.lean. Over the library and the shapes of
Johnson/Desc/First/Shape/ alone: no prover's text is read. Definitions, and statements with their
proofs.

Why. The step (readsAtSO, Johnson/Desc/First/Att/ReadsO.lean) makes its tables by two makers in a
row: ptsFrom (Att/RunsK.lean) and tablesP (Att/TablesP.lean). The first compares no value: it asks
numbers, lengths, and that slots of the ledger are filled. The second returns just where the
library's placeOk says yes (Att/Claims/ReadsReturn.lean): two tests on values, and tests on the
plan's numbers and on lengths.

Main names:
  `filledB`, `innerLen`, `unitLen`, `ptsB`   the test under which the first maker returns
  `longB`, `placeB`   the second maker's tests that read no value
  `tabsG`   **THE ONE BOOL ON THE SHAPE**: the two, and the test on lengths of Law/TabsShape.lean
  `valsT`   **THE TWO TESTS ON VALUES**
  `tabsOf`   the two makers in a row, of the state's own parts
  `filled_of_B`, `innerLen_is`, `zk_size`, `forall₂_of_each`, `fellow_of_forall₂`   tools
  `pts_returns`, `longs_of`, `tabs_returns`   **returns**
  `tabs_shape`   **both halves in one equation: the shapes of the tables that are made are some
    (attFuns A)**
  `tabs_carries_G`   carries, at the one Bool

EVERY STATEMENT ON THE MAKERS IS CONDITIONAL. `pts_returns`: the first test's yes. `tabs_returns`,
`tabs_shape`: the one Bool's yes at the shapes of what was heard, of what the lookup returned and of
the ledger; the two tests on values. `tabs_carries_G`: the tables are made; the one Bool's yes.
By `points_ret` (Att/K05PointsRet.lean), `left_ret`, `leftKey_ret` (Att/K05LeftRet.lean),
`scoreW_ret` (Att/K05ReturnsLeft.lean), `weights_size`, `pieces_size` (Att/K05Row.lean),
`leftP_of_is` (Att/Claims/LeftIsBack.lean), `tablesP_some`, `longs_eq`
(Att/Claims/ReadsReturn.lean), `asks_laid`, `units_plan` (Att/Door/Law/K5FunsSkel.lean),
`points_are` (Att/Claims/PointsRows.lean), `cut5_of` (Att/Claims/PointsTie.lean).
Limits. THE BOOL IS SUFFICIENT, NOT NECESSARY. It is stricter than the two makers' texts in three
places: ptsB asks that the ledger's arrays have their size (sizedB); filledB asks first + n ≤ the
number of marks; and tabsFitB: of its nine tests the makers' texts ask one (2 ^ lt = T, which longB
has too); the other eight they do not ask, by a reading of these texts; two of the eight are seen by
evaluation (Law/TabsReturnsToy.lean: with a point on the planes one coordinate short or long the
tables are still made, with other shapes). The key points' own lengths are not pinned by it (there:
key points without their first coordinate: all four say yes). NO STATEMENT OF THIS FILE ENDS IN THE
BOOL's YES: that the Bool and the two tests on values say yes together, at what the verifier's own
hearing hands on at a plan that the planner makes, is an evaluation (Law/TabsReturnsToy.lean), no
proof; what the lookup returned is laid by hand there. That a run's lookup hands on points of these
lengths the library has as one Bool on the state (k3OnOut, Johnson/Desc/First/Look/K3Borders.lean),
given from the promise in front and a yes of the lookup's block (k3_calls_lookOut,
First/Look/K3CallsLookOut.lean) and kept over the attention link's own lay (lookOut_behind,
First/Att/K05BehindLay.lean); the tie from it to this Bool: `tabsG_at_plan`, Law/TabsLook.lean. Each
under its own premises; who gives the promise in front, and the tie's second Bool (lookAttB), at a
state of a run is not said here. The two tests on values are read at the first maker's own points:
where it refuses they say no. The makers alone: the step's other tests (the list is open; the guard
of order) are not here. Shapes alone: nothing on the weights themselves.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.TabsShape
import Johnson.Desc.First.Att.K05PointsRet
import Johnson.Desc.First.Att.K05ReturnsLeft
import Johnson.Desc.First.Att.K05Row
import Johnson.Desc.First.Att.Claims.LeftIsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo geoOf UnitG LookIn Pts TablesP Heard Left)
open VerifiableInference.Desc.First.Shape (FunSh funSh HeardAll heardAll Heard5Sh heard5Sh SumSh
  sumSh LedSh ledSh sizedB sized_of_B)
open OnBytes.Tie.Pv.Tail.Closed (attAsks nScores)

/-! ## 1 The names -/

/-- The n slots from first on are there and filled. -/
def filledB (L : LedSh) (first n : Nat) : Bool :=
  decide (first + n ≤ L.got.length) && ((L.got.drop first).take n).all id

/-- The number of coordinates of a unit's inner point, of the number z of coordinates of its call's
key point. -/
def innerLen (u : UnitG) (z : Nat) : Nat := z - (z - u.bits)

/-- The number that the functions of the forms and of the points ask of a softmax-table unit's inner
point. -/
def unitLen (g : Geo) (u : UnitG) : Nat :=
  (if u.below then g.lgk + (g.lnT - 1) + g.lnT else g.lgk + g.lnT) + 2 * g.lB

/-- **THE TEST UNDER WHICH THE FUNCTION OF THE POINTS RETURNS** (ptsFrom,
Johnson/Desc/First/Att/RunsK.lean): on the place's numbers g, the key points' lengths zk, the shape
H of what the segment's own rounds handed on and the ledger's shape L: numbers of units and
messages; lengths of inner points; numbers of pieces; the end values' slots are filled. -/
def ptsB (g : Geo) (zk : List Nat) (H : Heard5Sh) (L : LedSh) : Bool :=
  sizedB L && ((g.units .kr [.rm, .rd]).length == H.remainders.length) &&
    (g.scores.length == H.scores.length) &&
    (g.scores.all fun u => innerLen u (zk.getD u.call 0) == unitLen g u) &&
    ((g.scores.zip H.scores).all fun x => filledB L x.2.2.sEnd (2 * x.1.pcs.length)) &&
    (match g.single .wl, g.single .ix, g.single .wh with
     | some uW, some uX, some uH =>
       (uW.pcs.length == g.NP) && (uX.pcs.length == g.NP) && (uH.pcs.length == g.NP) &&
         (innerLen uW (zk.getD uW.call 0) == 1 + g.lgk + g.lt + g.ldh) &&
         (innerLen uX (zk.getD uX.call 0) == g.lgk + g.lt) &&
         (innerLen uH (zk.getD uH.call 0) == g.lgk + g.lt + g.ldh)
     | _, _, _ => false) &&
    filledB L H.division.sEnd (2 * g.NP) && filledB L H.below.sEnd (2 * g.NP) &&
    filledB L H.on.sEnd (2 * g.NP) && filledB L H.atIndex.sEnd (2 * H.om) &&
    filledB L H.key.sEnd (g.Lam + g.NP * g.lt) && filledB L H.cells.sEnd (2 * H.om'')

/-- The long tables' tests on lengths, on the shape of what was heard. -/
def longB (g : Geo) (H : Heard5Sh) : Bool :=
  (2 ^ g.la == 2 ^ g.ls * g.T) && (2 ^ g.lt == g.T) && decide (g.ls ≤ g.ldh) &&
    (H.scores.all fun o => decide (g.ls ≤ g.ldh) && decide (g.ldh ≤ o.2.r - 1)) &&
    decide (g.lgk + g.lt ≤ H.division.r - 1) &&
    decide (g.lt + g.lgk + g.ls ≤ H.atIndex.r - 1) && decide (g.lt ≤ H.key.r - 1)

/-- **The tests of the tables' maker that read no value** (placeOk,
Johnson/Desc/First/Att/Claims/ReadsReturn.lean, without its two tests on values): the lookup's test
on its planes; every table of the plan fits the list of matrices; the long tables' lengths; the
numbers of entries add up. -/
def placeB (A : Attention.Plan) (H : Heard5Sh) (K : HeardAll) : Bool :=
  VerifiableInference.Desc.First.Look.planesOk K.shape (P.parCOf A).geo.lmb &&
    ((attAsks A.S (nScores A.S)).all fun a => P.fits (P.parCOf A).mats a.1 a.2.1 a.2.2) &&
    longB (P.parCOf A).geo H &&
    (3 * (P.parCOf A).geo.nScores + (nScores A.S + 6) * (P.parCOf A).geo.nRows +
      (P.parCOf A).geo.nOut + (2 * nScores A.S + 5) * (P.parCOf A).geo.nQkv +
      3 * (P.parCOf A).geo.nPlanes == (P.parCOf A).nW)

/-- **THE ONE BOOL ON THE SHAPE** for the tables of the quiet step behind the reads: H: the shape of
what the segment's own rounds handed on; K: of what the lookup returned; L: the ledger's.
SUFFICIENT, not necessary. -/
def tabsG (A : Attention.Plan) (H : Heard5Sh) (K : HeardAll) (L : LedSh) : Bool :=
  ptsB (P.parCOf A).geo K.zk H L && placeB A H K && tabsFitB (P.parCOf A).geo H K

/-- **THE TWO TESTS ON VALUES**, at the state's own parts: the units' inner points and the
division's points share their last coordinates with the lookup's point (mergedPlanes, mergedTokens,
Johnson/Desc/First/Att/TablesP.lean). No where the function of the points refuses. -/
def valsT (A : Attention.Plan) (gl : Forest.Heard) (h : Heard) (F : Fork) : Bool :=
  match P.ptsFrom (P.parCOf A).geo gl.zk h F with
  | some p => P.mergedPlanes (P.parCOf A).geo.lmS gl.zx p.planes &&
      P.mergedTokens (P.parCOf A).geo gl.zx p.d
  | none => false

/-- The tables that are made, of the state's own parts: the two makers in a row. -/
def tabsOf (A : Attention.Plan) (gl : Forest.Heard) (h : Heard) (F : Fork) :
    Option Attention.Tables :=
  (P.ptsFrom (P.parCOf A).geo gl.zk h F).bind fun p =>
    (P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb gl) p).map tabsBack

/-! ## 2 Lengths and marks -/

theorem filled_of_B {F : Fork} {first n : Nat} (h : filledB (ledSh F) first n = true) :
    ∀ i, i < n → ∃ y f, P.Put F (first + i) y f := by
  unfold filledB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h0 : first + n ≤ F.gotF.toList.length := of_decide_eq_true h1
  have h1' : first + n ≤ F.gotF.size := by simpa using h0
  intro i hi
  have hl : first + i < F.gotF.toList.length := by omega
  have hm : F.gotF.toList[first + i] ∈ (F.gotF.toList.drop first).take n :=
    List.mem_iff_getElem.2 ⟨i, by simp; omega, by simp⟩
  have ht : F.gotF.toList[first + i] = true := List.all_eq_true.1 h2 _ hm
  have hs : first + i < F.gotF.size := by simpa using hl
  refine ⟨_, _, ?_, rfl, rfl⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
  simpa using ht

theorem innerLen_is (u : UnitG) (z : Array E) : (P.inner u z).size = innerLen u z.size := by
  unfold P.inner innerLen
  rw [Array.size_extract]
  omega

theorem zk_size (zk : Array (Array E)) (c : Nat) :
    (zk.getD c #[]).size = (zk.toList.map (·.size)).getD c 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases zk[c]? <;> rfl

/-- A list of answers, one a member. -/
theorem forall₂_of_each {α β : Type} {R : α → β → Prop} : ∀ (l : List α), (∀ a ∈ l, ∃ b, R a b) →
    ∃ l', List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl⟩ := forall₂_of_each l fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: l', .cons hb hl⟩

/-- Each member of the first list has its fellow in the second. -/
theorem fellow_of_forall₂ {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab ht, a, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, r⟩ := fellow_of_forall₂ ht a h'
      exact ⟨b, List.mem_cons_of_mem _ hb, r⟩

/-! ## 3 The function of the points returns -/

/-- **RETURNS, THE FIRST MAKER.** CONDITIONAL on the test's yes at the shapes. No premise speaks of
a value. -/
theorem pts_returns {g : Geo} {gl : Forest.Heard} {h : Heard} {F : Fork}
    (hB : ptsB g (heardAll gl).zk (heard5Sh h) (ledSh F) = true) :
    ∃ p, P.ptsFrom g gl.zk h F = some p := by
  unfold ptsB at hB
  simp only [Bool.and_eq_true, beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b0, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hB
  have hz0 := sized_of_B b0
  have hz : OnBytes.Model.Road.Sized F := ⟨hz0.1, hz0.2.1, hz0.2.2⟩
  have n1 : (g.units .kr [.rm, .rd]).length = h.remainders.size := by
    rw [b1]
    show h.remainders.toList.length = _
    rw [Array.length_toList]
  have n2 : g.scores.length = h.scores.size := by
    rw [b2]
    show (h.scores.toList.map _).length = _
    rw [List.length_map, Array.length_toList]
  have hu : ∀ u ∈ g.scores, (P.inner u (gl.zk.getD u.call #[])).size = unitLen g u := by
    intro u hu
    rw [innerLen_is, zk_size]
    exact beq_iff_eq.1 (List.all_eq_true.1 b3 u hu)
  cases sW : g.single .wl with
  | none => simp [sW] at b5
  | some uW =>
    cases sX : g.single .ix with
    | none => simp [sW, sX] at b5
    | some uX =>
      cases sH : g.single .wh with
      | none => simp [sW, sX, sH] at b5
      | some uH =>
        simp only [sW, sX, sH, Bool.and_eq_true, beq_iff_eq] at b5
        obtain ⟨⟨⟨⟨⟨d1, d2⟩, d3⟩, d4⟩, d5⟩, d6⟩ := b5
        have zW : (P.inner uW (gl.zk.getD uW.call #[])).size = 1 + g.lgk + g.lt + g.ldh := by
          rw [innerLen_is, zk_size]
          exact d4
        have zX : (P.inner uX (gl.zk.getD uX.call #[])).size = g.lgk + g.lt := by
          rw [innerLen_is, zk_size]
          exact d5
        have zH : (P.inner uH (gl.zk.getD uH.call #[])).size = g.lgk + g.lt + g.ldh := by
          rw [innerLen_is, zk_size]
          exact d6
        have each : ∀ x ∈ (g.scores.toArray.zip h.scores).toList,
            ∃ f, P.ScoresLeft g gl.zk F x f := by
          intro x hx
          have hx' : x ∈ g.scores.zip h.scores.toList := by simpa using hx
          obtain ⟨W, w1, w2⟩ := P.scoreW_ret (g := g) (u := x.1) (zkc := gl.zk.getD x.1.call #[])
            (P.chal x.2.2) (hu _ (List.of_mem_zip hx').1)
          have hm : (x.1, x.2.1, sumSh x.2.2) ∈ g.scores.zip (heard5Sh h).scores := by
            show _ ∈ g.scores.zip (h.scores.toList.map fun o => (o.1, sumSh o.2))
            rw [List.zip_map_right]
            exact List.mem_map.2 ⟨x, hx', rfl⟩
          have hf := List.all_eq_true.1 b4 _ hm
          obtain ⟨f, e⟩ := P.left_ret hz x.2.2 W (n := 2 * x.1.pcs.length)
            (by rw [w2, P.weights_size]) (filled_of_B hf)
          exact ⟨f, W, w1, e⟩
        obtain ⟨fs, hfs⟩ := forall₂_of_each _ each
        obtain ⟨fE, eE⟩ := P.left_ret hz h.division
          (P.wDivision g (P.weights uW (gl.zk.getD uW.call #[]))
            (P.inner uW (gl.zk.getD uW.call #[])) h) (n := 2 * g.NP)
          (by unfold P.wDivision; rw [Array.size_map, P.weights_size, d1]) (filled_of_B c1)
        obtain ⟨fM, eM⟩ := P.left_ret hz h.below
          (P.wBelow g (P.weights uW (gl.zk.getD uW.call #[]))
            (P.inner uW (gl.zk.getD uW.call #[])) h) (n := 2 * g.NP)
          (by unfold P.wBelow; rw [Array.size_map, P.weights_size, d1]) (filled_of_B c2)
        obtain ⟨fO, eO⟩ := P.left_ret hz h.on
          (P.wOn g (P.weights uW (gl.zk.getD uW.call #[]))
            (P.inner uW (gl.zk.getD uW.call #[])) h) (n := 2 * g.NP)
          (by unfold P.wOn; rw [Array.size_map, P.weights_size, d1]) (filled_of_B c3)
        obtain ⟨fF, eF⟩ := P.left_ret hz h.atIndex (P.wAtIndex g h) (n := 2 * h.om.size)
          (by unfold P.wAtIndex; rw [Array.size_map]) (filled_of_B c4)
        obtain ⟨fK, eK⟩ := P.leftKey_ret hz g h.key (P.chal h.atIndex) h.om'
          (n := g.Lam + g.NP * g.lt) (Nat.le_refl _) (Nat.le_refl _) (filled_of_B c5)
        obtain ⟨fH, eH⟩ := P.left_ret hz h.cells (P.wCells g h) (n := 2 * h.om''.size)
          (by unfold P.wCells; rw [Array.size_map]) (filled_of_B c6)
        have LI : P.LeftIs g gl.zk h F ⟨fs.toArray, fE, fM, fO, fF, fK, fH⟩ :=
          ⟨n2, hfs, uW, sW, by rw [P.weights_size, d1], zW, eE, eM, eO, eF, eK, eH⟩
        have n3 : g.scores.length = (fs.toArray).size := by
          have e := hfs.length_eq
          simp only [Array.toList_zip, List.length_zip, Array.length_toList,
            List.size_toArray] at e ⊢
          omega
        obtain ⟨p, hp⟩ := P.points_ret (L := ⟨fs.toArray, fE, fM, fO, fF, fK, fH⟩) n1 n2 n3 hu sW sX
          sH (by rw [P.pieces_size, d1]) (by rw [P.pieces_size, d2]) (by rw [P.pieces_size, d3])
          zW zX zH
        refine ⟨p, ?_⟩
        unfold P.ptsFrom
        rw [K5Law.leftP_of_is LI]
        exact hp

/-! ## 4 The tables' maker returns -/

/-- The long tables' tests. CONDITIONAL on: the function of the points returns; the test on the
shape. -/
theorem longs_of {g : Geo} {gl : Forest.Heard} {h : Heard} {L : Left} {p : Pts} (lk : LookIn)
    (hp : P.pointsOf g gl.zk h L = some p) (hB : longB g (heard5Sh h) = true) :
    (P.reads p.scores.size).all (K5Law.longOk g lk p) = true := by
  have PA := K5Law.points_are hp
  obtain ⟨uW, uX, uH, _, _, _, sW, _, _, _, _, eW, eC, _, _, _, _, _⟩ := (K5Law.cut5_of hp).at'
  have hW : p.d.ziW.size = g.lt := by
    rw [eW, Array.size_extract, sW]
    omega
  have hC : p.d.zcW.size = g.ldh := by
    rw [eC, Array.size_extract, sW]
    omega
  simp only [longB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hB
  have a5' : g.lgk + g.lt ≤ h.division.r.length - 1 := a5
  have a6' : g.lt + g.lgk + g.ls ≤ h.atIndex.r.length - 1 := a6
  have a7' : g.lt ≤ h.key.r.length - 1 := a7
  have rE : p.d.scE.r.size = h.division.r.length - 1 := by rw [PA.scE, sumOfP_size]
  have rF : p.x.scF.r.size = h.atIndex.r.length - 1 := by rw [PA.scF, sumOfP_size]
  have rK : p.x.scd.r.size = h.key.r.length - 1 := by rw [PA.scd, sumOfP_size]
  have lng : ∀ (zc w : Array E), w.size = g.T → g.ls ≤ zc.size → K5Law.lngB g zc w = true := by
    intro zc w h1 h2
    unfold K5Law.lngB
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨h1, a1⟩, h2⟩
  have hCl : g.ls ≤ p.d.zcW.size := by rw [hC]; exact a3
  have hrc : g.ls ≤ (p.x.rc g).size := by
    unfold P.MaxP.rc
    rw [Array.size_extract, rF]
    omega
  rw [K5Law.longs_eq]
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.and_true]
  refine ⟨lng _ _ (by rw [K5Law.eqTab_size, hW, a2]) hCl, ?_, lng _ _ ?_ hCl,
    lng _ _ (K5Law.tok_size _ _ _) hCl, lng _ _ (K5Law.tok_size _ _ _) hCl, lng _ _ ?_ hrc,
    lng _ _ ?_ hrc⟩
  · intro k hk
    obtain ⟨x, hx, ⟨e1, _⟩, _⟩ := fellow_of_forall₂ PA.units k hk
    have hx1 : x.1 ∈ (g.scores.toArray.zip h.scores).toList :=
      (List.of_mem_zip (by simpa using hx)).1
    have hx2 : x.1.2 ∈ h.scores.toList := (List.of_mem_zip (by simpa using hx1)).2
    have hm : (x.1.2.1, sumSh x.1.2.2) ∈ (heard5Sh h).scores :=
      List.mem_map.2 ⟨x.1.2, hx2, rfl⟩
    have hb := (a4 _ hm).2
    have hb' : g.ldh ≤ x.1.2.2.r.length - 1 := hb
    have hr : g.ls ≤ (P.lastCoords k.sc.r g.ldh).size := by
      rw [K5Law.lastCoords_size _ _ (by rw [e1, sumOfP_size]; exact hb')]
      exact a3
    exact ⟨lng _ _ (K5Law.tok_size _ _ _) hr, lng _ _ (K5Law.tok_size _ _ _) hr⟩
  · rw [K5Law.eqTab_size, Array.size_extract, rE, ← a2]
    congr 1
    omega
  · rw [K5Law.eqTab_size, ← a2]
    unfold P.MaxP.ri
    rw [Array.size_extract, rF]
    congr 1
    omega
  · rw [K5Law.eqTab_size, ← a2]
    unfold P.MaxP.pj
    rw [Array.size_extract, rK]
    congr 1
    omega

/-- **RETURNS, BOTH MAKERS: where the Bool on the shape and the two tests on values say yes, the
tables are made.** CONDITIONAL on these two. -/
theorem tabs_returns (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    (hG : tabsG A (heard5Sh h) (heardAll gl) (ledSh F) = true) (hV : valsT A gl h F = true) :
    (tabsOf A gl h F).isSome = true := by
  unfold tabsG at hG
  simp only [Bool.and_eq_true] at hG
  obtain ⟨⟨g1, g2⟩, _⟩ := hG
  obtain ⟨p, hp⟩ := pts_returns g1
  unfold valsT at hV
  rw [hp] at hV
  simp only [Bool.and_eq_true] at hV
  obtain ⟨L, _, hP⟩ := Option.bind_eq_some_iff.1 hp
  have hP' : P.pointsOf (geoOf A.S) gl.zk h L = some p := hP
  have hn : p.scores.size = nScores A.S := H2K5.Door.units_plan hP'
  unfold placeB at g2
  simp only [Bool.and_eq_true] at g2
  obtain ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩ := g2
  have hfits : (P.reads p.scores.size).all (fun r =>
      (K5Law.tabs (P.parCOf A).geo (P.lookOfO (P.parCOf A).geo.lmb gl) p r).all
        (K5Law.fitsT (P.parCOf A).mats)) = true := by
    rw [← List.all_flatMap, ← K5Law.laidBy_eq]
    have e := H2K5.Door.asks_laid A.S (P.lookOfO (P.parCOf A).geo.lmb gl) p
    rw [hn] at e
    rw [← e, List.all_map] at q2
    exact q2
  have hok : K5Law.placeOk (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW
      (P.lookOfO (P.parCOf A).geo.lmb gl) p = true := by
    unfold K5Law.placeOk
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨hV.1, hV.2⟩, q1⟩, hfits⟩, longs_of _ hP q3⟩, ?_⟩
    rw [hn]
    exact q4
  obtain ⟨t, ht⟩ := K5Law.tablesP_some hok
  unfold tabsOf
  rw [hp]
  show ((P.tablesP _ _ _ _ p).map tabsBack).isSome = true
  rw [ht]
  rfl

/-- **BOTH HALVES IN ONE EQUATION: where the Bool on the shape and the two tests on values say yes,
the shapes of the tables that are made are attFuns A.** CONDITIONAL on these two. -/
theorem tabs_shape (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    (hG : tabsG A (heard5Sh h) (heardAll gl) (ledSh F) = true) (hV : valsT A gl h F = true) :
    (tabsOf A gl h F).map (fun t => t.funs.toList.map funSh) = some (attFuns A) := by
  have hs := tabs_returns A hG hV
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hs
  rw [hT]
  unfold tabsOf at hT
  obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 hT
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hT
  unfold tabsG at hG
  simp only [Bool.and_eq_true] at hG
  exact congrArg some (tabs_carries A hp ht hG.2)

/-- **CARRIES, at the one Bool**: where the tables are made and the Bool says yes, their shapes are
attFuns A: the tests on values are not asked again. -/
theorem tabs_carries_G (A : Attention.Plan) {gl : Forest.Heard} {h : Heard} {F : Fork}
    {T : Attention.Tables} (hT : tabsOf A gl h F = some T)
    (hG : tabsG A (heard5Sh h) (heardAll gl) (ledSh F) = true) :
    T.funs.toList.map funSh = attFuns A := by
  unfold tabsOf at hT
  obtain ⟨p, hp, hT⟩ := Option.bind_eq_some_iff.1 hT
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hT
  unfold tabsG at hG
  simp only [Bool.and_eq_true] at hG
  exact tabs_carries A hp ht hG.2

end H2K5.Honest

#print axioms H2K5.Honest.filled_of_B
#print axioms H2K5.Honest.innerLen_is
#print axioms H2K5.Honest.zk_size
#print axioms H2K5.Honest.forall₂_of_each
#print axioms H2K5.Honest.fellow_of_forall₂
#print axioms H2K5.Honest.pts_returns
#print axioms H2K5.Honest.longs_of
#print axioms H2K5.Honest.tabs_returns
#print axioms H2K5.Honest.tabs_shape
#print axioms H2K5.Honest.tabs_carries_G
