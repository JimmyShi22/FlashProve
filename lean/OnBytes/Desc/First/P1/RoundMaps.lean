-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/RoundMaps.lean: HOW THE WRITTEN ROUNDS OF A MASKED SUMCHECK, OF A PRODUCT
LAYER AND OF A JOIN ARE READ AS THE TYPED ROUNDS OF THE LIBRARY'S BLOCKS (Cb/Pv/Lay/): one map for
each kind of round, and the lists of maps. Definitions, and that they are as asked. A FILE SHARED BY
the files that carry the layers' typed blocks to the layers' own text.

In the style of OnBytes/Flat/KindsBattSend.lean: a reading is laid a kind of block at a time
(`Maps`, OnBytes/Flat/CarrySMaps.lean). That each definition is accepted by Lean shows that the
block's rounds are as many, and of the types, as the maps say. The single maps are those of the
merge's files (Johnson/Top/H0/MergeLaw/Maps.lean: mZ, m0, mR, mY, mV), made general in the
number of scalars and in the names of the end values, with one more for a round that draws a point.

  `mEps`: the sum of the hiding polynomial: one scalar; one element. `mVar`: a variable's round: two
    scalars; one element. `mY n`: the round of the further variable: n scalars; one element other
    than 0. `mVals num`: the end values: the scalar number num a under the name a; nothing is drawn.
    `mDraw`: an empty message; one element. `mPoint n`: an empty message; n elements at once. Each
    with `…_ok`.
  `midMaps`, `MidDs`, `midMaps_ok`: the variables' rounds, the further variable's, the end values'.
  `pscMaps`, `PscDs`, `pscMaps_ok`: a masked sumcheck, against `pscShape` (Cb/Pv/Lay/Shapes.lean).
  `bNum`: the left end value has the number 0 and the name false, the right one 1 and true.
  `layerMaps`, `LayerDs`, `layerMaps_ok`: a product layer: a masked sumcheck with two scalars in the
    further variable's round and two end values, and the draw of the point on the line.
  `prodMaps`, `prodMaps_ok`: against the shape of any `ProdL` (Cb/Pv/Lay/Prod.lean) with as many
    variables. `routedMaps`, `routedMaps_ok`: against the shape of any `RoutedL`
    (Cb/Pv/Lay/Routed.lean): the round that draws the fresh point, then the layer.

Limits. Shapes and maps alone. `MidDs`, `PscDs`, `LayerDs` say what each written round must send and
draw: THAT A PLAN'S STRETCH HAS THEM IS NOT SHOWN HERE. Nothing on the counts, on what the image of
a transcript is against what a text has heard, or on any law. No round is skipped.
-/
import OnBytes.Flat.KindsBattSend
import OnBytes.Flat.CarrySProx
import OnBytes.Flat.CarrySForms
import Cb.Pv.Lay.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes.Flat OnBytes.Maker OnBytes.Slice

/-! ### One map for each kind of round -/

/-- The sum of the hiding polynomial: one scalar; one element. -/
def mEps (d : RDT) : RMap d (pRound0 GE) := RMap.one (fun m => ((), sentT d m 0)) id

/-- A variable's round: two scalars; one element. -/
def mVar (d : RDT) : RMap d (sRound (pfCube GE 2)) :=
  RMap.one (fun m => ((), fun t : Fin 2 => sentT d m t.val)) id

/-- The round of the further variable: n scalars; one element other than 0. -/
noncomputable def mY (n : ℕ) (d : RDT) : RMap d (sRound (pDummy GE n)) :=
  RMap.seed (fun m => ((), fun t : Fin n => sentT d m t.val)) 0
    fun s => (⟨s.2.val, s.2.ne_zero⟩ : {x : GE // x ≠ 0})

/-- The end values: the scalar number num a under the name a; nothing is drawn. -/
def mVals {A : Type} (num : A → ℕ) (d : RDT) : RMap d (pRoundV GE A) :=
  RMap.none (fun m => ((), fun a => sentT d m (num a))) ()

/-- An empty message; one element. -/
def mDraw (d : RDT) : RMap d (drawRound GE) := RMap.one (fun _ => ((), ())) id

/-- An empty message; n elements at once. -/
def mPoint (n : ℕ) (d : RDT) : RMap d (drawRound (Fin n → GE)) :=
  RMap.vec (fun _ => ((), ())) n id

theorem mEps_ok {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns 1 0 a) : (mEps d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.one_ok _ h Function.injective_id

theorem mVar_ok {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns 1 0 a) : (mVar d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.one_ok _ h Function.injective_id

theorem mDraw_ok {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns 1 0 a) : (mDraw d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.one_ok _ h Function.injective_id

theorem mPoint_ok {n : ℕ} {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns n 0 a) :
    (mPoint n d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.vec_ok _ h Function.injective_id

theorem mVals_ok {A : Type} (num : A → ℕ) {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns 0 0 a) :
    (mVals num d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.none_ok (r' := pRoundV GE A) _ h ()

theorem mY_ok (n : ℕ) {d : RDT} (hp : PlainDraws (Fmt.dsOf d.entry d.kind))
    (hE : nE (Fmt.dsOf d.entry d.kind) = 0 + 1) (hP : nP (Fmt.dsOf d.entry d.kind) = 0)
    (hz : IsNZ (Fmt.dsOf d.entry d.kind) 0) (hl : d.entry.logN ≤ 64) : (mY n d).OK := by
  refine RMap.seed_ok _ hp hE hP hz hl ?_
  intro s s' h
  have h1 : s.2.val = s'.2.val := congrArg Subtype.val h
  exact Prod.ext (funext fun i => i.elim0) (Units.ext h1)

/-! ### The middle of a masked sumcheck -/

/-- The variables' rounds, the round of the further variable, the round of the end values. -/
noncomputable def midMaps {A : Type} (n : ℕ) (num : A → ℕ) (dY dV : RDT) : (ds : List RDT) →
    Maps (ds ++ [dY, dV])
      (List.replicate ds.length (sRound (pfCube GE 2)) ++ [sRound (pDummy GE n), pRoundV GE A])
  | [] => .step (mY n dY) (.step (mVals num dV) .nil)
  | d :: ds => .step (mVar d) (midMaps n num dY dV ds)

/-- What is asked of these written rounds: what each sends and draws. -/
structure MidDs (ds : List RDT) (dY dV : RDT) : Prop where
  r : ∀ d ∈ ds, ∃ ns a, SendsDraws (toRD d) ns 1 0 a
  yPlain : PlainDraws (Fmt.dsOf dY.entry dY.kind)
  yE : nE (Fmt.dsOf dY.entry dY.kind) = 0 + 1
  yP : nP (Fmt.dsOf dY.entry dY.kind) = 0
  yNZ : IsNZ (Fmt.dsOf dY.entry dY.kind) 0
  yLog : dY.entry.logN ≤ 64
  v : ∃ ns a, SendsDraws (toRD dV) ns 0 0 a

theorem midMaps_ok' {A : Type} (n : ℕ) (num : A → ℕ) {dY dV : RDT} (hY : (mY n dY).OK)
    (hV : (mVals num dV).OK) :
    ∀ ds : List RDT, (∀ d ∈ ds, (mVar d).OK) → (midMaps n num dY dV ds).OK
  | [], _ => ⟨hY, hV, trivial⟩
  | d :: ds, h => ⟨h d List.mem_cons_self,
      midMaps_ok' n num hY hV ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

theorem midMaps_ok {A : Type} (n : ℕ) (num : A → ℕ) {ds : List RDT} {dY dV : RDT}
    (H : MidDs ds dY dV) : (midMaps n num dY dV ds).OK :=
  midMaps_ok' n num (mY_ok n H.yPlain H.yE H.yP H.yNZ H.yLog) (mVals_ok num H.v) ds
    fun d hd => mVar_ok (H.r d hd)

/-! ### A masked sumcheck -/

/-- A masked sumcheck's written rounds, read as `pscShape`. -/
noncomputable def pscMaps {A : Type} (n : ℕ) (num : A → ℕ) (dE : RDT) (ds : List RDT)
    (dY dV : RDT) : Maps (dE :: (ds ++ [dY, dV])) (pscShape GE ds.length n A) :=
  .step (mEps dE) (midMaps n num dY dV ds)

structure PscDs (dE : RDT) (ds : List RDT) (dY dV : RDT) : Prop where
  o : ∃ ns a, SendsDraws (toRD dE) ns 1 0 a
  mid : MidDs ds dY dV

theorem pscMaps_ok {A : Type} (n : ℕ) (num : A → ℕ) {dE : RDT} {ds : List RDT} {dY dV : RDT}
    (H : PscDs dE ds dY dV) : (pscMaps n num dE ds dY dV).OK :=
  ⟨mEps_ok H.o, midMaps_ok n num H.mid⟩

/-! ### A product layer; a join with a product layer -/

/-- The left end value has the number 0 and the name false, the right one 1 and true. -/
def bNum (b : Bool) : ℕ := if b then 1 else 0

/-- A product layer's written rounds: the masked sumcheck, and the point on the line. -/
noncomputable def layerMaps (dE : RDT) (ds : List RDT) (dY dV dT : RDT) :
    Maps ((dE :: (ds ++ [dY, dV])) ++ [dT]) (pscShape GE ds.length 2 Bool ++ [drawRound GE]) :=
  (pscMaps 2 bNum dE ds dY dV).app (.step (mDraw dT) .nil)

structure LayerDs (dE : RDT) (ds : List RDT) (dY dV dT : RDT) : Prop where
  psc : PscDs dE ds dY dV
  t : ∃ ns a, SendsDraws (toRD dT) ns 1 0 a

theorem layerMaps_ok {dE : RDT} {ds : List RDT} {dY dV dT : RDT} (H : LayerDs dE ds dY dV dT) :
    (layerMaps dE ds dY dV dT).OK :=
  Maps.OK.app (pscMaps_ok 2 bNum H.psc) ⟨mDraw_ok H.t, trivial⟩

theorem prod_shape (L : ProdL GE) {Ex : ExtSpec} (V : ShortK L.T.par Ex) (ds : List RDT)
    (hk : ds.length = L.k) :
    pscShape GE ds.length 2 Bool ++ [drawRound GE] = (L.blk V).shape := by
  rw [hk, L.shape_eq V]

/-- **A product layer, against any `ProdL` with as many variables.** -/
noncomputable def prodMaps (L : ProdL GE) {Ex : ExtSpec} (V : ShortK L.T.par Ex) (dE : RDT)
    (ds : List RDT) (dY dV dT : RDT) (hk : ds.length = L.k) :
    Maps ((dE :: (ds ++ [dY, dV])) ++ [dT]) (L.blk V).shape :=
  Maps.castT (prod_shape L V ds hk) (layerMaps dE ds dY dV dT)

theorem prodMaps_ok (L : ProdL GE) {Ex : ExtSpec} (V : ShortK L.T.par Ex) {dE : RDT}
    {ds : List RDT} {dY dV dT : RDT} (hk : ds.length = L.k) (H : LayerDs dE ds dY dV dT) :
    (prodMaps L V dE ds dY dV dT hk).OK :=
  Maps.ok_castT _ (layerMaps_ok H)

theorem routed_shape (G : RoutedL GE) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) (ds : List RDT)
    (hk : ds.length = G.g + G.k') :
    drawRound (Fin G.g → GE) :: (pscShape GE ds.length 2 Bool ++ [drawRound GE]) =
      (G.blk V).shape := by
  rw [hk, G.shape_eq V]

/-- **The round that draws the fresh point, then the layer: against any `RoutedL`.** -/
noncomputable def routedMaps (G : RoutedL GE) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex)
    (dJ dE : RDT) (ds : List RDT) (dY dV dT : RDT) (hk : ds.length = G.g + G.k') :
    Maps (dJ :: ((dE :: (ds ++ [dY, dV])) ++ [dT])) (G.blk V).shape :=
  Maps.castT (routed_shape G V ds hk) (.step (mPoint G.g dJ) (layerMaps dE ds dY dV dT))

theorem routedMaps_ok (G : RoutedL GE) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) {dJ dE : RDT}
    {ds : List RDT} {dY dV dT : RDT} (hk : ds.length = G.g + G.k')
    (hJ : ∃ ns a, SendsDraws (toRD dJ) ns G.g 0 a) (H : LayerDs dE ds dY dV dT) :
    (routedMaps G V dJ dE ds dY dV dT hk).OK :=
  Maps.ok_castT _ ⟨mPoint_ok hJ, layerMaps_ok H⟩

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.midMaps_ok
#print axioms OnBytes.Desc.First.P1.pscMaps_ok
#print axioms OnBytes.Desc.First.P1.layerMaps_ok
#print axioms OnBytes.Desc.First.P1.prodMaps_ok
#print axioms OnBytes.Desc.First.P1.routedMaps_ok
