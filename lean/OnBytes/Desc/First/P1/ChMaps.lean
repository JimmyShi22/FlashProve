-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/ChMaps.lean: HOW A STRETCH OF WRITTEN ROUNDS IS READ AS THE TYPED ROUNDS OF A
CHAIN of masked sumchecks, draws and sent scalars (Cb/Pv/Att/Chain.lean: `Ch`), stage by stage.
Definitions, and that the maps are as asked.

Why. The own rounds of a layers' sub-proof are one such chain (Cb/Pv/Lay/Own.lean), and the
library's theorems on the whole of them stand on its rounds (`Ch.sh`, `Ch.shape_R`). A list of maps
(`Maps`, OnBytes/Flat/CarrySMaps.lean) against these rounds carries such a theorem's counts to the
written rounds.

  `mSend`: n scalars, in the order in which they are written; one element. `mSendPt` is not here:
    no stage of the layers' chain sends and draws a point.
  `mEpsN n`: the first round of a chain's sumcheck: n further scalars, then the sum of the hiding
    polynomial; one element.
  `mid_shape`: the rounds of formats "k cube variables of degree 2, then the further variable" are
    the list that `midMaps` (RoundMaps.lean) is typed with.
  `ChM c ds`: the data, stage by stage: which written rounds are read as which stage of the chain
    c. At a sumcheck: that its formats are k cube variables of degree 2 and the further variable of
    degree DY, and a numbering of its end values. At a draw: of one element, or of a point of g
    coordinates.
  `ChM.maps`: the list of maps against `c.sh`; `ChM.mapsR`: against the shape of the chain's
    reduction.
  `ChM.Ds`: what is asked of the written rounds: what each sends and draws. `ChM.maps_ok`,
    `ChM.mapsR_ok`.

Limits. Shapes and maps alone. No round is skipped. That a plan's stretch meets `Ds` is not shown
here. Nothing on the counts, on what the image of a transcript is against what a text has heard, or
on any law. A sumcheck with a variable of another degree than 2, or a draw from another set, has no
constructor.
-/
import OnBytes.Desc.First.P1.RoundMaps
import Cb.Pv.Lay.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice

/-! ### Two more maps -/

/-- n scalars, in the order in which they are written; one element. -/
def mSend (n : ℕ) (d : RDT) : RMap d (sendRound GE (Fin n) GE) :=
  RMap.one (fun m => ((), fun i : Fin n => sentT d m i.val)) id

theorem mSend_ok (n : ℕ) {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns 1 0 a) :
    (mSend n d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.one_ok _ h Function.injective_id

/-- The first round of a chain's sumcheck: n further scalars, then the sum of the hiding
polynomial; one element. -/
def mEpsN (n : ℕ) (d : RDT) : RMap d (rRoundN GE n) :=
  RMap.one (fun m => ((), (fun i : Fin n => sentT d m i.val, sentT d m n))) id

theorem mEpsN_ok (n : ℕ) {d : RDT} (h : ∃ ns a, SendsDraws (toRD d) ns 1 0 a) :
    (mEpsN n d).OK := by
  obtain ⟨_, _, h⟩ := h
  exact RMap.one_ok _ h Function.injective_id

/-- The rounds of these formats, as the list that `midMaps` is typed with. -/
theorem mid_shape (k DY : ℕ) (A : Type) :
    List.replicate k (sRound (pfCube GE 2)) ++ [sRound (pDummy GE DY), pRoundV GE A] =
      sRounds (List.replicate k (pfCube GE 2) ++ [pDummy GE DY]) ++ [pRoundV GE A] := by
  simp [sRounds, List.map_append, List.map_replicate]

/-! ### The data, stage by stage -/

variable {M : Type}

/-- Which written rounds are read as which stage of a chain. -/
inductive ChM : {X : Type} → Ch GE M X → List RDT → Type 1
  | done (X : Type) : ChM (.done X) []
  | ride {X : Type} {Y : PscPar GE} {n : ℕ} {F : ∀ st, HFixs (Y.vars st)}
      {cl : X → (Fin n → GE) → GE × Y.St} {msg : M → Y.J → GE}
      {L : X → (Fin n → GE) → M → Prop} {Ow : (X × (Fin n → GE)) × Y.Out → M → Prop}
      {next : Ch GE M ((X × (Fin n → GE)) × Y.Out)} {ds : List RDT}
      (dE : RDT) (vs : List RDT) (dY dV : RDT) (DY : ℕ) (num : Y.A → ℕ)
      (hf : Y.fmt = List.replicate vs.length (pfCube GE 2) ++ [pDummy GE DY])
      (rest : ChM next ds) :
      ChM (.ride Y n F cl msg L Ow next) ((dE :: (vs ++ [dY, dV])) ++ ds)
  | draw1 {X : Type} {err : ℕ} {P : X → M → Prop} {next : Ch GE M (X × GE)} {ds : List RDT}
      (d : RDT) (rest : ChM next ds) : ChM (.draw (dE GE) err P next) ([d] ++ ds)
  | drawPt {X : Type} {g err : ℕ} {P : X → M → Prop} {next : Ch GE M (X × (Fin g → GE))}
      {ds : List RDT} (d : RDT) (rest : ChM next ds) :
      ChM (.draw (dPt GE g) err P next) ([d] ++ ds)
  | send {X : Type} {n err : ℕ} {P : X → M → Prop} {L : X → (Fin n → GE) → M → Prop}
      {next : Ch GE M ((X × (Fin n → GE)) × GE)} {ds : List RDT}
      (d : RDT) (rest : ChM next ds) : ChM (.send n (dE GE) err P L next) ([d] ++ ds)

namespace ChM

/-- A sumcheck's written rounds, read as the chain's rounds of that stage. -/
noncomputable def rideMaps (Y : PscPar GE) (n : ℕ) (dE : RDT) (vs : List RDT) (dY dV : RDT)
    (DY : ℕ) (num : Y.A → ℕ)
    (hf : Y.fmt = List.replicate vs.length (pfCube GE 2) ++ [pDummy GE DY]) :
    Maps (dE :: (vs ++ [dY, dV])) (shapeRN Y n) :=
  .step (mEpsN n dE) (Maps.castT ((mid_shape vs.length DY Y.A).trans (by rw [hf]))
    (midMaps DY num dY dV vs))

/-- **The list of maps, against the chain's rounds.** -/
noncomputable def maps : {X : Type} → {c : Ch GE M X} → {ds : List RDT} → ChM c ds → Maps ds c.sh
  | _, _, _, .done _ => .nil
  | _, _, _, .ride (Y := Y) (n := n) dE vs dY dV DY num hf rest =>
      (rideMaps Y n dE vs dY dV DY num hf).app rest.maps
  | _, _, _, .draw1 d rest => (Maps.step (mDraw d) .nil).app rest.maps
  | _, _, _, .drawPt (g := g) d rest => (Maps.step (mPoint g d) .nil).app rest.maps
  | _, _, _, .send (n := n) d rest => (Maps.step (mSend n d) .nil).app rest.maps

/-- The same against the shape of the chain's reduction. -/
noncomputable def mapsR (Ex : ExtSpec) {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds) :
    Maps ds (c.R Ex).shape :=
  Maps.castT (Ch.shape_R Ex c).symm D.maps

/-- What is asked of the written rounds: what each sends and draws. -/
def Ds : {X : Type} → {c : Ch GE M X} → {ds : List RDT} → ChM c ds → Prop
  | _, _, _, .done _ => True
  | _, _, _, .ride dE vs dY dV _ _ _ rest => PscDs dE vs dY dV ∧ rest.Ds
  | _, _, _, .draw1 d rest => (∃ ns a, SendsDraws (toRD d) ns 1 0 a) ∧ rest.Ds
  | _, _, _, .drawPt (g := g) d rest => (∃ ns a, SendsDraws (toRD d) ns g 0 a) ∧ rest.Ds
  | _, _, _, .send d rest => (∃ ns a, SendsDraws (toRD d) ns 1 0 a) ∧ rest.Ds

theorem rideMaps_ok (Y : PscPar GE) (n : ℕ) {dE : RDT} {vs : List RDT} {dY dV : RDT} (DY : ℕ)
    (num : Y.A → ℕ) (hf : Y.fmt = List.replicate vs.length (pfCube GE 2) ++ [pDummy GE DY])
    (H : PscDs dE vs dY dV) : (rideMaps Y n dE vs dY dV DY num hf).OK :=
  ⟨mEpsN_ok n H.o, Maps.ok_castT _ (midMaps_ok DY num H.mid)⟩

/-- **The maps are as asked.** -/
theorem maps_ok : ∀ {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds), D.Ds → D.maps.OK
  | _, _, _, .done _, _ => trivial
  | _, _, _, .ride (Y := Y) (n := n) _ _ _ _ DY num hf rest, h =>
      Maps.OK.app (rideMaps_ok Y n DY num hf h.1) (maps_ok rest h.2)
  | _, _, _, .draw1 _ rest, h => Maps.OK.app ⟨mDraw_ok h.1, trivial⟩ (maps_ok rest h.2)
  | _, _, _, .drawPt _ rest, h => Maps.OK.app ⟨mPoint_ok h.1, trivial⟩ (maps_ok rest h.2)
  | _, _, _, .send (n := n) _ rest, h => Maps.OK.app ⟨mSend_ok n h.1, trivial⟩ (maps_ok rest h.2)

theorem mapsR_ok (Ex : ExtSpec) {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds)
    (h : D.Ds) : (D.mapsR Ex).OK :=
  Maps.ok_castT _ (maps_ok D h)

end ChM

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.ChM.maps_ok
#print axioms OnBytes.Desc.First.P1.ChM.mapsR_ok
