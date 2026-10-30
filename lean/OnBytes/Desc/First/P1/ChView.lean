-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/ChView.lean: THE IMAGE OF A WRITTEN TRANSCRIPT UNDER THE MAPS OF A CHAIN
(`ChM.mapsR`, ChMaps.lean) IS THE CHAIN'S JOINED TRANSCRIPT OF THE STAGES' OWN IMAGES; so what the
chain's verifier puts out there, and what the chain claims at its end there, are had stage by stage.
A definition, three statements and their proofs. Bookkeeping: no protocol is read.

  `trCast`: a typed transcript along an equation of lists of rounds; `view_cast`, `app_view`.
  `ChM.trs D τ`: for each stage of the chain its own image: for a sumcheck the image of its written
    rounds under `rideMaps`; for a draw what its round's map makes of the verifier's message; for
    sent scalars the scalars and that. The written transcript is cut by `Maps.trL` and `Maps.trR`
    (OnBytes/Flat/KindsRow.lean).
  `ChM.view_join`: `(D.mapsR Ex).view τ = c.join Ex (D.trs τ)` (`Ch.join`, Cb/Pv/Att/ChainRun.lean),
    for every written transcript τ.
  `ChM.val_view`: the chain's function (`Ch.val`, Cb/Pv/Att/ChainVal.lean) at the image is the
    chain's run (`Ch.run`) on these.
  `ChM.last_view`: the chain's last claim at that output holds exactly if the claim carried along
    holds and the stages' debts (`Ch.Owed`, Cb/Pv/Att/ChainLast.lean) do on these.

NO NEW ARGUMENT: `Maps.view_app` (KindsRow.lean), `Ch.val_join`, `Ch.last_run`.

Limits. At every written transcript, also where a test of work fails (there the library's own
reading has no image: `Maps.tr_none`). What a stage's image is against what a text has heard is not
said here. Nothing on counts, on soundness or on any law.
-/
import OnBytes.Desc.First.P1.ChMaps
import OnBytes.Flat.KindsRow
import Cb.Pv.Att.ChainLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob IOR Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers Johnson.L5.Door
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open _root_.Run (ckP)

/-! ### Along an equation of lists of rounds -/

/-- A typed transcript along an equation of lists of rounds. -/
def trCast {s t : Shape} (h : s = t) (τ : Tr s) : Tr t := h ▸ τ

theorem view_cast {ds : List RDT} {s t : Shape} (h : s = t) (A : Maps ds s)
    (τ : Tr (uLT (ckP .two) ds)) : (A.castT h).view τ = trCast h (A.view τ) := by
  subst h
  rfl

/-- The image of two stretches in a row, the second's typed list replaced along an equation. -/
theorem app_view {ds es : List RDT} {s t t' : Shape} (h : t = t') (h2 : s ++ t = s ++ t')
    (A : Maps ds s) (B : Maps es t) (τ : Tr (uLT (ckP .two) (ds ++ es))) :
    ((A.app B).castT h2).view τ =
      Tr.app (A.view (Maps.trL ds es τ)) ((B.castT h).view (Maps.trR ds es τ)) := by
  subst h
  exact Maps.view_app A B τ

/-! ### The stages' own images -/

variable {M : Type}

namespace ChM

/-- For each stage of the chain its own image of the written transcript. -/
noncomputable def trs : {X : Type} → {c : Ch GE M X} → {ds : List RDT} → ChM c ds →
    Tr (uLT (ckP .two) ds) → c.Trs
  | _, _, _, .done _, _ => ()
  | _, _, _, .ride (Y := Y) (n := n) (ds := ds) dE vs dY dV DY num hf rest, τ =>
      ((rideMaps Y n dE vs dY dV DY num hf).view (Maps.trL (dE :: (vs ++ [dY, dV])) ds τ),
        rest.trs (Maps.trR (dE :: (vs ++ [dY, dV])) ds τ))
  | _, _, _, .draw1 (ds := ds) d rest, τ =>
      (((Maps.step (mDraw d) .nil).view (Maps.trL [d] ds τ)).2.1, rest.trs (Maps.trR [d] ds τ))
  | _, _, _, .drawPt (g := g) (ds := ds) d rest, τ =>
      (((Maps.step (mPoint g d) .nil).view (Maps.trL [d] ds τ)).2.1,
        rest.trs (Maps.trR [d] ds τ))
  | _, _, _, .send (n := n) (ds := ds) d rest, τ =>
      ((((Maps.step (mSend n d) .nil).view (Maps.trL [d] ds τ)).1.2,
          ((Maps.step (mSend n d) .nil).view (Maps.trL [d] ds τ)).2.1),
        rest.trs (Maps.trR [d] ds τ))

/-- **The image under the chain's maps is the joined transcript of the stages' own images.** -/
theorem view_join (Ex : ExtSpec) : ∀ {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds)
    (τ : Tr (uLT (ckP .two) ds)), (D.mapsR Ex).view τ = c.join Ex (D.trs τ)
  | _, _, _, .done _, _ => rfl
  | _, _, _, .ride (Y := Y) (n := n) (next := next) dE vs dY dV DY num hf rest, τ =>
      (app_view (Ch.shape_R Ex next).symm (congrArg (shapeRN Y n ++ ·) (Ch.shape_R Ex next).symm)
        (rideMaps Y n dE vs dY dV DY num hf) rest.maps τ).trans
        (congrArg (Tr.app (s := shapeRN Y n) _) (view_join Ex rest _))
  | _, _, _, .draw1 (next := next) d rest, τ =>
      (app_view (Ch.shape_R Ex next).symm
        (congrArg ([drawRound GE] ++ ·) (Ch.shape_R Ex next).symm)
        (Maps.step (mDraw d) .nil) rest.maps τ).trans
        (congrArg (Tr.app (s := [drawRound GE]) _) (view_join Ex rest _))
  | _, _, _, .drawPt (g := g) (next := next) d rest, τ =>
      (app_view (Ch.shape_R Ex next).symm
        (congrArg ([drawRound (Fin g → GE)] ++ ·) (Ch.shape_R Ex next).symm)
        (Maps.step (mPoint g d) .nil) rest.maps τ).trans
        (congrArg (Tr.app (s := [drawRound (Fin g → GE)]) _) (view_join Ex rest _))
  | _, _, _, .send (n := n) (next := next) d rest, τ =>
      (app_view (Ch.shape_R Ex next).symm
        (congrArg ([sendRound GE (Fin n) GE] ++ ·) (Ch.shape_R Ex next).symm)
        (Maps.step (mSend n d) .nil) rest.maps τ).trans
        (congrArg (Tr.app (s := [sendRound GE (Fin n) GE]) _) (view_join Ex rest _))

/-- The chain's function at the image is the chain's run on the stages' own images. -/
theorem val_view (Ex : ExtSpec) {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds) (x : X)
    (y : Ex.Str) (τ : Tr (uLT (ckP .two) ds)) :
    c.val Ex (x, y) ((D.mapsR Ex).view τ) = (c.run x (D.trs τ), y) := by
  rw [view_join, Ch.val_join]

/-- **The chain's last claim at its output on the image, stage by stage.** -/
theorem last_view (Ex : ExtSpec) {X : Type} {c : Ch GE M X} {ds : List RDT} (D : ChM c ds)
    (Dn : X → M → Prop) (x : X) (y : Ex.Str) (τ : Tr (uLT (ckP .two) ds)) (m : M) :
    c.Last Dn (c.val Ex (x, y) ((D.mapsR Ex).view τ)).1 m ↔ Dn x m ∧ c.Owed x (D.trs τ) m := by
  rw [val_view]
  exact Ch.last_run c Dn x _ m

end ChM

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.ChM.view_join
#print axioms OnBytes.Desc.First.P1.ChM.val_view
#print axioms OnBytes.Desc.First.P1.ChM.last_view
