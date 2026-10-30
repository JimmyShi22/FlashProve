-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Item.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: every field of ItemOpens is a hypothesis. That the
fields can hold together: no example is known. Nothing on soundness, on completeness or on any other
property. No property is claimed.

All hypotheses of W/Join.lean at one state, in one structure, and the fourteen worths from it, in
the form in which the hypothesis `K4Worths` (Johnson/Desc/ProofFile/Honest/K4/Law/Worth.lean) asks
them at a state.

  `ItemOpens h pc D tl P g o F₀ F₁ mask Mm`   F₀: the ledger in front of "front"; F₁: the ledger
      that "front" leaves; mask: the mask row; Mm: the matrices. Nine fields.
  `item_worths`   FrontWorth in F₁'s world at whatever "front" has read, and BackWorth in the world
      of whatever ledger "back" leaves.

WHAT EACH FIELD OF ItemOpens RESTS ON.
  ground, sizes, grp   proved behind an accepting decision, from nine public facts on the plan
      (W/ItemOfKept.lean).
  opened, and back's first half   in two halves
      (Johnson/Desc/ProofFile/Honest/K4/Law/W/Halves.lean): "a slot is worth the reading of the
      honest part's own word" (`opened_left`, Johnson/Desc/ProofFile/Honest/K4/Law/SlotsTrue.lean),
      and "that reading is the library's term at the cells" (the hypothesis OpenedRight; laws for
      ten of its fourteen fields: nine in Johnson/Road/K4/C/, emb's in Law/W/EmbRight.lean). At rt,
      sc, sel, sideA, sideB the second half has no term of the library: it says that the entries
      which the honest side has read are the world's; at rt, sc, sel besides, that a form's worth at
      the end point is the extension of its worths at the corners. At emb it follows where the
      stream that comes in is the embedding of the tokens (the library's identity j11;
      W/EmbOpened.lean, at the library's own sizes alone), and from nothing else that is known.
  idn   the library's NormField (Johnson/Road/Rows/LayerTop.lean), at the library's full-size
      structure of sizes, four layers in a group, and matrices that agree with Mm on the cells read;
      at another size: the integer rule of the model.
  hot   the selector's identity at one point: the claims of group 10 restated in the library's terms
      (`hot_zero_iff`, Johnson/Road/K4/HotIs.lean). It follows at every point from the identity at
      every position (`hotPoint_of_cube`, W/HotEmb.lean): that a selector's entries sum to 1 at the
      cells: a fact on the witness.
  own, and back's second half   the own claims of six sumchecks. They ask further equations on slots
      (W/OpenedOwn.lean). OwnBack.stack is the dearest: W/Join.lean, at the field.
  look   a call: `look_of_asks` (W/LookAsks.lean), from the lookup's own sentence on its planes
      (K3Planes) and what it has heard, at an assignment of the lookup's places that holds the mask
      row and Mm's matrix of planes.
-/
import Johnson.Road.K4.W.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Pub Own)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (planesParts formsBack)

/-- **All hypotheses at one state.** This defines a hypothesis; the definition claims nothing. -/
structure ItemOpens (h : Layer.Shape) (pc : List (List String)) (D : Dim) (tl : HTailF2) (P : Pub)
    (g : ℕ) (o : Own) (F₀ F₁ : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Mats Cb.Gl.E) : Prop where
  /-- the public facts on the layout -/
  ground : ∃ rd r pts, K4Ground h pc o.v rd r tl o.H o.hd o.hd2 pts o.funs D
  /-- the public numbers -/
  sizes : K4Sizes P o.v o.H o.hd o.hd2 D
  /-- the group -/
  grp : o.v.g = g
  /-- which hidden value each slot holds, behind "front" -/
  opened : Opened (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) Reading.gl
    (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P o D (cellsOf D (cellsAt o.v.y Mm))
  /-- the norms' identities at the cells -/
  idn : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm))
  /-- the selector's identity, extended over the positions, at the lookup's token point -/
  hot : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF)
  /-- the own claims of four sumchecks -/
  own : ∀ sh, ((Array.range (4 * P.y.NI)).mapM fun i => F₀.shown (o.H.tV.sEnd + i)) = some sh →
    OwnFront Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P o sh
  /-- the lookup's three claims -/
  look : ∀ pp, planesParts o.v o.H.fo = some pp →
    LookThree Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) o pp
  /-- the two slots and the two own claims of "back", behind "back" -/
  back : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    OpenedBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o ∧
      OwnBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o

/-- **THE FOURTEEN WORTHS AT ONE STATE.** CONDITIONAL: on every field of I. -/
theorem item_worths {h : Layer.Shape} {pc : List (List String)} {D : Dim} {tl : HTailF2} {P : Pub}
    {g : ℕ} {o : Own} {F₀ F₁ : Fork} {mask : ℕ → Cb.Gl.E} {Mm : Mats Cb.Gl.E}
    (I : ItemOpens h pc D tl P g o F₀ F₁ mask Mm) :
    (∀ sh pp,
      ((Array.range (4 * P.y.NI)).mapM fun i => F₀.shown (o.H.tV.sEnd + i)) = some sh →
      planesParts o.v o.H.fo = some pp →
      FrontWorth Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P g o sh pp) ∧
    ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
      BackWorth Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o := by
  obtain ⟨rd, r, pts, G⟩ := I.ground
  exact ⟨fun sh pp hsh hpp =>
      front_item G I.sizes Mm F₁ mask I.grp I.opened I.idn I.hot (I.own sh hsh) (I.look pp hpp),
    fun fs₂ F₂ hb => back_item Mm F₂ mask (I.back fs₂ F₂ hb).1 (I.back fs₂ F₂ hb).2⟩

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.item_worths
