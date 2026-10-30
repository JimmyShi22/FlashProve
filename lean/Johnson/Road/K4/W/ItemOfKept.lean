-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/ItemOfKept.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: every field of ItemSlots is a hypothesis. That the
fields can hold together: no example is known. Nothing on soundness, on completeness or on any other
property. No property is claimed.

Behind an accepting decision of the layers' own rounds (sub-protocol K4), three of the nine fields
of `ItemOpens` (W/Item.lean), the public ones, follow from the nine public facts K4Plan on the plan.
Six fields stay: `ItemSlots`.

  `ItemSlots h D tl P o F₀ F₁ mask Mm`   the six fields of ItemOpens that speak of a world or of the
      cells.
  `plan_tokens`, `sizes_tokens`   K4Plan and K4Sizes do not read the request's tokens.
  `item_of_kept`   ItemOpens from KeptAtS, K4Plan and ItemSlots.
-/
import Johnson.Road.K4.W.Item
import Johnson.Road.K4.W.SizesOfHear
import Johnson.Road.K4.InT.FormsInTOwn
import Johnson.Desc.First.K4.SeatS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard Pub Own)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par seatS planesParts formsBack)
open OnBytes.Road.K4.InT (kept_open)
open VerifiableInference.Desc.First (S)

/-- **The fields of ItemOpens that speak of a world.** This defines a hypothesis; the definition
claims nothing. -/
structure ItemSlots (h : Layer.Shape) (D : Dim) (tl : HTailF2) (P : Pub) (o : Own) (F₀ F₁ : Fork)
    (mask : ℕ → Cb.Gl.E) (Mm : Mats Cb.Gl.E) : Prop where
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

/-- K4Plan does not read the request's tokens. -/
theorem plan_tokens {hS : Layer.Shape} {pc : List (List String)} {P : Pub} {g : ℕ} {tl : HTailF2}
    {D : Dim} (A : K4Plan hS pc P g tl D) (tk : Array ℕ) :
    K4Plan hS pc { P with tokv := tk } g tl D :=
  { lay := A.lay
    sw := A.sw
    scales := A.scales
    grp := A.grp
    reads := A.reads
    tails := A.tails
    mats := A.mats
    NM := A.NM
    sized := A.sized }

/-- K4Sizes does not read the request's tokens. -/
theorem sizes_tokens {P : Pub} {tk : Array ℕ} {v : Env} {H : Heard} {hd : Level}
    {hd2 : Option Level} {D : Dim} (Z : K4Sizes { P with tokv := tk } v H hd hd2 D) :
    K4Sizes P v H hd hd2 D :=
  { y := Z.y
    NI := Z.NI
    la := Z.la
    Pd := Z.Pd
    lsPd := Z.lsPd
    NIle := Z.NIle
    blocks := Z.blocks
    wpl := Z.wpl
    lsF := Z.lsF
    lsFe := Z.lsFe
    Lam := Z.Lam
    f := Z.f
    Pf := Z.Pf
    LamM := Z.LamM
    fe := Z.fe
    Dfe := Z.Dfe
    hd := Z.hd
    hd2 := Z.hd2 }

/-- **ItemOpens behind an accepting decision.** CONDITIONAL: on K, A and every field of Sl. -/
theorem item_of_kept {p : Par} {s s' : S} (K : KeptAtS p s s') {h : Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan h pc p.P p.g tl D) {o : Own}
    (ho : seatS.own s' = some o) {F₀ F₁ : Fork} {mask : ℕ → Cb.Gl.E} {Mm : Mats Cb.Gl.E}
    (Sl : ItemSlots h D tl p.P o F₀ F₁ mask Mm) :
    ItemOpens h pc D tl p.P p.g o F₀ F₁ mask Mm := by
  obtain ⟨a, a', fo, o', G, t, u, _, _, ha', _, eo, _, _, hh⟩ := kept_open K
  have hown : seatS.own s' = some o' := by
    show (match s'.here with | .lay a => a.own | _ => none) = _
    rw [ha']
    exact eo
  obtain rfl : o' = o := Option.some.inj (hown.symm.trans ho)
  have A' := plan_tokens A s.tokv
  obtain ⟨vg, _, r, pts, Gr⟩ := ground_of_hear hh A'
  exact
    { ground := ⟨_, r, pts, Gr⟩
      sizes := sizes_tokens (sizes_of_hear hh A')
      grp := vg
      opened := Sl.opened
      idn := Sl.idn
      hot := Sl.hot
      own := Sl.own
      look := Sl.look
      back := Sl.back }

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.plan_tokens
#print axioms OnBytes.Road.K4.W.sizes_tokens
#print axioms OnBytes.Road.K4.W.item_of_kept
