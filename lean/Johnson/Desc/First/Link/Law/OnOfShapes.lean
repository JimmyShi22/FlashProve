-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OnOfShapes.lean (kind K10): K10's OWN CONDITION IN FRONT (`K10OnS`: the field hOn of `K10Heavy`, Johnson/Desc/First/Close/Law/K10Heavy.lean) AT ONE STATEMENT, AT THE GROUP THAT THE PROGRAMS HAVE AND THE LETTERS OF
`tied_of_shapes` (TiedOfShapes.lean beside this file): THE JOIN OF WHAT LIES IN FOUR PLACES. A structure and two theorems.

Why. hOn had four sources and no file that joined them. `k10OnS_of_order` (Close/Law/OnOfOrder.lean) has K10OnS from: hk · hh · front · tied · zl · hI · code. tied: `tied_of_shapes` from `ShapesOwes` (fifteen fields). hk · hh · zl · code:
four of the five comparisons of public
numbers (`five_in_front` | `five_of_facts`; the third of the five is not spent here).
Of ShapesOwes' fifteen, SEVEN FOLLOW FROM THE HINGE, THE ORDER AND THREE CLOSED FACTS (begunAt · ok · shapes · shapes0 · agrees · k · h); EIGHT ARE HANDED ON.

What is said.
  `OnLeft a`: **WHAT IS LEFT, BY NAME**: closed on public data: good (the group's own test) · agrees (`LayoutAgrees lo kb`) · kL (kLay lo kb = s.h + s.g) · h0 (s.h = 0) · apart (the numbering parts the members) · tie; at the state: plain · gens (the two
    counts) · seed · plan.
  `shapesOwes_of_left`: the statement is in order · THE HINGE (`ShapesAre` in front, at the plan's numbering) · OnLeft ⊢ `ShapesOwes` at every group Gr of the frame's and every layout lay of the begun statement, with Gb := begunGroup Gr. PAID INSIDE:
    begunAt · ok · shapes · shapes0 · agrees · k · h (and h0, apart handed on).
  `onS_of_left`: **front · the five (in `five_in_front`'s own end) · the order · the hinge · OnLeft ⊢ `K10OnS`.**

WHO PAYS WHAT IS LEFT, BY NAME (none is called here): agrees: `linksFull_layout` | `five_layout` · apart: `hinj_full` | `AtMg.hinge_inj` · plain | gens: `plain_of_held` | `gens_of_held` (CountsOfHeld.lean) · seed: `seed_field` · tie:
`tieAll_of` · plan: `plan_of_shapes` · front: `fa_front_same` from K10Heavy's hV | hCfX and A₀.on · good · kL · h0: closed: evaluated true at 25 links;
h0 closed (stage_h0); good, kL theorems at the written lists under named premises (good_cs, kL_of):
Johnson/Desc/First/Close/Law/StageClosed.lean.

Limits. AN IMPLICATION. At `tied_of_shapes`' letters (n · num · the names · pS · the reader of samples are that theorem's terms): that K10Heavy's letters at the constant are these is not shown here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.TiedOfShapes
import Johnson.Desc.First.Close.Law.OnOfOrder
import Johnson.Desc.First.Close.Law.ShapesBegun
import Johnson.Desc.First.Close.Law.LayoutOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop
open IOR Prob Run KObj OnBytes.Params OnBytes.Means Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)
open VerifiableInference.Desc.LinkJoin (numBy smpDrawn smpDrawn_seed pSseed esOf esOf_nodup esOf_all
  members_of_shapes inMain_of_shapes inKept_of_shapes inMask_of_shapes sampleFits_of_shapes)

attribute [local instance] Classical.propDecidable

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (seats : List (ℕ × ℕ)) (s : Sg) (e : ℕ)
  (kb : Fin lo.length → Bool)
  (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C)
  (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z)
  (keep : (sigOf cs lo).O → Prop) [DecidablePred keep]
  (pull : ((groupLayK cs lo s e kb hM hZ).Sh.Cin.J → GE) →
    (groupLayK cs lo s e kb hM hZ).G.C.J → GE)
  (nP nG : ℕ)

variable (fx : Fin (((groupLayK cs lo s e kb hM hZ).Sh.fold
    (SbV (groupLayK cs lo s e kb hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull)
    (ZV (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ)))).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo s e kb hM hZ).sizeB keep
    (SbV (groupLayK cs lo s e kb hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull)
    (ZV (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ)))).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW (groupLayK cs lo s e kb hM hZ).G ((groupLayK cs lo s e kb hM hZ).sizeB keep
    (SbV (groupLayK cs lo s e kb hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull)
    (ZV (groupLayK cs lo s e kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG)
      (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ)
        (esOf_all cs lo s e kb hM hZ)))).kp Wp)
  (L : List (BatFoldCaller GE)) {Pz : Type}
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : VerifiableInference.Desc.First.S × F.E.Str →
    (groupLayK cs lo s e kb hM hZ).Sh.par.Cw.nat.Str) (T₀ : Statement) (L₀ : GroupLayout)

/-- **WHAT IS LEFT OF K10's CONDITION IN FRONT, BY NAME.** -/
structure OnLeft (a : VerifiableInference.Desc.First.S × F.E.Str) : Prop where
  good : (groupLayK cs lo s e kb hM hZ).Good
  agrees : LayoutAgrees lo kb
  kL : kLay lo kb = s.h + s.g
  h0 : s.h = 0
  apart : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, numAt seats ⟨⟨lo, seat⟩, i⟩ = numAt seats ⟨⟨lo,
      seat⟩, j⟩ → i = j
  tie : ∀ i : Fin lo.length, memMain lo i → K1.Tie cs (lo.get i).1
  plain : ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (Gr.rows.filter (·.kind ==
      .plain)).toList.length = nP
  gens : ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (Gr.rows.filter (·.kind ==
      .generator)).toList.length = nG
  seed : ∀ i : Fin lo.length, memMain lo i → ∃ (ρ : (Fin (bitsZ cs (lo.get i).1) → GE) × GEˣ) (y :
      GE), K1.SeedIs cs (lo.get i).1 a.1.st (numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y
  plan : ∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → ∀ as D, pSseed cs lo (groupLayK cs
      lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀ (fun
      i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D = pSseed cs lo (groupLayK cs lo s e kb hM hZ) (namesOf
      cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) (begun (rdK a.1).2.2 (rdK
      a.1).2.1.group Gr) lay (fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) as D

/-- **ShapesOwes FROM THE ORDER, THE HINGE AND WHAT IS LEFT.** -/
theorem shapesOwes_of_left (a : VerifiableInference.Desc.First.S × F.E.Str) (Gr : Group) (lay :
    GroupLayout)
    (hG : (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr)
    (hl : (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay)
    (hI : InOrder (rdK a.1).2.2)
    (H : ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → ShapesAre (rdK a.1).2.2 Gr lo
        kb fun i => numAt seats ⟨⟨lo, seat⟩, i⟩)
    (O : OnLeft cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a) :
    ShapesOwes cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a Gr (begunGroup Gr) lay := by
  have hG' := begun_at (rdK a.1).2.1.group Gr hG
  have H' := shapesAre_begun (rdK a.1).2.1.group (H Gr hG)
  obtain ⟨L', h1, h2, -, -⟩ := layout_of_shapes hG' H' O.agrees
  obtain rfl : L' = lay := Option.some.inj (h1.symm.trans hl)
  exact ⟨O.good, hG', (hI.begun (rdK a.1).2.1.group Gr hG).groups (rdK a.1).2.1.group _ hG', H', H
      Gr hG, h2, O.apart, h2.1.trans O.kL, O.h0, h2.2.1.trans O.h0.symm, O.plain Gr hG, O.gens Gr
      hG, O.seed, O.tie, O.plan Gr L' hG hl⟩

/-- **K10's CONDITION IN FRONT, AT ONE STATEMENT.** -/
theorem onS_of_left (Pr : Par) (z : Pz) (a : VerifiableInference.Desc.First.S × F.E.Str)
    (front : ((Cb.Pv.Bat.inJ ((groupLayK cs lo s e kb hM hZ).sizeB keep (SbV (groupLayK cs lo s e kb
        hM hZ) (Fin nP ⊕ Fin nG)) (slV (groupLayK cs lo s e kb hM hZ) pull) (ZV (groupLayK cs lo s e
        kb hM hZ) (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb hM
        hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)))) A₀).keepE (groupLayK cs
        lo s e kb hM hZ).Sh.par.Cw.nat).on (faK10 G cs lo seat (groupLayK cs lo s e kb hM hZ)
        (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) keep pull (nP + (esOf cs
        lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb hM hZ) (esOf_nodup cs lo s e
        kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L (fun (a : Pz ×
        VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀ st₀ e₀ mW z a))
    (five : (planOf (entries Pr) (rdK a.1)).k = s.h + s.g ∧ (planOf (entries Pr) (rdK a.1)).h = s.h
        ∧ (∀ Gr lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → (begun (rdK a.1).2.2
        (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay → 2 ^ lay.logEll = s.C.l ∧ 2 ^
        lay.logEllZk = s.Z.l) ∧ ((rdK a.1).2.2.codes.mask.getD (planOf (entries Pr) (rdK
        a.1)).maskCode default).ell = s.Z.l)
    (hI : InOrder (rdK a.1).2.2)
    (H : ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr → ShapesAre (rdK a.1).2.2 Gr lo
        kb fun i => numAt seats ⟨⟨lo, seat⟩, i⟩)
    (O : OnLeft cs lo seat seats s e kb hM hZ nP nG T₀ L₀ a) :
    K10OnS (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo,
        seat⟩, i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s
        e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁
        L (pSseed cs lo (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt
        seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) Pr (faK10 G cs lo seat
        (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats ⟨⟨lo, seat⟩,
        i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs lo s e kb
        hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀ w₁ L
        (fun (a : Pz × VerifiableInference.Desc.First.S) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀
        st₀ e₀ mW z) a :=
  k10OnS_of_order (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt seats
      ⟨⟨lo, seat⟩, i⟩) keep pull (nP + (esOf cs lo s e kb hM hZ).length + nG) (numBy nP nG (esOf cs
      lo s e kb hM hZ) (esOf_nodup cs lo s e kb hM hZ) (esOf_all cs lo s e kb hM hZ)) fx A₀ bC bZ w₀
      w₁ L (pSseed cs lo (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ fun i => numAt
      seats ⟨⟨lo, seat⟩, i⟩) T₀ L₀ fun i => numAt seats ⟨⟨lo, seat⟩, i⟩) Pr _ a five.1 five.2.1
      front
    (fun Gr lay hG hl => tied_of_shapes G cs lo seat seats s e kb hM hZ keep pull nP nG fx A₀ bC bZ
        w₀ w₁ L σ₀ st₀ e₀ mW T₀ L₀ z a Gr (begunGroup Gr) lay hG hl (shapesOwes_of_left cs lo seat
        seats s e kb hM hZ nP nG T₀ L₀ a Gr lay hG hl hI H O))
    (fun Gr lay hG hl => le_of_eq (five.2.2.1 Gr lay hG hl).2.symm) hI five.2.2.2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.shapesOwes_of_left
#print axioms VerifiableInference.Desc.First.Close.onS_of_left
