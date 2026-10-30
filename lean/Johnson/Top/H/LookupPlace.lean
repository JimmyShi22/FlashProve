-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupPlace.lean: the law at a lookup's place, at the kind's own block over the
caller's signature.

OnBytes/Tie/Pv/Lookup/Peel/FoPeelPlace.lean states the law at a lookup's place for the typed
lookup at the base. A written
file's rows hold the block lifted over the caller's signature (Johnson/Top/Kind.lean:
BaseKind.toKind; Johnson/Top/H/LookupC.lean, LookupCRows.lean). The lift keeps the rounds and hands
the signature's samples and oracles on unchanged. This file states the law for that block, written
out in the form: for every written transcript τ and every list rest: τ passes its tests of work →
the rounds still to be taken before the place are τ's reading and then rest → τ has an image, the
block's verifier puts out a' on it, and rest is still to be taken behind the place.

What the file states.
 - keep_out: a verifier that keeps further state and further oracles puts out what the verifier
   beneath puts out, with both handed on: stated where the verifier beneath puts out a statement.
 - lookCarryK c ds hl: Fo.Peel.lookCarryT, typed at the shape of the block of kLookupCN at the
   caller c. (The two shapes are one by definition.)
 - look_place_top: the law at the block of kLookupCN [c] at c: p := cx.ch.left, p' := cx'.ch.left
   for a run of Forest.pad from cx to cx'; V := rvT (ckP .two) ds; F := lookCarryK; a : the
   statement over the signature before the place; a' := the typed statement x that the base verifier
   puts out, from a's state and base oracles (a.1.1, a.2.1), at Fo.lookImgP c.h c.L c.Ex ds
   cx.ch.left, with a's samples and oracles.
 - look_place_topC: the same at the block of kLookupC [c] (the two kinds have one reduction).

Under: as Fo.look_place. Written out: c.h is the record of public numbers that the byte-level
verifier's own routines make of the calls (ShapeOf); Fk's arrays have their sizes (Sized); cx is on
a view with no message open (Clean); each written round meets its place in the lookup's list of
rounds (MeetsT); no item of a message is an answer to a sample (NoAns).

Limits. Those of FoPeelPlace.lean, but for the lift. The form is written out; no file that names the
form is imported. That the context at the door is as asked is a premise. Nothing here ties ds to a
description's rounds at the place: of ds the statement asks MeetsT and NoAns alone. The two
conditions on τ and rest (τ passes its tests of work; cx.ch.left = rvT (ckP .two) ds τ ++ rest) are
shown here at no run.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.LookupCRows
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp TWhole OnBytes.Flat Run
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Maker Fo Fo.Peel

/-- A verifier that keeps further state and oracles. -/
theorem keep_out {Xi Xo Z : Type} {Ei Eo F : ExtSpec} (R : IOR Xi Ei Xo Eo) (st : Xi)
    (y : Ei.Str) (z : Z) (e : F.Str) (τ : Tr R.shape) (x : Xo) (y' : Eo.Str)
    (h : R.red.out (st, y) τ = some (x, y')) :
    (R.keep Z F).red.out ((st, z), (y, e)) τ = some ((x, z), (y', e)) := by
  obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 h
  refine IOR.red_out_eq_some.2 ⟨?_, ?_⟩
  · show (R.out st y τ).map (fun xo => (xo, z)) = some (x, z)
    have h1' : R.out st y τ = some x := h1
    rw [h1']
    rfl
  · show (y', e) = (R.imp y τ, e)
    have h2' : y' = R.imp y τ := h2
    rw [h2']

section
variable (c : LookupCCaller) (ds : List RDT)

/-- The maps of the lookup's written rounds, at the shape of the kind's block. -/
noncomputable def lookCarryK (hl : ds.length = (specF c.h).length) :
    CarryS (uLT (ckP .two) ds) ((kLookupCN [c]).toKind.block c).R.shape :=
  lookCarryT c.h c.L c.Ex ds hl

/-- **The law at a lookup's place, at the kind's block.** -/
theorem look_place_top {calls : Array Call} {pub : Array Nat} {lid : ℕ} {Fk F' : Fork}
    {cx cx' : Ctx} {g : Forest.Heard}
    (hr : Forest.pad calls pub lid Fk cx = .ok ((g, F'), cx'))
    (hS : ShapeOf calls pub lid c.h) (hF : Sized Fk) (hc : Clean cx)
    (hM : List.Forall₂ MeetsT ds (specF c.h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (a : (c.St₀ × c.Sg.Smp) × (c.Ex.prod c.Sg.ext).Str)
    (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (hx : (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.red.out (a.1.1, a.2.1)
      (lookImgP c.h c.L c.Ex ds cx.ch.left) = some (x, a.2.1)) :
    ∀ (τ : Tr (uLT (ckP .two) ds)) (rest : List Fmt.RoundView),
      passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = true →
      cx.ch.left = rvT (ckP .two) ds τ ++ rest →
      ∃ τ', (lookCarryK c ds hM.length_eq).tr τ = some τ' ∧
        ((kLookupCN [c]).toKind.block c).R.red.out a τ' = some ((x, a.1.2), a.2) ∧
        cx'.ch.left = rest := by
  intro τ rest hp hl
  obtain ⟨τ', h1, h2, h3⟩ :=
    look_place c.h c.L c.Ex ds hr hS hF hc hM hA (a.1.1, a.2.1) (x, a.2.1) hx τ rest hp hl
  exact ⟨τ', h1, keep_out _ a.1.1 a.2.1 a.1.2 a.2.2 τ' x a.2.1 h2, h3⟩

/-- The same at the kind whose joint behind the block does not say the number of rows. -/
theorem look_place_topC {calls : Array Call} {pub : Array Nat} {lid : ℕ} {Fk F' : Fork}
    {cx cx' : Ctx} {g : Forest.Heard}
    (hr : Forest.pad calls pub lid Fk cx = .ok ((g, F'), cx'))
    (hS : ShapeOf calls pub lid c.h) (hF : Sized Fk) (hc : Clean cx)
    (hM : List.Forall₂ MeetsT ds (specF c.h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (a : (c.St₀ × c.Sg.Smp) × (c.Ex.prod c.Sg.ext).Str)
    (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (hx : (forB Cb.Gl.E c.h c.L V₀ V₀C (Ex := c.Ex)).R.red.out (a.1.1, a.2.1)
      (lookImgP c.h c.L c.Ex ds cx.ch.left) = some (x, a.2.1)) :
    ∀ (τ : Tr (uLT (ckP .two) ds)) (rest : List Fmt.RoundView),
      passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = true →
      cx.ch.left = rvT (ckP .two) ds τ ++ rest →
      ∃ τ', (lookCarryK c ds hM.length_eq).tr τ = some τ' ∧
        ((kLookupC [c]).toKind.block c).R.red.out a τ' = some ((x, a.1.2), a.2) ∧
        cx'.ch.left = rest :=
  look_place_top c ds hr hS hF hc hM hA a x hx

end

#print axioms VerifiableInference.OnPublicFiles.keep_out
#print axioms VerifiableInference.OnPublicFiles.look_place_top
#print axioms VerifiableInference.OnPublicFiles.look_place_topC

end VerifiableInference.OnPublicFiles
