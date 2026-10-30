-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/ViewAt.lean: THE VIEW: how a stretch of a file's written rounds is
read as the typed lookup's rounds, so that the flat view at which the typed verifier's out is
described is the reading of the written rounds themselves.

Cb/Pv/KeyLookup/Flat.lean reads and writes each typed round flat (RdR, RdS). The library's kit for
maps from written rounds to typed rounds (Fo.Peel.Rd, Rds, mapsT:
OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean, Peel/FoPeelMapsT.lean) takes a reader of each typed
round from plain data. This file makes the second of the first.

Main names:
  spOf, rdOf, rdsOf: a format as the kit's spec; a typed round's record as the kit's reader; a
    shape's.
  outs_view: the kit's reading back is the flat view.
  mapsOf A ds h: the maps from the written rounds ds to the shape of A. mapsOf_ok: they are as
    asked.
  view_maps: the flat view of the image of a written transcript is the view's rounds, read.
  flat_read: on rounds whose items are all elements, flatRV (Statement.lean) is that reading.
  lamS_out_at: THE TYPED LOOKUP's OUT AT THE IMAGE of a written transcript is lamRun at the view's
    rounds, read.

Limits. That the written rounds meet the typed lookup's formats (MeetsT, round by round) and hold no
answer to a sample is a premise.

-/
import Johnson.Desc.First.Look.KeyLaw.Statement
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelMapsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open Iop OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker
open _root_.Run (ckP)
open OnBytes.Model (Reading)
open Lk6 (Dat Pl)
open Lk6.Flat (Fm RdR RdS)
open Fo.Peel (Rd Rds outs mapsT MeetsT NoAns)

/-- A format as the kit's spec. -/
def spOf (f : Fm) : Tw.RSp := ⟨f.sent, f.drawn, f.nz⟩

/-- A typed round's record as the kit's reader. -/
def rdOf {r' : Round} (R : RdR GE r') : Rd r' (spOf R.fm) where
  fm := R.mkM
  g := R.mkC
  out := fun m c => (R.sent m, R.drawn c)
  inv := fun r h => by
    have e := R.inv r ((Fm.fits_iff R.fm r).2 h)
    exact Prod.ext e.1 e.2

/-- A shape's. -/
def rdsOf : {s : Iop.Shape} → (A : RdS GE s) → Rds s (A.fms.map spOf)
  | [], _ => ()
  | _ :: _, (a, A) => (rdOf a, rdsOf A)

/-- The kit's reading back is the flat view. -/
theorem outs_view : ∀ {s : Iop.Shape} (A : RdS GE s) (τ : Tr s),
    outs s (A.fms.map spOf) (rdsOf A) τ = A.view τ
  | [], _, _ => rfl
  | _ :: _, (a, A), (m, c, τ) => by
    show (a.sent m, a.drawn c) :: outs _ _ (rdsOf A) τ = (a.sent m, a.drawn c) :: A.view τ
    rw [outs_view A τ]

/-- **The maps from written rounds to a typed shape.** -/
def mapsOf {s : Iop.Shape} (A : RdS GE s) (ds : List RDT) (h : ds.length = (A.fms.map spOf).length)
    :
    Maps ds s :=
  mapsT ds s (A.fms.map spOf) (rdsOf A) h

theorem mapsOf_ok {s : Iop.Shape} (A : RdS GE s) (ds : List RDT)
    (hM : List.Forall₂ MeetsT ds (A.fms.map spOf)) : (mapsOf A ds hM.length_eq).OK :=
  Fo.Peel.mapsT_ok ds s _ (rdsOf A) hM

/-- **The flat view of the image of a written transcript is the view's rounds, read.** -/
theorem view_maps {s : Iop.Shape} (A : RdS GE s) (ds : List RDT)
    (hM : List.Forall₂ MeetsT ds (A.fms.map spOf)) (hA : ∀ d ∈ ds, NoAns d.items)
    (τ : Tr (uLT (ckP .two) ds)) :
    A.view ((mapsOf A ds hM.length_eq).view τ) =
      (rvT (ckP .two) ds τ).map (Fo.rdRV Reading.gl) := by
  rw [← outs_view, Fo.Peel.flWsT_view ds τ hA]
  exact Fo.Peel.mapsT_read ds s _ (rdsOf A) hM τ

/-- A message whose items are all elements. -/
theorem elems_filter : ∀ (vs : List Fmt.ItemValue) (l : List E), First.Tape.elemsOf vs = some l →
    vs.filterMap PscRun.eOf = l
  | [], l, h => by
    cases h
    rfl
  | .e x :: vs, l, h => by
    have h' : (First.Tape.elemsOf vs).map (E.ofTriple x :: ·) = some l := h
    cases hv : First.Tape.elemsOf vs with
    | none => rw [hv] at h'; cases h'
    | some l' =>
      rw [hv] at h'
      cases h'
      show E.ofTriple x :: vs.filterMap PscRun.eOf = _
      rw [elems_filter vs l' hv]
  | .root _ :: _, _, h => by cases h
  | .answer _ :: _, _, h => by cases h

/-- **On rounds whose items are all elements, flatRV is the library's reading.** -/
theorem flat_read (rs : List Fmt.RoundView) (h : ∀ r ∈ rs, (First.Tape.elemsOf r.vals).isSome) :
    flatRV rs = rs.map (Fo.rdRV Reading.gl) := by
  unfold flatRV
  refine List.map_congr_left fun r hr => ?_
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (h r hr)
  show (((First.Tape.elemsOf r.vals).getD []).map readE, _) =
    ((r.vals.filterMap PscRun.eOf).map readE, (r.drawn.elems.map E.ofTriple).map readE)
  rw [hl, elems_filter _ _ hl, List.map_map]
  rfl

/-- **The typed lookup's out at the image of a written transcript.** -/
theorem lamS_out_at (A : Dat GE) (P : Pl A) (Ex : ExtSpec) (ds : List RDT)
    (hM : List.Forall₂ MeetsT ds ((Lk6.lamS_runs A P Ex).rd.fms.map spOf))
    (hA : ∀ d ∈ ds, NoAns d.items) (st : A.St) (y : Ex.Str) (τ : Tr (uLT (ckP .two) ds)) :
    (A.lamS P Ex).R.out st y ((mapsOf (Lk6.lamS_runs A P Ex).rd ds hM.length_eq).view τ) =
      some (A.lamRun P st ((rvT (ckP .two) ds τ).map (Fo.rdRV Reading.gl))) := by
  rw [Lk6.lamS_out, view_maps _ ds hM hA τ]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.mapsOf_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.view_maps
#print axioms VerifiableInference.Desc.K3.KeyLaw.flat_read
#print axioms VerifiableInference.Desc.K3.KeyLaw.lamS_out_at
