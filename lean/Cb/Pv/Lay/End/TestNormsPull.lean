-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TestNormsPull.lean: norms_pull applied at closed letters, with every premise shown.

norms_pull (Cb/Pv/Lay/End/NormsA.lean) has many premises. This file gives closed letters at which
all of them hold together, and applies the theorem. These are theorems, not runs.

The letters. The field is the integers modulo 97. Sizes: the library's reference sizes with 2
positions, 2 layers (4 norms, 1 routed layer), a stream of width 2 and 2 experts; one block of 2
features (b = 0, s = 1, B = 1). The scales are the library's reference scales. There is one early
entry, and it is 1: every mask entry is that entry, and a cell is a made-up number times that entry.
In every ledger byte 59 is 1, byte 64 is 2 and the others are 0; the first selector's entry is 1; a
limb of the stream is made up. The late entries are those of Cb/Pv/Lay/End/NormsLay.lean. The token
point, the drawn elements and the coefficients are made up. The points inside the two outputs are
any: they are letters of the theorems. Scalars and outputs are those of
Cb/Pv/Lay/End/NormsMeetAt.lean, with product 4 raised and product 5 lowered by 6.

Main theorem: toy_pull (norms_pull applied; inside its proof every premise is shown).

Limits. The points inside the two outputs are letters; the type of such points has a member (ppt0 in
Cb/Pv/Lay/End/TestGated.lean). There is one block, so the claims' sums over blocks are idle. Every
mask entry is the one entry, so a swap of two mask names would pass. The bytes are the same for
every norm and position.


-/
import Mathlib.Data.ZMod.Basic
import Cb.Pv.Lay.End.NormsLay
import Cb.Pv.Lay.End.NormsMeetAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End.TestPull

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr led val d10 lDd)
open Inst.Model.Ledger (l1 h1 sig rr rq)
open Blocks (ext)

instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-- The field. -/
abbrev K : Type := ZMod 97

/-- The sizes. -/
def Dt : Dim := { Dim.ref with P := { Dim.ref.P with d := 2, nexp := 2 }, lT := 1, lL := 1 }

/-- The bytes of every ledger. -/
def byt (n : ℕ) : K := if n = 59 then 1 else if n = 64 then 2 else 0

/-- The cells at the entry 1. -/
def tt : Cell → K := fun c =>
  match c.X with
  | .D => byt c.j - 128
  | .sel => if c.j = 0 then 1 else 0
  | _ => ((1 + c.k + 2 * c.inst + 3 * c.j + c.i : ℕ) : K)

/-- The letters. -/
def Pt : NormPar0 K where
  D := Dt
  J := Unit
  rd := fun m c => tt c * m ()
  two := by decide
  eS := Equiv.refl _
  mkS := fun _ _ => ()
  wS := fun _ => ()
  cS := fun _ => ()
  mkP := fun _ => ()
  rP := ()
  wP := fun _ => ()
  cP := fun _ => ()

instance : DecidableEq Pt.J := inferInstanceAs (DecidableEq Unit)

/-- The early entry. -/
def mt : Pt.J → K := fun _ => 1

theorem hrd_t (a b : K) (m m' : Pt.J → K) (c : Cell) :
    Pt.rd (fun j => a * m j + b * m' j) c = a * Pt.rd m c + b * Pt.rd m' c := by
  show tt c * (a * m () + b * m' ()) = a * (tt c * m ()) + b * (tt c * m' ())
  ring

/-- The token point. -/
def pt0 : Fin Pt.D.lT → K := fun _ => 3

/-- The extensions of the bytes are the bytes. -/
theorem dgs_t (ν : ℕ) : Dgs Pt mt pt0 ν = byt := by
  funext n
  unfold Dgs
  have e : (fun i => led (Pt.rd mt) ν i n) = fun _ => byt n := by
    funext i
    rw [led_cell]
    show (byt n - 128) * 1 + 128 = byt n
    ring
  rw [e, Blocks.ext_const]

theorem h12_t (ν : ℕ) :
    l1 (Dgs Pt mt pt0 ν) + h1 (Dgs Pt mt pt0 ν) - 2 * sig (Dgs Pt mt pt0 ν) = 0 := by
  rw [dgs_t]
  decide

theorem h16_t (ν : ℕ) :
    rr (Dgs Pt mt pt0 ν) + rq (Dgs Pt mt pt0 ν) - sig (Dgs Pt mt pt0 ν) + 1 = 0 := by
  rw [dgs_t]
  decide

theorem hot_t (zt : ℕ → K) (l : ℕ) : ext Pt.D.lT (d10 Pt.D (Pt.rd mt) l) zt = 0 := by
  have e : d10 Pt.D (Pt.rd mt) l = fun _ => 0 := by
    funext i
    unfold Inst.Model.FFSeg.d10
    show ∑ x ∈ range 2, val (Pt.rd mt) .sel l x i - 1 = 0
    rw [sum_range_succ, sum_range_one, sel_cell, sel_cell]
    show (1 : K) * 1 + 0 * 1 - 1 = 0
    ring
  rw [e, Blocks.ext_const]

/-- An entry that stands for the names out of range. -/
def d0 : NormsJ2 Pt.D.nNu 1 Pt.D.ne Pt.D.nx :=
  .inr (.inl (⟨0, by decide⟩, ⟨0, by decide⟩))

variable (pt1 : PPt Pt.sq.R.L.toSum.T.par.fmt) (pt2 : PPt Pt.rows.tok.toSum.T.par.fmt)

/-- norms_pull applied: all its premises are met together. -/
theorem toy_pull :
    Pt.sq.B ((pt0, fun q => sWAt Pt mt pt0 (finProdFinEquiv q)), 2) mt ∧
      Pt.sq.R.L.toSum.T.par.OutHolds (o1At Pt mt pt0 2 (fun _ => 7) 4 pt1) mt ∧
      (Pt.rows.led pt0 mt fun n => sPAt Pt mt pt0 6 n - mt (Pt.mkP n)) ∧
      Pt.rows.tie ((pt0, sPAt Pt mt pt0 6), 3) (zAt Pt mt pt0 6 3) mt ∧
      Pt.rows.tok.toSum.T.par.OutHolds (o2At Pt mt pt0 6 3 5 pt2) mt := by
  have h := norms_meets Pt (normsLay d0) hrd_t mt pt0 2 3 6 4 5 (fun _ => 7) pt1 pt2
    (fun _ => 11) 0 1 1 (by decide) (by decide) (by decide)
    (fun _ _ _ a1 a2 a3 => ⟨a1, a2, a3⟩) (fun _ _ a1 a2 => ⟨a1, a2⟩) (fun _ _ a1 a2 => ⟨a1, a2⟩)
    (fun _ _ a1 a2 => ⟨a1, a2⟩) (fun ν _ => h12_t ν) (fun ν _ => h16_t ν) (fun l _ => hot_t _ l)
  exact norms_pull Pt hrd_t (normsLay d0) id _ pt0 _ 2 _ _ 3 _ _ (fun _ => 11) mt 0 1 1
    (by decide) (by decide) (by decide) h.1 (fun _ _ => rfl)
    (fun _ _ _ a1 a2 a3 => ⟨a1, a2, a3⟩) (fun _ _ a1 a2 => ⟨a1, a2⟩) (fun _ _ a1 a2 => ⟨a1, a2⟩)
    (fun _ _ a1 a2 => ⟨a1, a2⟩) h.2

end Cb.Pv.Lay.End.TestPull

#print axioms Cb.Pv.Lay.End.TestPull.toy_pull
#print axioms Cb.Pv.Lay.End.norms_pull
#print axioms Cb.Pv.Lay.End.norms_pull_iff
#print axioms Cb.Pv.Lay.End.norms_meets
#print axioms Cb.Pv.Lay.End.tables_true
#print axioms Cb.Pv.Lay.End.norms_cl_iff
