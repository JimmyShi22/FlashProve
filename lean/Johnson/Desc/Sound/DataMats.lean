-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DataMats.lean: THE MATRICES UNPACKED FROM THE DATA's SYMBOLS: three definitions, free of any kind of sub-protocol: cut, to the letter, out of Johnson/Desc/First/Att/K05DataMats.lean, so that every kind's arm of the one stated function
can be made of one term.
  dataByAddr arrayOf Dt: the data (the arrays' cells and the segment's mask row: Bound), read by address: a mask entry is the mask row's; cell (t, r, c) is cell (r, c) of the array that the list of names arrayOf names at t; 0 WHERE IT NAMES NONE.
  symOfData tl arrayOf Dt: the committed symbols, off the data: symbol (matrix μ, row of symbols i', column c) is the data's cell at the matrix's symbol array tl.gtTree.getD μ 0.
  matsOfData tl arrayOf Dt: the matrices, off the data: a cell is the one unpacking (cellValS, Cb/Pv/Tail/InLink.lean) of these symbols; 0 outside the sizes.
What they need: Bound and GQ (Johnson/Desc/Sound/FormsQ.lean) · cellJ and szOf (Johnson/Desc/First/Look/K3CallerAtt.lean) · Syms and cellValS (Cb/Pv/Tail/InLink.lean) · Addr (OnBytes/Tie/Pv/Led/LedJoint.lean) and Mats (Johnson/Road/FormsKeysMat.lean).
No theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Road.FormsKeysMat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight (as in the file out of which the three are cut) -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)
open Cb.Pv.Tail (Syms cellValS)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.First.Look (cellJ szOf)

/-- The data, read by address. -/
def dataByAddr (arrayOf : Array (ℕ × String)) (Dt : Bound GQ) : Addr → GQ
  | .mask j => Dt.mask j
  | .cell t r c =>
    match arrayOf[t]? with
    | some b => Dt.cell b.1 b.2 r c
    | none => 0

/-- The committed symbols, off the data. -/
def symOfData (tl : HTailF2) (arrayOf : Array (ℕ × String)) (Dt : Bound GQ) : Syms GQ (szOf tl) :=
  fun μ i' c => dataByAddr arrayOf Dt (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)

/-- **The matrices, off the data.** -/
noncomputable def matsOfData (tl : HTailF2) (arrayOf : Array (ℕ × String)) (Dt : Bound GQ) :
    OnBytes.Road.Mats GQ := fun a r c =>
  match cellJ (szOf tl) a r c with
  | some j => cellValS (symOfData tl arrayOf Dt) j
  | none => 0

end VerifiableInference.Desc.Sound
