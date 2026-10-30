-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPass.lean: a key on the cells that are read in the verifier's matrices lies
in its table exactly if the key of the library's relation does.

The library's field relation of a feed-forward segment (trace in Inst/Model/FF/Trace.lean) asks,
over a prime field, that every key be an entry of its table. The proofs in Cm/TargetSegFF.lean
speak of keys over a larger field, at casts of integer matrices, and pass from one to the
other by two theorems, key_pass and key_mem_iff (Cm/TargetSegFFAffPass.lean), stated at the
library's own dictionary from names of cells to places in its matrices. This file states their
twins at the dictionary of these files: the cells that the verifier's rule reads in the list of
matrices of a layer sub-proof (cellsOf and cellsAt in Johnson/Road/FormsKeysFits.lean and
Johnson/Road/FormsKeysMat.lean).

What is compared with what. On the left the library's key, and key vector, over a field EE that is
an algebra over the prime field Cb.Gl.F, on cells named by these files' dictionary in integer
matrices Mz, and on the weights that the library's layout reads in an integer index matrix Wi, both
carried into EE. On the right the key of the library's relation over Cb.Gl.F at a trace t' on the
valid names, in the letters of trace and of Cm.TP.CondL.ffKey (Cm/TargetPRel.lean). No function of
the verifier stands in a statement but through cellsAt, which reads the layout's numbers.

Main theorems: key_pass_port, key_mem_iff_port; keyVecs_mem_iff (all entries of the eight key
vectors below their lengths lie in their calls' tables exactly if the relation's clause on the keys
holds at t'); cells_cast, rd_agrees_port, rows_call, pad_call.

At which sizes, tables and scales. The sizes are DF, which is the library's Dim.ref: the reference
sizes alone. The tables tb, the first layer L0 and the table of scales scl are free, and the same
on both sides. The condition Cm.TP.CondL.ffKey has tbRef, L0 = 4 g and the scales SFK κ nf g. That
the table of scales under which the theorems of these files stand (sclOf in
Johnson/Road/FormsKeysFits.lean) is that one is not shown here, nor that the first layer g Lam of a
group is 4 g.

The hypotheses, and that they can be met.
 - ht: t' holds the integer cells at the valid names. Met by taking that for t'.
 - the ranges l < nl, present s l, x < len, i < T: those of the relation's names of keys. Nothing
   is asked of y, Mz or Wi.

What is not claimed. That the entries of the matrices of a run are casts of integers is not shown;
nor that the key vectors' entries lie in the tables, which is the lookup's matter. The relation's
two other clauses (the cells' ranges, the identities) are not touched. The program does not import
this file.
-/
import Johnson.Road.FormsKeysFits
import Johnson.Road.FormsKeysMat
import Cm.TargetSegFF
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay)
open Inst.Model (Scl Tables Lut Mat ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Cell Fam key keyVec layerR rd castT lut lutSet call len present famAt lJ aC
  pos keyIdx KeyName trace)

variable [scl : Scl] {EE : Type} [Field EE] [Algebra Cb.Gl.F EE]

/-! ## The cells -/

omit scl [Algebra Cb.Gl.F EE] in
/-- The cells that are read in integer matrices carried into a ring are the integer cells, carried
into the ring. -/
theorem cells_cast (y : Lay) (Mz : Mats ℤ) :
    cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE))) =
      (castT (cellsOf DF (cellsAt y Mz)) : Cell → EE) := rfl

section Pass

variable (y : Lay) (Mz : Mats ℤ) (Wi : Mat) (t' : {c : Cell // c.Valid DF} → ℤ)
  (ht : ∀ c, t' c = cellsOf DF (cellsAt y Mz) c.val) (tb : Tables) (L0 : ℕ)

include ht

omit scl in
/-- A trace on the valid names that holds the integer cells agrees with them on the valid names. -/
theorem rd_agrees_port :
    ∀ c : Cell, c.Valid DF → cellsOf DF (cellsAt y Mz) c = (rd DF t' : Cell → ℤ) c := fun c hc => by
  unfold Inst.Model.FFSeg.rd
  rw [dif_pos hc, ht ⟨c, hc⟩]
  exact (Int.cast_id).symm

/-- The keys. A key of the library over EE, on the cells that the verifier's rule reads in integer
matrices carried into EE and on the weights that the library's layout reads in an integer index
matrix carried into EE, is the image of the key of the library's relation over the prime field, at
the trace t' and the same index matrix. The twin of key_pass (Cm/TargetSegFFAffPass.lean), which is
stated at the library's own dictionary of cells. -/
theorem key_pass_port {s : Fam} {l x i : ℕ} (hl : l < DF.nl) (hs : present s l = true)
    (hx : x < len DF s) (hi : i < DF.T) :
    key DF (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE)))) tb L0
        (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (L0 + l)) s l x i =
      algebraMap Cb.Gl.F EE
        (key DF (rd DF t') tb L0
          (fun l => layerR ppref kRef (Cm.TP.castW Cb.Gl.p Wi) (L0 + l)) s l x i) := by
  rw [cells_cast, Inst.Model.FFSeg.rd_cast]
  simp only [Inst.Model.FFSeg.Cast.layerCast']
  rw [Inst.Model.FFSeg.key_cast, Inst.Model.FFSeg.key_cast, map_intCast,
    Inst.Model.FFSeg.key_congr (rd_agrees_port y Mz t' ht) rfl tb L0 _ hl hs hx hi]

/-- The key over EE is the image of an entry of the table exactly if the relation's key is an entry
of the table. The twin of key_mem_iff. -/
theorem key_mem_iff_port {L : Lut} {T : ℕ} (hL : L.rows = 2 ^ T) {s : Fam} {l x i : ℕ}
    (hl : l < DF.nl) (hs : present s l = true) (hx : x < len DF s) (hi : i < DF.T) :
    (∃ u ∈ (Cm.Seg.tabOf L T : Cb.Tab Cb.Gl.F).set,
      key DF (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE)))) tb L0
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (L0 + l)) s l x i =
        algebraMap Cb.Gl.F EE u) ↔
    key DF (rd DF t') tb L0
        (fun l => layerR ppref kRef (Cm.TP.castW Cb.Gl.p Wi) (L0 + l)) s l x i ∈
      (lutSet L : Set Cb.Gl.F) := by
  rw [key_pass_port y Mz Wi t' ht tb L0 hl hs hx hi]
  exact Cm.Seg.TS.mem_image_iff hL _

/-! ## The key vectors -/

omit ht scl in
/-- log2 of the number of rows of a call's table. -/
theorem rows_call (c : Fin 8) : (lut tb c).rows = 2 ^ (if c = 3 then 8 else 16) := by
  fin_cases c <;> rfl

omit ht in
/-- The padding value of a call's table is an entry of the table. From the library's pad_mem
(Cm/TargetSegFF.lean), which is stated family by family. -/
theorem pad_call (c : Fin 8) :
    (((lut tb c).pad : ℤ) : Cb.Gl.F) ∈ (lutSet (lut tb c) : Set Cb.Gl.F) := by
  have hc : ∃ s : Fam, call s = c := by
    fin_cases c
    exacts [⟨.G, rfl⟩, ⟨.N1, rfl⟩, ⟨.QK, rfl⟩, ⟨.GH, rfl⟩, ⟨.CN1, rfl⟩, ⟨.MR, rfl⟩, ⟨.F, rfl⟩,
      ⟨.UT, rfl⟩]
  obtain ⟨s, rfl⟩ := hc
  exact Cm.Seg.TS.pad_mem tb s

/-- All entries of the eight key vectors on the verifier's cells, below the vectors' lengths, are
images of entries of their calls' tables exactly if every key of the library's relation at the trace
t' is an entry of its table: the clause on the keys of the part of the field relation that belongs
to the segment (trace in Inst/Model/FF/Trace.lean), over the prime field. -/
theorem keyVecs_mem_iff (first : Bool) (tok : ℕ → ℕ) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut tb c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec DF (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE)))) tb L0
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (L0 + l)) c X =
          algebraMap Cb.Gl.F EE u) ↔
    ∀ q, (trace DF tb kRef L0 first Cb.Gl.F).key tok (Cm.TP.castW Cb.Gl.p Wi) t' q ∈
      (trace DF tb kRef L0 first Cb.Gl.F).table q := by
  constructor
  · rintro H ⟨⟨s, l, x, i⟩, hl, hs, hx, hi⟩
    have hX : keyIdx DF (call s) l (pos DF s x) i < 2 ^ aC DF (call s) := by
      have e : 2 ^ aC DF (call s) = DF.nl * 2 ^ lJ DF (call s) * DF.T := by
        show 2 ^ (DF.lL + lJ DF (call s) + DF.lT) = 2 ^ DF.lL * 2 ^ lJ DF (call s) * 2 ^ DF.lT
        rw [pow_add, pow_add]
      rw [e]
      exact Inst.Model.FFSeg.IndexFacts.mr_lt
        (Inst.Model.FFSeg.IndexFacts.mr_lt hl (Inst.Model.FFSeg.IndexFacts.pos_lt DF hx)) hi
    have h1 := H (call s) _ hX
    rw [Inst.Model.FFSeg.IndexFacts.keyVecAt EE DF _ tb L0 _ s l x i hx hi hs] at h1
    exact (key_mem_iff_port y Mz Wi t' ht tb L0 (rows_call tb (call s)) hl hs hx hi).mp h1
  · intro H c X hX
    have hT : 0 < DF.T := Nat.two_pow_pos _
    have hi : X % DF.T < DF.T := Nat.mod_lt _ hT
    have hl : X / DF.T / 2 ^ lJ DF c < DF.nl := by
      have e : 2 ^ aC DF c = DF.nl * 2 ^ lJ DF c * DF.T := by
        show 2 ^ (DF.lL + lJ DF c + DF.lT) = 2 ^ DF.lL * 2 ^ lJ DF c * 2 ^ DF.lT
        rw [pow_add, pow_add]
      rw [e] at hX
      rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hT (Nat.two_pow_pos _))]
      calc X < DF.nl * 2 ^ lJ DF c * DF.T := hX
        _ = DF.nl * (DF.T * 2 ^ lJ DF c) := by ring
    have hp : ∃ u ∈ (Cm.Seg.tabOf (lut tb c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        (((lut tb c).pad : ℤ) : EE) = algebraMap Cb.Gl.F EE u :=
      ⟨_, (Cm.Seg.mem_tabOf (rows_call tb c) _).2 (pad_call tb c), (map_intCast _ _).symm⟩
    unfold keyVec
    cases hfa : famAt DF c (X / DF.T % 2 ^ lJ DF c) with
    | none => exact hp
    | some sx =>
      obtain ⟨s, x⟩ := sx
      obtain ⟨hc, hx, -⟩ := (Inst.Model.FFSeg.IndexFacts.famAtPos DF c _ s x).mp hfa
      by_cases hs : present s (X / DF.T / 2 ^ lJ DF c) = true
      · subst hc
        have h2 := (key_mem_iff_port (EE := EE) y Mz Wi t' ht tb L0 (rows_call tb (call s)) hl hs hx
          hi).mpr (H ⟨⟨s, _, x, _⟩, hl, hs, hx, hi⟩)
        simpa only [if_pos hs] using h2
      · simpa only [if_neg hs] using hp

end Pass

#print axioms key_pass_port
#print axioms key_mem_iff_port
#print axioms pad_call
#print axioms keyVecs_mem_iff

end OnBytes.Road
