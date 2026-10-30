-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTieE.lean: the key vectors on the verifier's cells against the keys' half of
the library's glued segment.

Johnson/Road/FormsKeysTie.lean ties the library's key vectors of a group's eight calls to the keys'
half of the group's segment in the library's partition, at the library's own dictionary from names
of cells to places in its matrices (tA) and its own reading of the weights (wOf). The theorems of
these files speak of the key vectors on the cells that the verifier's rule reads in its list of
matrices (cellsOf and cellsAt), under the table of scales sclOf. This file carries the tie over.

What is compared with what. On the left the library's key vectors on cells named by these files'
dictionary in integer matrices Mz, at weights read by the library's layout in an integer index
matrix Wi, both carried into the field, under sclOf. On the right the keys' half (KeysHold) of
segment 2 g of the library's model in glued form, at Wi modulo the prime and at integer matrices M
of the library's. Of the verifier nothing stands in a statement but through cellsAt, which reads
the layout's numbers, and wordsAt, which reads the scale file.

Main theorems: vec_dict (the key vectors in the two dictionaries are the same below their lengths);
tie_end; tie_end_file (at the library's table made from the verifier's own scale file).

Who reads the target. As in Johnson/Road/FormsKeysTie.lean. The laws admit and force read Cond
whole: all 25 segments, the identities' half too, and a bound on the cells: so nothing here reaches
the relation. The keys' half alone is read by the library's theorem on the lookup's claim before the
shift (ldPartKeys_holds in Cb/Part/LdPartLkpFam.lean), which the front of a segment and the law on
the multiplicities' bits use; no file of this library joins it with vecs_glued. The laws have the
cast LdPartD.castM where these files have Cb.Partition.castM: one body. The left side of tie_end is
the left side of keyVecs_ffKey (Johnson/Road/FormsKeysScl.lean) at Cb.Gl.E.

At which sizes. DF, the library's Dim.ref, alone; groups of four layers; the first layer 4 g;
tie_end at the reference tables and the fields Cb.Gl.F and Cb.Gl.E. vec_dict: every field that is
an algebra over Cb.Gl.F, all tables, every table of scales.

The hypotheses, and that they can be met.
 - hD: the matrices M hold, at the library's places of the valid names, the verifier's cells. No
   witness is given in this file. It is the statement of dict_valid, for matrices made from Mz, in
   Johnson/Road/FormsKeysDict.lean, which this file does not import.
 - hw: the words of the group's four layers, as wordsAt reads them, are those of s. Met, with
   nothing asked, by s := scalesOf h sc nf: tie_end_file.
 - g < nGr = 12.

What is not claimed. That the entries lie in the tables. That the entries of a run's matrices are
casts of integers. That the verifier's first layer g Lam is 4 g, its tables the reference tables,
its sizes the reference sizes, its field Cb.Gl.E. That Wi is a matrix to which anybody has
committed, or that the verifier reads its weights by the library's layerR. Anything on the
identities' half, on other segments, on the cells' size. The program does not import this file.
-/
import Johnson.Road.FormsKeysTie
import Johnson.Road.FormsKeysScl
import Johnson.Road.FormsKeysValid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay Shape Scales)
open Inst.Model (Scl Tables Mat ppref)
open Inst.Model.All (DF SFK nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Cell keyVec layerR lut aC)

section Dict

variable {E : Type} [Field E] [Algebra Cb.Gl.F E] (y : Lay) (Mz : Mats ℤ) (Wi : Mat) (g : ℕ)
  (M : ℕ → ℕ → ℕ → ℤ)
  (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c)

include hD

/-- The key vectors in the two dictionaries. If integer matrices M of the library's hold, at the
library's places of the valid names of cells of group g, the cells that the verifier's rule reads in
the integer matrices Mz, then below the vectors' lengths the key vectors on the verifier's cells
are the key vectors on the library's reading of M; the weights on both sides are read in one integer
index matrix. Under every table of scales and all tables. -/
theorem vec_dict [scl : Scl] (tb : Tables) (c : Fin 8) {X : ℕ} (hX : X < 2 ^ aC DF c) :
    keyVec DF (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : E)))) tb (4 * g)
        (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : E)) (4 * g + l)) c X =
      keyVec DF (Cm.Seg.tA g (Cb.Partition.castM (E := E) M)) tb (4 * g)
        (Cm.Seg.wOf g (Cm.TP.castW Cb.Gl.p Wi)) c X := by
  rw [Cm.Seg.TS.wOf_cast g Wi, Cm.Seg.TS.tA_castM g M, cells_cast]
  simp only [Inst.Model.FFSeg.Cast.layerCast']
  refine keyVec_agree (fun q hq => ?_) Inst.Model.FFSeg.ref_ok.f tb (4 * g) _ c hX
  show ((cellsOf DF (cellsAt y Mz) q : ℤ) : E) = ((Cm.Seg.TS.tM g M q : ℤ) : E)
  rw [hD q hq]

end Dict

/-- The end. All entries of the eight key vectors of group g on the verifier's cells, below the
vectors' lengths, under the table of scales of these files, are images of entries of their calls'
tables exactly if the keys' half of the conditions of segment 2 g of the library's partition holds
at the integer index matrix and at integer matrices M that hold the verifier's cells at the
library's places. The left side is that of keyVecs_ffKey (Johnson/Road/FormsKeysScl.lean) at the
library's larger field. Asked besides: the words of the group's four layers are those of the
library's table s. -/
theorem tie_end (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) Inst.Model.tbRef
            (4 * g) (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
            c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) ↔
    KeysHold (Cm.Seg.TS.segM s (2 * g)).glued Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
      (Cb.Partition.castM (E := Cb.Gl.E) M) := by
  rw [vecs_glued s hg]
  refine forall_congr' fun c => forall_congr' fun X => imp_congr_right fun hX => ?_
  rw [keyVec_scl (sclOf h sc g 4) (SFK s.kap s.nf g) (kap_sclOf h sc g s.kap hw s.nf),
    vec_dict (scl := SFK s.kap s.nf g) y Mz Wi g M hD Inst.Model.tbRef c hX]
  rfl

/-- The same at the library's table made from the verifier's own scale file: nothing is asked of the
words. -/
theorem tie_end_file (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr)
    (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) Inst.Model.tbRef
            (4 * g) (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
            c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) ↔
    KeysHold (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued Cm.Seg.TS.fmtRef x
      (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) M) :=
  tie_end y Mz Wi hg M hD h sc (scalesOf h sc nf)
    (fun l hl => by
      have hg' : g < 12 := hg
      rw [Nat.mul_comm g 4]
      exact kap_scalesOf h sc nf (by omega)) x

#print axioms vec_dict
#print axioms tie_end
#print axioms tie_end_file

end OnBytes.Road
